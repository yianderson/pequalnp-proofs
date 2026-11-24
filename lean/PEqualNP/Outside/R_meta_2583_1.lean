import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_2583_1

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity TopForm

theorem R_meta_2583_1
  (h1 : ∃ (D : Circuit), TopForm.IsAO2 (N + N) D ∧ D.size ≤ 100)
  (h2 : ∀ (D : Circuit), TopForm.IsAO2 (N + N) D → ∃ (D' : Circuit), TopForm.IsAO2 (N + N) D' ∧ D'.size ≤ D.size ∧ ReadK.IsReadK (N + N) D' 1)
  : ∃ (D : Circuit), TopForm.IsAO2 (N + N) D ∧ D.size ≤ 100 ∧ ReadK.IsReadK (N + N) D 1 := by
  rcases h1 with ⟨D, h_top, h_size⟩
  rcases h2 D h_top with ⟨D', h_read, h_size_le, h_read_k⟩
  have h_size' : D'.size ≤ 100 := Nat.le_trans h_size_le h_size
  exact ⟨D', h_read, h_size', h_read_k⟩

end PEqualNP.Outside.R_meta_2583_1