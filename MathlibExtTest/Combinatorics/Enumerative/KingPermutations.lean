/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.KingPermutations

/-! # Tests for the generating function of king permutations avoiding a flat pattern -/

namespace MetaMathlibExt.kingFlatPOPAboveGF_three_eq_rename

-- The singleton has one minimum in either direction and no adjacent pair.
example : PowerSeries.coeff 1 (kingFlatPOPAboveGF 3) =
    MvPolynomial.X 2 * MvPolynomial.X 3 := by
  classical
  rw [kingFlatPOPAboveGF, PowerSeries.coeff_mk,
    Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin 1))]
  · have ha : permAscentCount (1 : Equiv.Perm (Fin 1)) = 0 := by decide
    have hd : permDescentCount (1 : Equiv.Perm (Fin 1)) = 0 := by decide
    have hl : permLeftToRightMinCount (1 : Equiv.Perm (Fin 1)) = 1 := by decide
    have hr : permRightToLeftMinCount (1 : Equiv.Perm (Fin 1)) = 1 := by decide
    simp [ha, hd, hl, hr]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, fun h => by simpa using four_le_of_containsFlatPOPAbove h⟩
    unfold IsKingPerm
    decide
  · intro σ _ h
    exact (h (Subsingleton.elim _ _)).elim

-- In zero-based one-line notation this king permutation is 352041.
private def sample : Equiv.Perm (Fin 6) := Equiv.swap 0 3 * Equiv.swap 1 5

example : IsKingPerm sample ∧ IsKingPerm (Fin.revPerm.permCongr sample) := by
  unfold IsKingPerm
  decide

example : ¬ ContainsFlatPOPBelow sample 0 := by
  rintro ⟨f, h⟩
  have check : ∀ a b c d : Fin 6, a < b → b < c → c < d →
      ¬ (sample a < sample b ∧ sample a < sample c ∧ sample a < sample d) := by decide
  exact check (f 0) (f 1) (f 2) (f 3) (f.strictMono (by decide)) (f.strictMono (by decide))
    (f.strictMono (by decide)) ⟨h 1 (by decide), h 2 (by decide), h 3 (by decide)⟩

-- The two weights have exponents (2, 3, 2, 3) and (2, 3, 3, 2), respectively.
example :
    (permAscentCount sample, permDescentCount sample,
      permLeftToRightMaxCount sample, permRightToLeftMaxCount sample) = (2, 3, 2, 3) ∧
    let τ := Fin.revPerm.permCongr sample
    (permAscentCount τ, permDescentCount τ,
      permLeftToRightMinCount τ, permRightToLeftMinCount τ) = (2, 3, 3, 2) := by
  decide

end MetaMathlibExt.kingFlatPOPAboveGF_three_eq_rename
