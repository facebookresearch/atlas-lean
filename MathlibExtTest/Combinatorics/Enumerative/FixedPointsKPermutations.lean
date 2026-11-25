/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FixedPointsKPermutations

namespace MathlibExtTest.Combinatorics.Enumerative.FixedPointsKPermutations

open MetaMathlibExt

-- Check the exact public statement, including the names of the binders.
example {n k j : ℕ} (hjk : j ≤ k) :
    kPermFixedPointCount n k j = n.choose j * kPermFixedPointCount (n - j) (k - j) 0 :=
  kPermFixedPointCount_eq_choose_mul_derangement (n := n) (k := k) (j := j) (hjk := hjk)

-- An oversized fixed set makes the count zero even when j ≤ k.
example : kPermFixedPointCount 2 3 3 = 0 := by
  rw [kPermFixedPointCount_eq_choose_mul_derangement (by decide)]
  simp

private theorem emptyCount : kPermFixedPointCount 0 0 0 = 1 := by
  unfold kPermFixedPointCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨1, by simp [cycleQuotientCount_eq], by simp⟩, ?_⟩
  exact fun σ => Subtype.ext (Subsingleton.elim _ _)

-- The empty permutation yields one choice, as does fixing all three points.
example : kPermFixedPointCount 0 0 0 = 1 := emptyCount

example : kPermFixedPointCount 3 3 3 = 1 := by
  simpa [emptyCount] using
    (kPermFixedPointCount_eq_choose_mul_derangement (n := 3) (k := 3) (j := 3) (by decide))

-- On two elements the swap is the only derangement, and it has one cycle.
private theorem twoPointDerangementCount : kPermFixedPointCount 2 1 0 = 1 := by
  let τ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  have hτ : ∀ x, τ x ≠ x := by decide
  have hfix : Fintype.card (Function.fixedPoints τ) = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun x => hτ x.val x.property⟩
  have hcycle : τ.IsCycle := Equiv.Perm.isCycle_swap (by decide : (0 : Fin 2) ≠ 1)
  unfold kPermFixedPointCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨τ, by simp [cycleQuotientCount_eq, hcycle.cycleType, hfix], hfix⟩, ?_⟩
  rintro ⟨σ, _, hσ⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change σ x = τ x
  have ha : (σ x).val ≠ x.val := fun hx =>
    (Fintype.card_eq_zero_iff.mp hσ).false ⟨x, Fin.ext hx⟩
  have hb : (τ x).val ≠ x.val := fun hx => hτ x (Fin.ext hx)
  apply Fin.ext
  omega

-- A two-cycle and a singleton on three points: three choices of singleton.
example : kPermFixedPointCount 3 2 1 = 3 := by
  simpa [twoPointDerangementCount] using
    (kPermFixedPointCount_eq_choose_mul_derangement (n := 3) (k := 2) (j := 1) (by decide))

end MathlibExtTest.Combinatorics.Enumerative.FixedPointsKPermutations
