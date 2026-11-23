/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.PermutationInversions

/-!
# Tests for inversions of a random permutation
-/

namespace MetaMathlibExt.Test.PermutationInversions

open MetaMathlibExt

/-- The reversal `2 1 0` of `Fin 3` has all `3` pairs inverted. -/
example : permInversionCount (Fin.revPerm : Equiv.Perm (Fin 3)) = 3 := by decide

/-- The identity has no inversion. -/
example : permInversionCount (1 : Equiv.Perm (Fin 4)) = 0 := by decide

/-- A transposition of adjacent positions has exactly one inversion. -/
example : permInversionCount (Equiv.swap (0 : Fin 3) 1) = 1 := by decide

/-- Over the six permutations of `Fin 3` the inversion numbers are `0, 1, 1, 2, 2, 3`, summing to
`9 = 3! · 3 · 2 / 4`. -/
example : ∑ σ : Equiv.Perm (Fin 3), permInversionCount σ = 9 := by decide

example : 4 * ∑ σ : Equiv.Perm (Fin 3), permInversionCount σ = Nat.factorial 3 * (3 * 2) :=
  four_mul_sum_permInversionCount

/-- For `n = 4` the expected number of inversions is `4 · 3 / 4 = 3`. -/
example : ((PMF.uniformFintype (Equiv.Perm (Fin 4))).expectENN
    (fun σ => (permInversionCount σ : ENNReal))).toReal = 3 := by
  rw [expectENN_permInversionCount_toReal]
  norm_num

/-- `inv(σ⁻¹) = inv(σ)` on a 3-cycle, whose inverse is a different permutation. -/
example : permInversionCount (finRotate 3)⁻¹ = permInversionCount (finRotate 3) :=
  permInversionCount_inv _

example : permInversionCount (finRotate 3) = 2 := by decide

/-- Numerical check of the generating function of inversions (Stanley, Corollary 1.3.13) at
`q = 2` for `n = 3`: `∑_σ 2 ^ inv(σ) = 1 · (1 + 2) · (1 + 2 + 4) = 21`. -/
example : ∑ σ : Equiv.Perm (Fin 3), 2 ^ permInversionCount σ =
    ∏ k ∈ Finset.range 3, ∑ i ∈ Finset.range (k + 1), 2 ^ i := by
  decide

end MetaMathlibExt.Test.PermutationInversions
