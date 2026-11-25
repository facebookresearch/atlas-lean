/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.InactivePermutation

/-!
# Inactive permutations on four points

The point `0` is active. The even permutation cycles `1 → 2 → 3 → 1`,
and the odd permutation swaps `1` and `2`. The cycle keeps its direction
on the complement and after padding, and the odd restriction keeps sign `-1`.
-/

namespace Equiv.Perm.InactivePermutationTests

private def active : Set (Fin 4) := {0}

local instance : DecidablePred (· ∈ active) := fun x =>
  inferInstanceAs (Decidable (x = 0))

private def one : {x : Fin 4 // x ∉ active} := ⟨1, by decide⟩
private def two : {x : Fin 4 // x ∉ active} := ⟨2, by decide⟩
private def three : {x : Fin 4 // x ∉ active} := ⟨3, by decide⟩

private def cycle : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3
private def transposition : Equiv.Perm (Fin 4) := Equiv.swap 1 2

private theorem cycle_fixes : ∀ x ∈ active, cycle x = x := by
  intro x hx
  have h : x = 0 := hx
  subst x
  decide

private theorem transposition_fixes : ∀ x ∈ active, transposition x = x := by
  intro x hx
  have h : x = 0 := hx
  subst x
  decide

example :
    (inactiveRestriction cycle active cycle_fixes one).val = 2 ∧
    (inactiveRestriction cycle active cycle_fixes two).val = 3 ∧
    (inactiveRestriction cycle active cycle_fixes three).val = 1 := by
  simp only [inactiveRestriction_apply]
  decide

example : ofSubtype (inactiveRestriction cycle active cycle_fixes) = cycle :=
  inactiveRestriction_extends cycle active cycle_fixes

example :
    sign (inactiveRestriction transposition active transposition_fixes) =
      -1 := by
  rw [inactiveRestriction_sign]
  exact sign_swap (by decide : (1 : Fin 4) ≠ 2)

example :
    paddedInactivePermutation cycle active cycle_fixes (Sum.inl one) =
      Sum.inl two := by
  rw [paddedInactivePermutation_eq]
  change Sum.inl (inactiveRestriction cycle active cycle_fixes one) =
    Sum.inl two
  congr 1
  apply Subtype.ext
  rw [inactiveRestriction_apply]
  decide

example (k : Fin 5) :
    paddedInactivePermutation cycle active cycle_fixes (Sum.inr k) =
      Sum.inr k := by
  rw [paddedInactivePermutation_eq]
  rfl

example : paddedInactivePermutation cycle active cycle_fixes ∈
    alternatingGroup (InactivePaddedIndex active) := by
  apply paddedInactivePermutation_even
  rw [cycle, sign_mul, sign_swap (by decide : (1 : Fin 4) ≠ 2),
    sign_swap (by decide : (2 : Fin 4) ≠ 3)]
  decide

end Equiv.Perm.InactivePermutationTests
