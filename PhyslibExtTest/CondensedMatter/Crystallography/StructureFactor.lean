/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.Crystallography.StructureFactor
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

open PhyslibExt.CondensedMatter.Crystallography.StructureFactor

namespace PhyslibExtTest.CondensedMatter.Crystallography.StructureFactor

/-! ### Structure factor: sign-sensitive `ZMod 4` test -/

/-- A unit amplitude at position `1` of `ZMod 4`, evaluated at `k = 1`, gives
`-i`: the negative-exponent kernel of `ZMod.dft`, not the positive-exponent
value `i`. -/
example :
    structureFactor (fun _ : Fin 1 => (1 : ℂ)) ![1] (1 : ZMod 4) = -Complex.I := by
  have h1 : ZMod.stdAddChar (-(1 : ZMod 4)) = -Complex.I := by
    have h := ZMod.stdAddChar_coe (N := 4) (-1)
    rw [Int.cast_neg, Int.cast_one] at h
    rw [h, ← Complex.exp_neg_pi_div_two_mul_I]
    congr 1
    push_cast
    ring
  simp [structureFactor, h1]

/-! ### Two-site structure factor on `ZMod 2` -/

example :
    structureFactor (fun _ : Fin 2 => (3 : ℂ)) ![0, 1] (1 : ZMod 2) = 0 :=
  structureFactor_twoSite_cancel 3

example : structureFactor (fun _ : Fin 2 => (3 : ℂ)) ![0, 1] (0 : ZMod 2) =
    2 * 3 := by
  rw [structureFactor_eq_sum_amp_of_zero, Fin.sum_univ_two, two_mul]

example (a : ℂ) :
    structureFactor (fun _ : Fin 2 => a) ![0, 1] (0 : ZMod 2) = 2 * a := by
  rw [structureFactor_eq_sum_amp_of_zero, Fin.sum_univ_two, two_mul]

end PhyslibExtTest.CondensedMatter.Crystallography.StructureFactor

#print axioms structureFactor_eq_sum_amp_of_zero
#print axioms structureFactor_twoSite_cancel
