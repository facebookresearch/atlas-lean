/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddEigenSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinOrthogonalLift

/-! The two nonzero coordinates and genuine norm of the actual Hadamard state family. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Insertion preserves the lower eleven spin coordinates. -/
theorem generatedOddSpinInsert_low (a : Fin 11 → ZMod 2) (z : ZMod 2) :
    generatedOddSpinLow (generatedOddSpinInsert a z) = a := by
  ext j
  exact Fin.snoc_castSucc (α := fun _ : Fin 12 => ZMod 2) z a j

/-- Insertion prescribes the final spin coordinate. -/
theorem generatedOddSpinInsert_last (a : Fin 11 → ZMod 2) (z : ZMod 2) :
    generatedOddSpinInsert a z 11 = z := by
  exact Fin.snoc_last (α := fun _ : Fin 12 => ZMod 2) z a

/-- The two inserted coordinates of one lower label are distinct. -/
theorem generatedOddSpinInsert_zero_ne_one (a : Fin 11 → ZMod 2) :
    generatedOddSpinInsert a 0 ≠ generatedOddSpinInsert a 1 := by
  intro h
  have hh := congrFun h 11
  rw [generatedOddSpinInsert_last, generatedOddSpinInsert_last] at hh
  exact zero_ne_one hh

/-- A Hadamard state is exactly the signed sum of its two genuine spin coordinate units. -/
theorem generatedOddSpinState_two_units (a : Fin 11 → ZMod 2) (e : ZMod 2) :
    generatedOddSpinState a e 0 =
      (Pi.single (generatedOddSpinInsert a 0) 1 : SpinSpace) +
        qSign e • Pi.single (generatedOddSpinInsert a 1) 1 := by
  classical
  ext t
  by_cases ht : generatedOddSpinLow t = a
  · have hb : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
    rcases hb (t 11) with hz | hz
    · have he : t = generatedOddSpinInsert a 0 := by
        rw [← generatedOddSpinInsert_reconstruct t, ht, hz]
      subst t
      simp [generatedOddSpinState, generatedOddSpinInsert_low,
        generatedOddSpinInsert_last, generatedOddSpinInsert_zero_ne_one]
    · have he : t = generatedOddSpinInsert a 1 := by
        rw [← generatedOddSpinInsert_reconstruct t, ht, hz]
      subst t
      simp [generatedOddSpinState, generatedOddSpinInsert_low,
        generatedOddSpinInsert_last, Ne.symm (generatedOddSpinInsert_zero_ne_one a)]
  · have h0 : t ≠ generatedOddSpinInsert a 0 := by
      intro he
      exact ht (he ▸ generatedOddSpinInsert_low a 0)
    have h1 : t ≠ generatedOddSpinInsert a 1 := by
      intro he
      exact ht (he ▸ generatedOddSpinInsert_low a 1)
    simp [generatedOddSpinState, ht, h0, h1]

/-- Every unnormalized Hadamard state has actual squared norm two. -/
theorem generatedOddSpinState_pairing (a : Fin 11 → ZMod 2) (e : ZMod 2) :
    spinPairing (generatedOddSpinState a e 0) (generatedOddSpinState a e 0) = 2 := by
  classical
  rw [generatedOddSpinState_two_units]
  norm_num [spinPairing, Pi.single_apply, mul_add, add_mul, Finset.sum_add_distrib,
    mul_ite, ite_mul, generatedOddSpinInsert_zero_ne_one,
    Ne.symm (generatedOddSpinInsert_zero_ne_one a), qSign_sq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
