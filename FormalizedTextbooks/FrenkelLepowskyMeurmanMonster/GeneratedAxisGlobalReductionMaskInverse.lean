/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskColumns

public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Right inverse certificates checked on compact coordinate columns give the
actual inverse binary action. No matrix inverse is supplied as an assumption. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- A single-bit mask decodes to the corresponding genuine coordinate unit. -/
theorem generatedAxisGlobalMaskDecode_two_pow {n : ℕ} (j : Fin n) :
    monsterCo1GeometryBinaryMaskDecode (2 ^ j.val) = (Pi.single j 1 : Fin n → ZMod 2) := by
  ext i
  simp [monsterCo1GeometryBinaryMaskDecode, Nat.testBit_two_pow, Pi.single_apply,
    Fin.ext_iff, eq_comm]

/-- Checking the image of every proposed inverse column proves a true matrix right inverse. -/
theorem generatedAxisGlobalMaskColumnMatrix_right_inverse {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (ZMod 2)) (cols : Fin n → ℕ)
    (hcol : ∀ j, A *ᵥ monsterCo1GeometryBinaryMaskDecode (cols j) = Pi.single j 1) :
    A * generatedAxisGlobalMaskColumnMatrix cols = 1 := by
  ext i j
  have h := congrFun (hcol j) i
  change (A *ᵥ monsterCo1GeometryBinaryMaskDecode (cols j)) i = _
  simpa only [Matrix.one_apply, Pi.single_apply, eq_comm] using h

/-- A checked right-inverse matrix is the inverse of an actual binary linear equivalence. -/
theorem generatedAxisGlobalMaskColumnMatrix_inverse_apply {n : ℕ}
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (A : Matrix (Fin n) (Fin n) (ZMod 2)) (cols : Fin n → ℕ)
    (he : ∀ v, e v = A *ᵥ v)
    (hcol : ∀ j, A *ᵥ monsterCo1GeometryBinaryMaskDecode (cols j) = Pi.single j 1)
    (v : Fin n → ZMod 2) :
    e.symm v = generatedAxisGlobalMaskColumnMatrix cols *ᵥ v := by
  apply e.injective
  rw [e.apply_symm_apply, he, Matrix.mulVec_mulVec,
    generatedAxisGlobalMaskColumnMatrix_right_inverse A cols hcol, Matrix.one_mulVec]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
