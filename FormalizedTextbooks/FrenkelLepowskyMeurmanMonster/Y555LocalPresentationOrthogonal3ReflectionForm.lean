/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine independent finite reflections preserve the given Cartan norm. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3RootReflection

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The symmetric finite pairing is linear in its first vector as well as its second. -/
theorem y322Orthogonal3Pairing_sub_smul (v w u : Fin 7 → ZMod 3) (t : ZMod 3) :
    y322Orthogonal3Pairing (v - t • w) u =
      y322Orthogonal3Pairing v u - t * y322Orthogonal3Pairing w u := by
  rw [y322Orthogonal3Pairing_symm, map_sub, map_smul]
  rw [y322Orthogonal3Pairing_symm u v, y322Orthogonal3Pairing_symm u w]
  rfl

/-- The finite quadratic norm expands exactly under subtraction of a scalar vector. -/
theorem y322Orthogonal3VectorNorm_sub_smul (v w : Fin 7 → ZMod 3) (t : ZMod 3) :
    y322Orthogonal3VectorNorm (w - t • v) =
      y322Orthogonal3VectorNorm w - t * y322Orthogonal3Pairing w v -
        t * y322Orthogonal3Pairing v w + t * t * y322Orthogonal3VectorNorm v := by
  change y322Orthogonal3Pairing (w - t • v) (w - t • v) = _
  rw [y322Orthogonal3Pairing_sub_smul]
  simp only [map_sub, map_smul, smul_eq_mul]
  change (y322Orthogonal3VectorNorm w - t * y322Orthogonal3Pairing w v) -
    t * (y322Orthogonal3Pairing v w - t * y322Orthogonal3VectorNorm v) = _
  ring

/-- Every genuine normalized nonisotropic reflection preserves the actual finite Cartan norm. -/
theorem y322Orthogonal3VectorReflection_norm (v w : Fin 7 → ZMod 3)
    (hv : y322Orthogonal3VectorNorm v ≠ 0) :
    y322Orthogonal3VectorNorm (y322Orthogonal3VectorReflection v hv w) =
      y322Orthogonal3VectorNorm w := by
  rw [y322Orthogonal3VectorReflection_apply, y322Orthogonal3VectorNorm_sub_smul,
    y322Orthogonal3Pairing_symm w v]
  field_simp
  ring

/-- The independent symmetric finite pairing is recovered by quadratic polarization. -/
theorem y322Orthogonal3Pairing_polarization (v w : Fin 7 → ZMod 3) :
    y322Orthogonal3Pairing v w =
      (y322Orthogonal3VectorNorm (v + w) - y322Orthogonal3VectorNorm v -
        y322Orthogonal3VectorNorm w) / 2 := by
  have h := y322Orthogonal3VectorNorm_sub_smul w v (-1)
  simp only [neg_one_smul, sub_neg_eq_add, y322Orthogonal3Pairing_symm w v] at h
  rw [h]
  calc
    _ = y322Orthogonal3Pairing v w * ((2 : ZMod 3)⁻¹ * 2) := by
      rw [inv_mul_cancel₀ (show (2 : ZMod 3) ≠ 0 by decide), mul_one]
    _ = _ := by ring

/-- Genuine nonisotropic reflections preserve the full independent bilinear Cartan pairing. -/
theorem y322Orthogonal3VectorReflection_pairing (v x y : Fin 7 → ZMod 3)
    (hv : y322Orthogonal3VectorNorm v ≠ 0) :
    y322Orthogonal3Pairing (y322Orthogonal3VectorReflection v hv x)
        (y322Orthogonal3VectorReflection v hv y) = y322Orthogonal3Pairing x y := by
  rw [y322Orthogonal3Pairing_polarization, ← map_add]
  simp only [y322Orthogonal3VectorReflection_norm]
  exact (y322Orthogonal3Pairing_polarization x y).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
