/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine independent finite reflections preserve the given Cartan norm. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3RootReflection

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The symmetric finite pairing is linear in its first vector as well as its second. -/
theorem y422Orthogonal3Pairing_sub_smul (v w u : Fin 8 → ZMod 3) (t : ZMod 3) :
    y422Orthogonal3Pairing (v - t • w) u =
      y422Orthogonal3Pairing v u - t * y422Orthogonal3Pairing w u := by
  rw [y422Orthogonal3Pairing_symm, map_sub, map_smul]
  rw [y422Orthogonal3Pairing_symm u v, y422Orthogonal3Pairing_symm u w]
  rfl

/-- The finite quadratic norm expands exactly under subtraction of a scalar vector. -/
theorem y422Orthogonal3VectorNorm_sub_smul (v w : Fin 8 → ZMod 3) (t : ZMod 3) :
    y422Orthogonal3VectorNorm (w - t • v) =
      y422Orthogonal3VectorNorm w - t * y422Orthogonal3Pairing w v -
        t * y422Orthogonal3Pairing v w + t * t * y422Orthogonal3VectorNorm v := by
  change y422Orthogonal3Pairing (w - t • v) (w - t • v) = _
  rw [y422Orthogonal3Pairing_sub_smul]
  simp only [map_sub, map_smul, smul_eq_mul]
  change (y422Orthogonal3VectorNorm w - t * y422Orthogonal3Pairing w v) -
    t * (y422Orthogonal3Pairing v w - t * y422Orthogonal3VectorNorm v) = _
  ring

/-- Every genuine normalized nonisotropic reflection preserves the actual finite Cartan norm. -/
theorem y422Orthogonal3VectorReflection_norm (v w : Fin 8 → ZMod 3)
    (hv : y422Orthogonal3VectorNorm v ≠ 0) :
    y422Orthogonal3VectorNorm (y422Orthogonal3VectorReflection v hv w) =
      y422Orthogonal3VectorNorm w := by
  rw [y422Orthogonal3VectorReflection_apply, y422Orthogonal3VectorNorm_sub_smul,
    y422Orthogonal3Pairing_symm w v]
  field_simp
  ring

/-- The independent symmetric finite pairing is recovered by quadratic polarization. -/
theorem y422Orthogonal3Pairing_polarization (v w : Fin 8 → ZMod 3) :
    y422Orthogonal3Pairing v w =
      (y422Orthogonal3VectorNorm (v + w) - y422Orthogonal3VectorNorm v -
        y422Orthogonal3VectorNorm w) / 2 := by
  have h := y422Orthogonal3VectorNorm_sub_smul w v (-1)
  simp only [neg_one_smul, sub_neg_eq_add, y422Orthogonal3Pairing_symm w v] at h
  rw [h]
  calc
    _ = y422Orthogonal3Pairing v w * ((2 : ZMod 3)⁻¹ * 2) := by
      rw [inv_mul_cancel₀ (show (2 : ZMod 3) ≠ 0 by decide), mul_one]
    _ = _ := by ring

/-- Genuine nonisotropic reflections preserve the full independent bilinear Cartan pairing. -/
theorem y422Orthogonal3VectorReflection_pairing (v x y : Fin 8 → ZMod 3)
    (hv : y422Orthogonal3VectorNorm v ≠ 0) :
    y422Orthogonal3Pairing (y422Orthogonal3VectorReflection v hv x)
        (y422Orthogonal3VectorReflection v hv y) = y422Orthogonal3Pairing x y := by
  rw [y422Orthogonal3Pairing_polarization, ← map_add]
  simp only [y422Orthogonal3VectorReflection_norm]
  exact (y422Orthogonal3Pairing_polarization x y).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
