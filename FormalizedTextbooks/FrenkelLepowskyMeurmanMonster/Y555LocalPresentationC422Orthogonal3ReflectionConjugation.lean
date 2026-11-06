/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual independent finite reflections conjugate by their root-vector isometry action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3ReflectionBinding

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- A product of actual invertible matrices acts by the corresponding vector action composition. -/
theorem y422Orthogonal3GL_mul_action
    (g h : Matrix.GeneralLinearGroup (Fin 8) (ZMod 3)) (v : Fin 8 → ZMod 3) :
    (g * h).val *ᵥ v = g.val *ᵥ (h.val *ᵥ v) := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]

/-- Actual matrix inverse action cancels the original coordinate action. -/
theorem y422Orthogonal3GL_action_inv
    (g : Matrix.GeneralLinearGroup (Fin 8) (ZMod 3)) (v : Fin 8 → ZMod 3) :
    g.val *ᵥ ((g⁻¹).val *ᵥ v) = v := by
  have h : g.val * (g⁻¹).val = 1 := g.val_inv
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

/-- Independent isometries transport the actual finite pairing through their inverse action. -/
theorem y422Orthogonal3FullGroup_pairing_inverse
    (g : Matrix.GeneralLinearGroup (Fin 8) (ZMod 3)) (hg : g ∈ y422Orthogonal3FullGroup)
    (v w : Fin 8 → ZMod 3) :
    y422Orthogonal3Pairing (g.val *ᵥ v) w = y422Orthogonal3Pairing v ((g⁻¹).val *ᵥ w) := by
  have h := y422Orthogonal3FullGroup_pairing g hg v ((g⁻¹).val *ᵥ w)
  rw [y422Orthogonal3GL_action_inv] at h
  exact h

/-- Conjugating a genuine independent reflection gives the reflection in its actual image root. -/
theorem y422Orthogonal3RootReflection_conjugate
    (g : Matrix.GeneralLinearGroup (Fin 8) (ZMod 3)) (hg : g ∈ y422Orthogonal3FullGroup)
    (v : Fin 8 → ZMod 3) (hv : y422Orthogonal3VectorNorm v ≠ 0)
    (hgv : y422Orthogonal3VectorNorm (g.val *ᵥ v) ≠ 0) :
    y422Orthogonal3RootReflection (g.val *ᵥ v) hgv =
      g * y422Orthogonal3RootReflection v hv * g⁻¹ := by
  apply y422Orthogonal3GL_ext
  intro w
  simp only [y422Orthogonal3GL_mul_action, y422Orthogonal3RootReflection_action,
    y422Orthogonal3VectorReflection_apply]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, y422Orthogonal3GL_action_inv,
    y422Orthogonal3FullGroup_norm g hg v, y422Orthogonal3FullGroup_pairing_inverse g hg v w]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
