/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine reflections of the independent nonsingular finite Cartan form. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3FullGroup
public import Mathlib.LinearAlgebra.Reflection

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Pairing with an actual vector in the independent finite Cartan form is a linear functional. -/
def y322Orthogonal3Pairing (v : Fin 7 → ZMod 3) : (Fin 7 → ZMod 3) →ₗ[ZMod 3] ZMod 3 where
  toFun w := dotProduct v (y322Orthogonal3Gram *ᵥ w)
  map_add' x y := by rw [Matrix.mulVec_add, dotProduct_add]
  map_smul' c w := by rw [Matrix.mulVec_smul, dotProduct_smul]; rfl

/-- Symmetry of the actual finite form gives symmetry of its vector pairing. -/
theorem y322Orthogonal3Pairing_symm (v w : Fin 7 → ZMod 3) :
    y322Orthogonal3Pairing v w = y322Orthogonal3Pairing w v := by
  change dotProduct v (y322Orthogonal3Gram *ᵥ w) = dotProduct w (y322Orthogonal3Gram *ᵥ v)
  simpa only [y322Orthogonal3Gram_symmetric] using
    Matrix.dotProduct_transpose_mulVec y322Orthogonal3Gram v w

/-- Normalize the independent form pairing to the standard reflection functional. -/
def y322Orthogonal3ReflectionFunctional (v : Fin 7 → ZMod 3) :
    (Fin 7 → ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
  (2 / y322Orthogonal3VectorNorm v) • y322Orthogonal3Pairing v

/-- Each actual nonisotropic vector has its normalized reflection functional value two. -/
theorem y322Orthogonal3ReflectionFunctional_self (v : Fin 7 → ZMod 3)
    (hv : y322Orthogonal3VectorNorm v ≠ 0) : y322Orthogonal3ReflectionFunctional v v = 2 := by
  change (2 / y322Orthogonal3VectorNorm v) * y322Orthogonal3VectorNorm v = 2
  exact div_mul_cancel₀ 2 hv

/-- The actual finite reflection in a nonisotropic vector as an invertible linear map. -/
def y322Orthogonal3VectorReflection (v : Fin 7 → ZMod 3)
    (hv : y322Orthogonal3VectorNorm v ≠ 0) : (Fin 7 → ZMod 3) ≃ₗ[ZMod 3] (Fin 7 → ZMod 3) :=
  Module.reflection (y322Orthogonal3ReflectionFunctional_self v hv)

/-- The genuine independent reflection has the usual normalized bilinear action. -/
theorem y322Orthogonal3VectorReflection_apply (v w : Fin 7 → ZMod 3)
    (hv : y322Orthogonal3VectorNorm v ≠ 0) :
    y322Orthogonal3VectorReflection v hv w =
      w - ((2 / y322Orthogonal3VectorNorm v) * y322Orthogonal3Pairing v w) • v := by
  exact Module.reflection_apply w (y322Orthogonal3ReflectionFunctional_self v hv)

/-- The normalized nonisotropic reflection is a genuine involution. -/
theorem y322Orthogonal3VectorReflection_involutive (v : Fin 7 → ZMod 3)
    (hv : y322Orthogonal3VectorNorm v ≠ 0) :
    Function.Involutive (y322Orthogonal3VectorReflection v hv) :=
  Module.involutive_reflection _

/-- Every independent form isometry preserves the actual bilinear pairing of arbitrary vectors. -/
theorem y322Orthogonal3FullGroup_pairing
    (g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) (hg : g ∈ y322Orthogonal3FullGroup)
    (v w : Fin 7 → ZMod 3) :
    y322Orthogonal3Pairing (g.val *ᵥ v) (g.val *ᵥ w) = y322Orthogonal3Pairing v w := by
  change dotProduct (g.val *ᵥ v) (y322Orthogonal3Gram *ᵥ (g.val *ᵥ w)) =
    dotProduct v (y322Orthogonal3Gram *ᵥ w)
  rw [dotProduct_comm (g.val *ᵥ v), ← Matrix.dotProduct_transpose_mulVec]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
