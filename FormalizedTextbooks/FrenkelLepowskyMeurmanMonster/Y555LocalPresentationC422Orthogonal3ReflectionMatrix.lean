/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine independent finite reflections as actual invertible eight-dimensional matrices. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3ReflectionForm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Convert the genuine independent reflection to its actual invertible coordinate matrix. -/
def y422Orthogonal3RootReflection (v : Fin 8 → ZMod 3)
    (hv : y422Orthogonal3VectorNorm v ≠ 0) : Matrix.GeneralLinearGroup (Fin 8) (ZMod 3) :=
  Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (y422Orthogonal3VectorReflection v hv))

/-- The actual coordinate matrix acts as exactly the independently defined finite reflection. -/
theorem y422Orthogonal3RootReflection_action (v w : Fin 8 → ZMod 3)
    (hv : y422Orthogonal3VectorNorm v ≠ 0) :
    (y422Orthogonal3RootReflection v hv).val *ᵥ w = y422Orthogonal3VectorReflection v hv w := by
  have h := Matrix.GeneralLinearGroup.toLin.apply_symm_apply
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (y422Orthogonal3VectorReflection v hv))
  exact congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 3) (Fin 8 → ZMod 3) => f.val w) h

/-- The actual finite reflection matrix has square one by its independent involutive action. -/
theorem y422Orthogonal3RootReflection_square (v : Fin 8 → ZMod 3)
    (hv : y422Orthogonal3VectorNorm v ≠ 0) : y422Orthogonal3RootReflection v hv ^ 2 = 1 := by
  have hi : (y422Orthogonal3RootReflection v hv)⁻¹ = y422Orthogonal3RootReflection v hv := by
    unfold y422Orthogonal3RootReflection
    rw [← map_inv, ← LinearMap.GeneralLinearGroup.ofLinearEquiv_inv]
    rfl
  calc
    _ = y422Orthogonal3RootReflection v hv * y422Orthogonal3RootReflection v hv := pow_two _
    _ = y422Orthogonal3RootReflection v hv * (y422Orthogonal3RootReflection v hv)⁻¹ :=
      congrArg (fun g => y422Orthogonal3RootReflection v hv * g) hi.symm
    _ = 1 := mul_inv_cancel _

/-- Equal actual nonisotropic root vectors give the same genuine reflection matrix. -/
theorem y422Orthogonal3RootReflection_congr (v w : Fin 8 → ZMod 3)
    (hv : y422Orthogonal3VectorNorm v ≠ 0) (hw : y422Orthogonal3VectorNorm w ≠ 0)
    (h : v = w) : y422Orthogonal3RootReflection v hv = y422Orthogonal3RootReflection w hw := by
  cases h
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
