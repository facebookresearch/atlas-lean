/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The literal source generators are genuine reflections of the independent finite form. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3MatrixAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3ReflectionMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Every actual nonisotropic root reflection lies in the independently defined isometry group. -/
theorem y422Orthogonal3RootReflection_mem_full (v : Fin 8 → ZMod 3)
    (hv : y422Orthogonal3VectorNorm v ≠ 0) :
    y422Orthogonal3RootReflection v hv ∈ y422Orthogonal3FullGroup := by
  apply y422Orthogonal3FullGroup_mem_of_norm
  intro w
  rw [y422Orthogonal3RootReflection_action]
  exact y422Orthogonal3VectorReflection_norm v w hv

set_option maxRecDepth 100000 in
-- All nine original Cartan roots have their exact finite quadratic value checked in the kernel.
/-- Each of the nine literal original source roots has norm exactly two. -/
theorem y422Orthogonal3Root_norm (i : Fin 9) :
    y422Orthogonal3VectorNorm (y422Orthogonal3Root i) = 2 := by
  fin_cases i <;> decide +kernel

/-- Each literal original source root is nonisotropic in the independent finite form. -/
theorem y422Orthogonal3Root_nonisotropic (i : Fin 9) :
    y422Orthogonal3VectorNorm (y422Orthogonal3Root i) ≠ 0 := by
  rw [y422Orthogonal3Root_norm]
  decide +kernel

/-- The exact original source generator is the genuine finite reflection in its declared root. -/
theorem y422Orthogonal3RootReflection_generator (i : Fin 9) :
    y422Orthogonal3RootReflection (y422Orthogonal3Root i)
      (y422Orthogonal3Root_nonisotropic i) = y422Orthogonal3Generator i := by
  apply y422Orthogonal3GL_ext
  intro w
  change (y422Orthogonal3RootReflection (y422Orthogonal3Root i)
    (y422Orthogonal3Root_nonisotropic i)).val *ᵥ w = y422Orthogonal3Reflection i *ᵥ w
  rw [y422Orthogonal3RootReflection_action, y422Orthogonal3VectorReflection_apply,
    y422Orthogonal3Root_norm, div_self (show (2 : ZMod 3) ≠ 0 by decide), one_mul]
  rw [y422Orthogonal3Reflection, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  rw [y422Orthogonal3Pairing_symm (y422Orthogonal3Root i) w, op_smul_eq_smul]
  change w - dotProduct w (y422Orthogonal3Gram *ᵥ y422Orthogonal3Root i) •
    y422Orthogonal3Root i = w - dotProduct (y422Orthogonal3Gram *ᵥ y422Orthogonal3Root i) w •
      y422Orthogonal3Root i
  rw [dotProduct_comm w]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
