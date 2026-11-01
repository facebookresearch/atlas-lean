/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The literal source generators are genuine reflections of the independent finite form. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3MatrixAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3ReflectionMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Every actual nonisotropic root reflection lies in the independently defined isometry group. -/
theorem y322Orthogonal3RootReflection_mem_full (v : Fin 7 → ZMod 3)
    (hv : y322Orthogonal3VectorNorm v ≠ 0) :
    y322Orthogonal3RootReflection v hv ∈ y322Orthogonal3FullGroup := by
  apply y322Orthogonal3FullGroup_mem_of_norm
  intro w
  rw [y322Orthogonal3RootReflection_action]
  exact y322Orthogonal3VectorReflection_norm v w hv

set_option maxRecDepth 100000 in
-- All eight original Cartan roots have their exact finite quadratic value checked in the kernel.
/-- Each of the eight literal original source roots has norm exactly two. -/
theorem y322Orthogonal3Root_norm (i : Fin 8) :
    y322Orthogonal3VectorNorm (y322Orthogonal3Root i) = 2 := by
  fin_cases i <;> decide +kernel

/-- Each literal original source root is nonisotropic in the independent finite form. -/
theorem y322Orthogonal3Root_nonisotropic (i : Fin 8) :
    y322Orthogonal3VectorNorm (y322Orthogonal3Root i) ≠ 0 := by
  rw [y322Orthogonal3Root_norm]
  decide +kernel

/-- The exact original source generator is the genuine finite reflection in its declared root. -/
theorem y322Orthogonal3RootReflection_generator (i : Fin 8) :
    y322Orthogonal3RootReflection (y322Orthogonal3Root i)
      (y322Orthogonal3Root_nonisotropic i) = y322Orthogonal3Generator i := by
  apply y322Orthogonal3GL_ext
  intro w
  change (y322Orthogonal3RootReflection (y322Orthogonal3Root i)
    (y322Orthogonal3Root_nonisotropic i)).val *ᵥ w = y322Orthogonal3Reflection i *ᵥ w
  rw [y322Orthogonal3RootReflection_action, y322Orthogonal3VectorReflection_apply,
    y322Orthogonal3Root_norm, div_self (show (2 : ZMod 3) ≠ 0 by decide), one_mul]
  rw [y322Orthogonal3Reflection, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  rw [y322Orthogonal3Pairing_symm (y322Orthogonal3Root i) w, op_smul_eq_smul]
  change w - dotProduct w (y322Orthogonal3Gram *ᵥ y322Orthogonal3Root i) •
    y322Orthogonal3Root i = w - dotProduct (y322Orthogonal3Gram *ᵥ y322Orthogonal3Root i) w •
      y322Orthogonal3Root i
  rw [dotProduct_comm w]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
