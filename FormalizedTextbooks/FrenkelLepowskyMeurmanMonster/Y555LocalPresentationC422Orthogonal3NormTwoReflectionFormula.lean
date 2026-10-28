/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact matrices and sign invariance of arbitrary independent norm-two reflections. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3ReflectionBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3NormTwoLineCodes

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Every independent norm-two reflection has its literal Cartan outer-product matrix. -/
theorem y422Orthogonal3RootReflection_norm_two_matrix (v : Fin 8 → ZMod 3)
    (hv : y422Orthogonal3VectorNorm v = 2) :
    (y422Orthogonal3RootReflection v (by rw [hv]; decide)).val =
      1 - Matrix.vecMulVec v (y422Orthogonal3Gram *ᵥ v) := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [y422Orthogonal3RootReflection_action, y422Orthogonal3VectorReflection_apply,
    hv, div_self (show (2 : ZMod 3) ≠ 0 by decide), one_mul]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  rw [y422Orthogonal3Pairing_symm v (Pi.single i 1), op_smul_eq_smul]
  change Pi.single i 1 - dotProduct (Pi.single i 1) (y422Orthogonal3Gram *ᵥ v) • v =
    Pi.single i 1 - dotProduct (y422Orthogonal3Gram *ᵥ v) (Pi.single i 1) • v
  rw [dotProduct_comm (Pi.single i 1)]

/-- Opposite actual norm-two vectors define the same independent reflection matrix. -/
theorem y422Orthogonal3RootReflection_norm_two_neg (v : Fin 8 → ZMod 3)
    (hv : y422Orthogonal3VectorNorm v = 2) :
    y422Orthogonal3RootReflection (-v)
      (by rw [y422Orthogonal3VectorNorm_neg, hv]; decide) =
      y422Orthogonal3RootReflection v (by rw [hv]; decide) := by
  apply Units.ext
  rw [y422Orthogonal3RootReflection_norm_two_matrix v hv]
  rw [y422Orthogonal3RootReflection_norm_two_matrix (-v)
    (by rw [y422Orthogonal3VectorNorm_neg, hv])]
  simp [Matrix.mulVec_neg, Matrix.neg_vecMulVec, Matrix.vecMulVec_neg]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
