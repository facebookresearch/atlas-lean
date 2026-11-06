/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Four hyperbolic pairs for the independent characteristic-three source form. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3FullGroup

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The standard split eight-dimensional form with four actual hyperbolic pairs. -/
def y422Orthogonal3HyperbolicGram : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  ![![0, 1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0]]

/-- An explicit change of coordinates from four hyperbolic pairs to the original source form. -/
def y422Orthogonal3HyperbolicBasis : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  ![![0, 2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 2, 0, 0],
    ![0, 0, 0, 0, 1, 2, 2, 2],
    ![0, 0, 1, 2, 2, 1, 0, 2],
    ![1, 2, 1, 2, 0, 0, 0, 1],
    ![2, 1, 0, 2, 0, 0, 0, 2],
    ![0, 0, 2, 1, 0, 0, 2, 1]]

/-- The exact two-sided inverse of the actual hyperbolic coordinate change. -/
def y422Orthogonal3HyperbolicInverse : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  ![![2, 1, 0, 0, 0, 1, 0, 1],
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 2, 2, 2],
    ![0, 0, 0, 2, 2, 2, 2, 1],
    ![0, 1, 2, 1, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 2, 0, 2, 2, 0, 0, 2],
    ![0, 2, 0, 1, 1, 0, 0, 1]]

/-- Actual finite matrix multiplication certifies the invertible hyperbolic coordinate change. -/
theorem y422Orthogonal3HyperbolicBasis_inverse :
    y422Orthogonal3HyperbolicBasis * y422Orthogonal3HyperbolicInverse = 1 ∧
      y422Orthogonal3HyperbolicInverse * y422Orthogonal3HyperbolicBasis = 1 := by
  decide +kernel

/-- The original source form is exactly the split four-pair form in these coordinates. -/
theorem y422Orthogonal3HyperbolicBasis_gram :
    y422Orthogonal3HyperbolicBasis.transpose * y422Orthogonal3Gram *
      y422Orthogonal3HyperbolicBasis = y422Orthogonal3HyperbolicGram := by
  decide +kernel

/-- The actual hyperbolic coordinate change as an invertible finite matrix. -/
def y422Orthogonal3HyperbolicGL : Matrix.GeneralLinearGroup (Fin 8) (ZMod 3) :=
  ⟨y422Orthogonal3HyperbolicBasis, y422Orthogonal3HyperbolicInverse,
    y422Orthogonal3HyperbolicBasis_inverse.1, y422Orthogonal3HyperbolicBasis_inverse.2⟩

/-- The exact quadratic values transform to the independent standard split form. -/
theorem y422Orthogonal3HyperbolicBasis_norm (v : Fin 8 → ZMod 3) :
    y422Orthogonal3VectorNorm (y422Orthogonal3HyperbolicBasis *ᵥ v) =
      dotProduct v (y422Orthogonal3HyperbolicGram *ᵥ v) := by
  unfold y422Orthogonal3VectorNorm
  rw [dotProduct_comm (y422Orthogonal3HyperbolicBasis *ᵥ v),
    ← Matrix.dotProduct_transpose_mulVec]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, y422Orthogonal3HyperbolicBasis_gram]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
