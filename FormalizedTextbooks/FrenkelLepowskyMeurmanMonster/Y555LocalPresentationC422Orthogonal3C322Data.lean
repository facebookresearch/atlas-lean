/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual C322 fixed-vector and intertwining data in the concrete projective C422 model. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3Hom
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422C322

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- A nonzero norm-two vector fixed by all eight original C322 source reflections. -/
def y422Orthogonal3FixedVector : Fin 8 → ZMod 3 := ![0, 2, 1, 0, 2, 1, 2, 0]

/-- The actual fixed vector is nonzero. -/
theorem y422Orthogonal3FixedVector_ne_zero : y422Orthogonal3FixedVector ≠ 0 := by decide +kernel

/-- The fixed vector has its exact norm in the actual nonsingular source form. -/
theorem y422Orthogonal3FixedVector_norm :
    dotProduct y422Orthogonal3FixedVector
      (y422Orthogonal3Gram *ᵥ y422Orthogonal3FixedVector) = 2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Eight source reflections are checked against the literal eight-dimensional fixed vector.
/-- Every original C322 source generator actually fixes the supplied vector. -/
theorem y422Orthogonal3C322_generator_fixed (i : Fin 8) :
    y422Orthogonal3Reflection (y422C322Letter i) *ᵥ y422Orthogonal3FixedVector =
      y422Orthogonal3FixedVector := by
  revert i
  decide +kernel

/-- A central scalar fixes this actual nonzero vector precisely when it is the identity scalar. -/
theorem y422Orthogonal3Scalar_fixed_iff (u : (ZMod 3)ˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin 8) u).val *ᵥ y422Orthogonal3FixedVector =
      y422Orthogonal3FixedVector ↔ u = 1 := by
  revert u
  decide +kernel

/-- The seven-dimensional C322 Cartan space is the exact subspace with e1 coordinate zero. -/
def y422Orthogonal3C322Embedding : Matrix (Fin 8) (Fin 7) (ZMod 3) :=
  ![![1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1]]

/-- The exact coordinate projection left inverse of the actual seven-dimensional embedding. -/
def y422Orthogonal3C322Projection : Matrix (Fin 7) (Fin 8) (ZMod 3) :=
  y422Orthogonal3C322Embedding.transpose

/-- The source Cartan subspace has a checked actual left inverse. -/
theorem y422Orthogonal3C322Projection_embedding :
    y422Orthogonal3C322Projection * y422Orthogonal3C322Embedding = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Eight rectangular source-action products are checked entry by entry in the kernel.
/-- The eight actual source actions intertwine with the already faithful C322 representation. -/
theorem y422Orthogonal3C322_generator_intertwines (i : Fin 8) :
    y422Orthogonal3Reflection (y422C322Letter i) * y422Orthogonal3C322Embedding =
      y422Orthogonal3C322Embedding * y322Orthogonal3Reflection i := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
