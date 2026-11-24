/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

import MathlibExt.AlgebraicTopology.SimplicialObject.DiagonalPreservesLimits
import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialDiagonal

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe v u

example : PreservesLimitsOfShape (Discrete WalkingPair)
    (CategoryTheory.SimplicialObject.diagonalFunctor (Type 0)) := by
  infer_instance

example : PreservesLimitsOfShape (Discrete WalkingPair)
    (CategoryTheory.SimplicialObject.diagonalFunctor (Type 1)) := by
  infer_instance

example : PreservesLimitsOfShape (Discrete WalkingPair)
    SSet.simplicialDiagonalFunctor.{0} := by
  infer_instance

example : PreservesLimitsOfShape (Discrete WalkingPair)
    SSet.simplicialDiagonalFunctor.{1} := by
  infer_instance

example (X Y : SimplicialObject (SimplicialObject (Type (max u v)))) :
    PreservesLimit (pair X Y)
      (CategoryTheory.SimplicialObject.diagonalFunctor (Type (max u v))) := by
  infer_instance

example (X Y : SimplicialObject SSet.{max u v}) :
    PreservesLimit (pair X Y) SSet.simplicialDiagonalFunctor := by
  infer_instance

#print axioms CategoryTheory.SimplicialObject.diagonalFunctor_preservesLimitsOfShape
#print axioms SSet.simplicialDiagonalFunctor_preservesLimitsOfShape
