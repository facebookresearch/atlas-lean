/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import MathlibExt.Geometry.Euclidean.Ellipsoid

@[expose] public section

namespace MathlibExtTest.Geometry.Euclidean.Ellipsoid

open MetaMathlibExt

-- Geometry 389: Ellipsoidal Body

theorem closedBall_isEllipsoidalBody
    (n : ℕ) :
    IsEllipsoidalBody
      (Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  refine ⟨
    AffineEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)),
    ?_
  ⟩
  simp

end MathlibExtTest.Geometry.Euclidean.Ellipsoid

end
