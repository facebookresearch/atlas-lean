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

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Geometry 389

/-!
# Ellipsoidal Body

## References

* This is the standard geometric definition of an ellipsoid as a nonsingular affine image of a
  Euclidean ball. See: R. J. Gardner, Geometric Tomography, 2nd ed., Cambridge University Press,
  2006. Gardner defines an ellipsoid in Euclidean space to be an affine image of the unit ball.
  For a full-dimensional ellipsoidal body, the affine map is equivalently taken to be invertible.
  It is the notion of ellipsoid appearing in the Agranovsky rigidity problem. (for
  `IsEllipsoidalBody`)

## References

* This is the standard geometric definition of an ellipsoid as a nonsingular affine image of a
  Euclidean ball. See: R. J. Gardner, Geometric Tomography, 2nd ed., Cambridge University Press,
  2006. Gardner defines an ellipsoid in Euclidean space to be an affine image of the unit ball.
  For a full-dimensional ellipsoidal body, the affine map is equivalently taken to be invertible.
  It is the notion of ellipsoid appearing in the Agranovsky rigidity problem. (for
  `IsEllipsoidalBody`)

## References

* This is the standard geometric definition of an ellipsoid as a nonsingular affine image of a
  Euclidean ball. See: R. J. Gardner, Geometric Tomography, 2nd ed., Cambridge University Press,
  2006. Gardner defines an ellipsoid in Euclidean space to be an affine image of the unit ball.
  For a full-dimensional ellipsoidal body, the affine map is equivalently taken to be invertible.
  It is the notion of ellipsoid appearing in the Agranovsky rigidity problem. (for
  `IsEllipsoidalBody`)

## References

* This is the standard geometric definition of an ellipsoid as a nonsingular affine image of a
  Euclidean ball. See: R. J. Gardner, Geometric Tomography, 2nd ed., Cambridge University Press,
  2006. Gardner defines an ellipsoid in Euclidean space to be an affine image of the unit ball.
  For a full-dimensional ellipsoidal body, the affine map is equivalently taken to be invertible.
  It is the notion of ellipsoid appearing in the Agranovsky rigidity problem. (for
  `IsEllipsoidalBody`)

## References

* This is the standard geometric definition of an ellipsoid as a nonsingular affine image of a
  Euclidean ball. See: R. J. Gardner, Geometric Tomography, 2nd ed., Cambridge University Press,
  2006. Gardner defines an ellipsoid in Euclidean space to be an affine image of the unit ball.
  For a full-dimensional ellipsoidal body, the affine map is equivalently taken to be invertible.
  It is the notion of ellipsoid appearing in the Agranovsky rigidity problem. (for
  `IsEllipsoidalBody`)

## References

* This is the standard geometric definition of an ellipsoid as a nonsingular affine image of a
  Euclidean ball. See: R. J. Gardner, Geometric Tomography, 2nd ed., Cambridge University Press,
  2006. Gardner defines an ellipsoid in Euclidean space to be an affine image of the unit ball.
  For a full-dimensional ellipsoidal body, the affine map is equivalently taken to be invertible.
  It is the notion of ellipsoid appearing in the Agranovsky rigidity problem. (for
  `IsEllipsoidalBody`)

## References

* This is the standard geometric definition of an ellipsoid as a nonsingular affine image of a
  Euclidean ball. See: R. J. Gardner, Geometric Tomography, 2nd ed., Cambridge University Press,
  2006. Gardner defines an ellipsoid in Euclidean space to be an affine image of the unit ball.
  For a full-dimensional ellipsoidal body, the affine map is equivalently taken to be invertible.
  It is the notion of ellipsoid appearing in the Agranovsky rigidity problem. (for
  `IsEllipsoidalBody`)
-/

namespace MetaMathlibExt

-- Geometry 389: Ellipsoidal Body

/-- A set

K⊂ℝⁿ

is an ellipsoidal body if it is the image of the closed Euclidean unit
ball under an invertible affine transformation of ℝⁿ.

Thus
$$
K=T(\overline{B(0,1)})
$$
for some affine equivalence

T:ℝⁿ→ℝⁿ.
-/
def IsEllipsoidalBody
    {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ e :
      EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ]
        EuclideanSpace ℝ (Fin n),
    K =
      e '' Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin n)) 1

end MetaMathlibExt

end
