/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.RootUnitContraction
public import MathlibExt.Topology.Homotopy.IntervalPathSpaceHomotopy
public import MathlibExt.Topology.Homotopy.IntervalHalfPaths

/-!
# Actual interval middle-unit triangle

The original three-stage middle reassociation unit Path and the same two
endpoint contractions give one actual boundary Path in the interval loop
space. The existing interval path-space homotopy compares it with the
same composite-root contraction, retaining all three coordinates.
-/

public section

noncomputable section

open unitInterval
open scoped Topology

namespace ContinuousMap

private def actualIntervalLeftUnitPath :
    Path (loopBasepointChange pathHalfLeft (Path.refl (0 : I)))
      (Path.refl pathHalfPoint) :=
  ((rootUnitContraction (fun r : Path (0 : I) pathHalfPoint => r)
    continuous_eval).evalAt pathHalfLeft).cast
      (rootUnitLoopFamily_pathSpace_apply pathHalfLeft).symm rfl

private def actualIntervalRightUnitPath :
    Path (loopBasepointChange pathHalfRight (Path.refl pathHalfPoint))
      (Path.refl (1 : I)) :=
  ((rootUnitContraction (fun r : Path pathHalfPoint (1 : I) => r)
    continuous_eval).evalAt pathHalfRight).cast
      (rootUnitLoopFamily_pathSpace_apply pathHalfRight).symm rfl

/-- The actual original interval middle unit boundary includes the
same target-root image of the first contraction and the second contraction. -/
def intervalMiddleUnitBoundary :
    Path (loopBasepointChange (pathHalfLeft.trans pathHalfRight) (Path.refl (0 : I)))
      (Path.refl (1 : I)) :=
  ((loopBasepointChangeTransHomotopy pathHalfLeft pathHalfRight).evalAt
    (Path.refl (0 : I))).trans
      ((actualIntervalLeftUnitPath.map (loopBasepointChange pathHalfRight).continuous).trans
        actualIntervalRightUnitPath)

/-- The comparison Path is the same joint-family contraction of the
actual composite of the two original half roots. -/
def intervalMiddleUnitContraction :
    Path (loopBasepointChange (pathHalfLeft.trans pathHalfRight) (Path.refl (0 : I)))
      (Path.refl (1 : I)) :=
  ((rootUnitContraction (fun r : Path (0 : I) (1 : I) => r)
    continuous_eval).evalAt (pathHalfLeft.trans pathHalfRight)).cast
      (rootUnitLoopFamily_pathSpace_apply (pathHalfLeft.trans pathHalfRight)).symm rfl

private theorem actualIntervalBoundaryPiecesComputed :
    intervalMiddleUnitBoundary =
      ((loopBasepointChangeTransHomotopy pathHalfLeft pathHalfRight).evalAt
        (Path.refl (0 : I))).trans
          (((((rootUnitContraction (fun r : Path (0 : I) pathHalfPoint => r)
            continuous_eval).evalAt pathHalfLeft).cast
              (rootUnitLoopFamily_pathSpace_apply pathHalfLeft).symm rfl).map
                (loopBasepointChange pathHalfRight).continuous).trans
            (((rootUnitContraction (fun r : Path pathHalfPoint (1 : I) => r)
              continuous_eval).evalAt pathHalfRight).cast
                (rootUnitLoopFamily_pathSpace_apply pathHalfRight).symm rfl)) := rfl

/-- The whole boundary contains exactly the actual middle Path and
the same two endpoint contractions with their original root-image join. -/
theorem intervalMiddleUnitBoundary_eq_actualPieces :
    intervalMiddleUnitBoundary =
      ((loopBasepointChangeTransHomotopy pathHalfLeft pathHalfRight).evalAt
        (Path.refl (0 : I))).trans
          (((((rootUnitContraction (fun r : Path (0 : I) pathHalfPoint => r)
            continuous_eval).evalAt pathHalfLeft).cast
              (rootUnitLoopFamily_pathSpace_apply pathHalfLeft).symm rfl).map
                (loopBasepointChange pathHalfRight).continuous).trans
            (((rootUnitContraction (fun r : Path pathHalfPoint (1 : I) => r)
              continuous_eval).evalAt pathHalfRight).cast
                (rootUnitLoopFamily_pathSpace_apply pathHalfRight).symm rfl)) :=
  actualIntervalBoundaryPiecesComputed

private theorem actualIntervalContractionRootComputed :
    intervalMiddleUnitContraction =
      ((rootUnitContraction (fun r : Path (0 : I) (1 : I) => r)
        continuous_eval).evalAt (pathHalfLeft.trans pathHalfRight)).cast
          (rootUnitLoopFamily_pathSpace_apply (pathHalfLeft.trans pathHalfRight)).symm rfl := rfl

/-- The whole comparison Path is the same joint-family contraction
at the actual composite root with its derived original source cast. -/
theorem intervalMiddleUnitContraction_eq_actualRoot :
    intervalMiddleUnitContraction =
      ((rootUnitContraction (fun r : Path (0 : I) (1 : I) => r)
        continuous_eval).evalAt (pathHalfLeft.trans pathHalfRight)).cast
          (rootUnitLoopFamily_pathSpace_apply (pathHalfLeft.trans pathHalfRight)).symm rfl :=
  actualIntervalContractionRootComputed

/-- The existing fixed-endpoint interval path-space homotopy compares
the two actual middle-unit boundary Paths, retaining the same full contractions. -/
def intervalMiddleUnitTriangleHomotopy :
    intervalMiddleUnitBoundary.Homotopy intervalMiddleUnitContraction :=
  Path.intervalPathSpaceHomotopy intervalMiddleUnitBoundary intervalMiddleUnitContraction

private theorem actualIntervalMiddleUnitValueComputed (t r s : I) :
    intervalMiddleUnitTriangleHomotopy (t, r) s =
      Set.Icc.convexComb (intervalMiddleUnitBoundary r s)
        (intervalMiddleUnitContraction r s) t :=
  Path.intervalPathSpaceHomotopy_apply
    intervalMiddleUnitBoundary intervalMiddleUnitContraction t r s

/-- Every comparison, boundary-Path and loop time has the original
pointwise interval coordinate on the two actual middle-unit Paths. -/
theorem intervalMiddleUnitTriangleHomotopy_apply (t r s : I) :
    intervalMiddleUnitTriangleHomotopy (t, r) s =
      Set.Icc.convexComb (intervalMiddleUnitBoundary r s)
        (intervalMiddleUnitContraction r s) t :=
  actualIntervalMiddleUnitValueComputed t r s

/-- The actual source unit image equals the identity-template image
only by the computed whole concatenation of the two original half paths. -/
theorem intervalMiddleUnitSource_eq_identity :
    loopBasepointChange (pathHalfLeft.trans pathHalfRight) (Path.refl (0 : I)) =
      loopBasepointChange Path.id (Path.refl (0 : I)) :=
  congrArg (fun p : Path (0 : I) (1 : I) => loopBasepointChange p (Path.refl (0 : I)))
    pathHalfLeft_trans_right

end ContinuousMap

end
