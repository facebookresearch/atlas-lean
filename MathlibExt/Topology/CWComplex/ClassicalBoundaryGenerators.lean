/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex

/-!
# Classical and canonical boundary generators through their original realization

The existing matched simplex-to-classical-disk Arrow Iso and the existing
simplex-to-Euclidean-disk Arrow Iso supply the entire comparison, including zero.
Both boundary and disk maps are projections of that same complete comparison.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace Topology.CWComplex.ClassicalBoundaryGenerators

/-- The complete classical boundary Arrow uses the two existing matched realization comparisons. -/
def classicalToEuclideanArrowIso (n : ℕ) :
    Arrow.mk (classicalCellDiskPair.{u} n).map ≅
      Arrow.mk (TopCat.diskBoundaryInclusion.{u} n) :=
  (SSet.boundary.toClassicalCellDiskArrowIso.{u} n).symm ≪≫
    SSet.boundary.toTopDiskArrowIso.{u} n

/-- The boundary comparison is the actual left component of the whole original Arrow Iso. -/
def classicalSphereEuclideanIso (n : ℕ) :
    (classicalCellDiskPair.{u} n).snd ≅ TopCat.diskBoundary.{u} n :=
  Arrow.leftFunc.mapIso (classicalToEuclideanArrowIso.{u} n)

/-- The disk comparison is the actual right component of the same whole original Arrow Iso. -/
def classicalDiskEuclideanIso (n : ℕ) :
    (classicalCellDiskPair.{u} n).fst ≅ TopCat.disk.{u} n :=
  Arrow.rightFunc.mapIso (classicalToEuclideanArrowIso.{u} n)

/-- Both original components retain the full boundary square in every dimension, including zero. -/
theorem classicalDiskEuclideanIso_boundary (n : ℕ) :
    (classicalCellDiskPair.{u} n).map ≫ (classicalDiskEuclideanIso.{u} n).hom =
      (classicalSphereEuclideanIso.{u} n).hom ≫ TopCat.diskBoundaryInclusion.{u} n :=
  (classicalToEuclideanArrowIso.{u} n).hom.w.symm

end Topology.CWComplex.ClassicalBoundaryGenerators
