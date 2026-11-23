/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.RelativeSkeletalColimit
public import MathlibExt.Topology.CWComplex.ClassicalBoundaryGenerators
public import Mathlib.Topology.CWComplex.Abstract.Basic

/-!
# The actual relative cell presentation of a classical subcomplex

The given subcomplex and original strict skeleta provide the actual stages.
Each successor attaches precisely the original cells outside the subcomplex.
The complete canonical relative CW structure retains those identifiers,
both boundary comparison maps and the inclusion into the original space.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology

namespace Topology.CWComplex

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
  (A : Subcomplex (Set.univ : Set X))

/-- Every original relative successor attaches the exact complementary classical cells. -/
def relativeSkeletonAttachCells (n : ℕ) :
    AttachCells.{u} (fun _ : Unit => (classicalCellDiskPair.{u} n).map)
      (relativeSkeletonTransition X A n) where
  ι := relativeCells X A n
  π _ := ()
  cofan₁ := TopCat.sigmaCofan (fun _ : relativeCells X A n =>
    (classicalCellDiskPair.{u} n).snd)
  cofan₂ := TopCat.sigmaCofan (fun _ : relativeCells X A n =>
    (classicalCellDiskPair.{u} n).fst)
  isColimit₁ := TopCat.sigmaCofanIsColimit _
  isColimit₂ := TopCat.sigmaCofanIsColimit _
  m := relativeSphereSumToDiskSum X A n
  hm j := by
    apply TopCat.ext
    intro x
    rfl
  g₁ := relativeSphereSumToSkeleton X A n
  g₂ := relativeDiskSumToSkeleton X A n
  isPushout := isPushout_relativeSkeletonAttachment X A n

/-- The original complementary identifiers are the actual attached-cell index type. -/
theorem relativeSkeletonAttachCells_indices (n : ℕ) :
    (relativeSkeletonAttachCells X A n).ι = relativeCells X A n := rfl

/-- Every attached classical disk retains its complete original characteristic map. -/
theorem relativeSkeletonAttachCells_cell (n : ℕ) (j : relativeCells X A n) :
    (relativeSkeletonAttachCells X A n).cell j =
      characteristicRelativeDiskToSkeleton X A n j := by
  apply TopCat.ext
  intro x
  rfl

/-- The zero relative stage is the given original subcomplex, through identity point maps. -/
def relativeSkeletalInitialIso :
    (relativeSkeletalDiagram X A).obj 0 ≅ TopCat.of (A : Set X) :=
  TopCat.isoOfHomeo (Homeomorph.setCongr (coe_relativeSkeleton_zero X A))

/-- The full relative dimension history is a cell complex of the original max-norm disks. -/
def classicalSubcomplexCellComplex :
    RelativeCellComplex.{u}
      (fun (n : ℕ) (_ : Unit) => (classicalCellDiskPair.{u} n).map)
      (subcomplexInclusion A) where
  F := relativeSkeletalDiagram X A
  isoBot := relativeSkeletalInitialIso X A
  incl := (relativeSkeletalCocone X A).ι
  isColimit := relativeSkeletalCoconeIsColimit X A
  fac := by
    apply TopCat.ext
    intro x
    rfl
  attachCells n _ := relativeSkeletonAttachCells X A n

/-- The original classical subcomplex inclusion has the canonical full relative CW structure. -/
def classicalSubcomplexRelativeCWComplex :
    TopCat.RelativeCWComplex (subcomplexInclusion A) :=
  let c := classicalSubcomplexCellComplex X A
  { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
    attachCells := fun n hn =>
      (c.attachCells n hn).reindexCellTypes (TopCat.RelativeCWComplex.basicCell n) id
        (fun _ => ClassicalBoundaryGenerators.classicalToEuclideanArrowIso.{u} n) }

/-- The full returned stage functor is the unchanged original relative skeletal diagram. -/
theorem classicalSubcomplexRelativeCWComplex_functor :
    (classicalSubcomplexRelativeCWComplex X A).F = relativeSkeletalDiagram X A := rfl

/-- Every actual stage is the original subcomplex union the original strict skeleton. -/
theorem classicalSubcomplexRelativeCWComplex_stage (n : ℕ) :
    (classicalSubcomplexRelativeCWComplex X A).F.obj n =
      relativeSkeletonTop X A n := rfl

/-- The initial stage is the entire given subcomplex, including when no cells occur. -/
theorem classicalSubcomplexRelativeCWComplex_zero :
    (classicalSubcomplexRelativeCWComplex X A).F.obj 0 = TopCat.of (A : Set X) :=
  congrArg (fun S : Set X => TopCat.of S) (coe_relativeSkeleton_zero X A)

/-- The returned complete colimit cocone retains every original ambient inclusion. -/
theorem classicalSubcomplexRelativeCWComplex_inclusion (n : ℕ) :
    (classicalSubcomplexRelativeCWComplex X A).incl.app n =
      relativeSkeletonInclusion X A n := rfl

/-- Canonical disk conversion leaves the original complementary cell identifiers unchanged. -/
theorem classicalSubcomplexRelativeCWComplex_indices (n : ℕ) (hn : ¬ IsMax n) :
    ((classicalSubcomplexRelativeCWComplex X A).attachCells n hn).ι =
      relativeCells X A n := rfl

/-- Every canonical cell map keeps the full original inverse disk comparison and characteristic map. -/
theorem classicalSubcomplexRelativeCWComplex_cell (n : ℕ) (hn : ¬ IsMax n)
    (j : relativeCells X A n) :
    ((classicalSubcomplexRelativeCWComplex X A).attachCells n hn).cell j =
      (ClassicalBoundaryGenerators.classicalDiskEuclideanIso.{u} n).inv ≫
        characteristicRelativeDiskToSkeleton X A n j := by
  apply TopCat.ext
  intro x
  rfl

/-- The complete canonical cell-to-colimit map reaches the original characteristic disk in X. -/
theorem classicalSubcomplexRelativeCWComplex_cell_inclusion (n : ℕ) (hn : ¬ IsMax n)
    (j : relativeCells X A n) :
    ((classicalSubcomplexRelativeCWComplex X A).attachCells n hn).cell j ≫
        (classicalSubcomplexRelativeCWComplex X A).incl.app (n + 1) =
      (ClassicalBoundaryGenerators.classicalDiskEuclideanIso.{u} n).inv ≫
        characteristicDiskMap n j.val := by
  apply TopCat.ext
  intro x
  rfl

end Topology.CWComplex
