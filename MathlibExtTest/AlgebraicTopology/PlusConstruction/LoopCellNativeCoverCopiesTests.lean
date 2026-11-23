/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellNativeCoverCopies
import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCellFamilyCopies

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open AlgebraicTopology.LoopCellNativeCoverCopies AlgebraicTopology.LoopCellSphericalGenerators
open scoped Simplicial

universe u

attribute [local instance] TopCat.toSSet_obj_kanComplex

#check @SSet.KanComplex.nativeCoverCopyCofanIsColimit
#print axioms SSet.KanComplex.nativeCoverCopyCofanIsColimit
#check @SSet.KanComplex.nativeCoverPullbackCopiesIso
#print axioms SSet.KanComplex.nativeCoverPullbackCopiesIso
#check @SSet.KanComplex.nativeCoverPullbackCopiesIso_deck
#print axioms SSet.KanComplex.nativeCoverPullbackCopiesIso_deck
#check @AlgebraicTopology.LoopCellNativeCoverCopies.nativeDeckGroupEquiv
#print axioms AlgebraicTopology.LoopCellNativeCoverCopies.nativeDeckGroupEquiv
#check @AlgebraicTopology.LoopCellNativeCoverCopies.diskFamilyCopiesIso
#print axioms AlgebraicTopology.LoopCellNativeCoverCopies.diskFamilyCopiesIso
#check @AlgebraicTopology.LoopCellNativeCoverCopies.boundaryFamilyCopiesIso_disk_ι
#print axioms AlgebraicTopology.LoopCellNativeCoverCopies.boundaryFamilyCopiesIso_disk_ι
#check @AlgebraicTopology.LoopCellNativeCoverCopies.boundaryFamilyLift_toCover
#print axioms AlgebraicTopology.LoopCellNativeCoverCopies.boundaryFamilyLift_toCover

/-- Every quotient-labelled copy retains the entire original characteristic disk. -/
private theorem client_every_translated_original_disk
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q : FundamentalGroup X x ⧸ P) (p : P) :
    CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p ≫
        ((CategoryTheory.Limits.Sigma.ι
          (fun _ : FundamentalGroup X x ⧸ P => diskFamily X x P) q ≫
            (diskFamilyCopiesIso X x P).hom) ≫
          (pullback.snd (diskFamilyLift X x P ≫ SSet.KanComplex.nativeCoverProjection
              (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P))
            (SSet.KanComplex.nativeCoverProjection
              (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P)) ≫
            SSet.KanComplex.nativeCoverProjection
              (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P))) =
      sSetTopAdj.homEquiv (Δ[2] : SSet.{u}) (LoopCellAttachment.space X x P)
        ((diskBoundaryArrowIso 2).hom.right ≫ LoopCellAttachment.cell X x P p) := by
  let L := diskFamilyLift X x P
  let e := nativeDeckGroupEquiv X x P
  let a := e.symm q
  let π := SSet.KanComplex.nativeCoverProjection
    (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P)
  let d := CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p
  have hc := diskFamilyCopiesIso_ι X x P q
  have hs := SSet.KanComplex.nativeCoverCopyLift_snd L a
  have hd := SSet.KanComplex.nativeCoverDeckMap_projection
    (X := TopCat.toSSet.obj (LoopCellAttachment.space X x P))
    (x := nativeTargetPoint X x P) a
  have hL : d ≫ L = nativeDiskLift X x P p :=
    diskFamilyLift_ι X x P p
  change d ≫ ((CategoryTheory.Limits.Sigma.ι
    (fun _ : FundamentalGroup X x ⧸ P => diskFamily X x P) q ≫
      (diskFamilyCopiesIso X x P).hom) ≫ (pullback.snd (L ≫ π) π ≫ π)) = _
  rw [hc, ← Category.assoc (SSet.KanComplex.nativeCoverCopyLift L a)
    (pullback.snd (L ≫ π) π) π, hs]
  rw [Category.assoc L (SSet.KanComplex.nativeCoverDeckMap
    (X := TopCat.toSSet.obj (LoopCellAttachment.space X x P))
    (x := nativeTargetPoint X x P) a) π, hd]
  rw [← Category.assoc d L π, hL]
  exact nativeDiskLift_projection X x P p

/-- The same boundary copies retain the actual noncommutative left deck-product order. -/
private theorem client_boundary_after_deck_product
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q r : FundamentalGroup X x ⧸ P) :
    boundarySum X x P ≫
        (CategoryTheory.Limits.Sigma.ι
          (fun _ : FundamentalGroup X x ⧸ P => diskFamily X x P) (q * r) ≫
            (diskFamilyCopiesIso X x P).hom) =
      ((CategoryTheory.Limits.Sigma.ι
        (fun _ : FundamentalGroup X x ⧸ P => boundaryFamily X x P) r ≫
          (boundaryFamilyCopiesIso X x P).hom) ≫
        SSet.KanComplex.nativeCoverCopyBaseChange (diskFamilyLift X x P) (boundarySum X x P)) ≫
          SSet.KanComplex.nativeCoverCopyPullbackDeck (diskFamilyLift X x P)
            ((nativeDeckGroupEquiv X x P).symm q) := by
  exact (congrArg (fun h => boundarySum X x P ≫ h)
    (diskFamilyCopiesIso_deck_ι X x P q r)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun h => h ≫ SSet.KanComplex.nativeCoverCopyPullbackDeck
          (diskFamilyLift X x P) ((nativeDeckGroupEquiv X x P).symm q))
          (boundaryFamilyCopiesIso_disk_ι X x P r)))


#check @SSet.KanComplex.nativeCoverCellFamilyLift_ι
#print axioms SSet.KanComplex.nativeCoverCellFamilyLift_ι

/-- The generic whole-family recipe retains the actual original disk and its full adjoint projection. -/
theorem client_actual_cell_family_lift (X : TopCat.{u}) [PathConnectedSpace X]
    (x : X) (P : Subgroup (FundamentalGroup X x)) (p : P) :
    let l := fun p : P => LoopCellSphericalGenerators.nativeDiskLift X x P p
    let L := SSet.KanComplex.nativeCoverCellFamilyLift l
    let j := CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p
    let π := SSet.KanComplex.nativeCoverProjection
      (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P)
    j ≫ L = l p ∧ j ≫ L ≫ π =
      sSetTopAdj.homEquiv (Δ[2] : SSet.{u}) (LoopCellAttachment.space X x P)
        ((diskBoundaryArrowIso 2).hom.right ≫ LoopCellAttachment.cell X x P p) := by
  let l := fun p : P => LoopCellSphericalGenerators.nativeDiskLift X x P p
  let L := SSet.KanComplex.nativeCoverCellFamilyLift l
  let j := CategoryTheory.Limits.Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p
  let π := SSet.KanComplex.nativeCoverProjection
    (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P)
  have h : j ≫ L = l p := SSet.KanComplex.nativeCoverCellFamilyLift_ι l p
  exact ⟨h, (Category.assoc j L π).symm.trans
    ((congrArg (fun k => k ≫ π) h).trans
      (LoopCellSphericalGenerators.nativeDiskLift_projection X x P p))⟩

end

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open AlgebraicTopology.LoopCellNativeCoverCopies
open AlgebraicTopology.LoopCellSphericalGenerators
open scoped Simplicial

universe u w


#check AlgebraicTopology.LoopCellNativeCoverCopies.boundarySum_eq
#print axioms AlgebraicTopology.LoopCellNativeCoverCopies.boundarySum_eq
#check AlgebraicTopology.LoopCellNativeCoverCopies.diskFamilyLift_ι
#print axioms AlgebraicTopology.LoopCellNativeCoverCopies.diskFamilyLift_ι
#check AlgebraicTopology.LoopCellNativeCoverCopies.boundaryFamilyLift_ι
#print axioms AlgebraicTopology.LoopCellNativeCoverCopies.boundaryFamilyLift_ι

/-- Each family component retains the actual matched original boundary adjoint. -/
theorem client_actual_family_boundary_source (X : TopCat.{w}) [PathConnectedSpace X]
    (x : X) (P : Subgroup (FundamentalGroup X x)) (p : P) :
    CategoryTheory.Limits.Sigma.ι (fun _ : P => (SSet.boundary.{w} 2).toSSet) p ≫
        boundaryFamilyLift X x P ≫ nativePullbackProjection X x P =
      sSetTopAdj.homEquiv (SSet.boundary.{w} 2).toSSet X
        ((diskBoundaryArrowIso.{w} 2).hom.left ≫ LoopCellAttachment.attachingMap X x P p) := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ nativePullbackProjection X x P)
      (boundaryFamilyLift_ι X x P p)).trans (nativeBoundaryLift_source X x P p))

#check @TopCat.singularMappedVertexIso_eq
#print axioms TopCat.singularMappedVertexIso_eq
#check @AlgebraicTopology.LoopCellNativeCoverCopies.nativeDeckGroupEquiv_canonical
#print axioms AlgebraicTopology.LoopCellNativeCoverCopies.nativeDeckGroupEquiv_canonical

/-- The actual deck label agrees with the original quotient-point dictionary
on every native loop, independently of the first paths of the cell lifts. -/
theorem client_original_quotient_deck_index (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (a : End (SSet.FundamentalGroupoid.mk (LoopCellSphericalGenerators.nativeTargetPoint X x P))) :
    LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P a =
      (LoopCellAttachment.fundamentalGroupQuotientMulEquiv X x P).symm
        (TopCat.singularFundamentalGroupoidEndMulEquiv (LoopCellAttachment.space X x P)
          (LoopCellAttachment.inclusion X x P x)
            ((eqToIso
              ((SSet.mapFundamentalGroupoid_obj_mk
                  (TopCat.toSSet.map (LoopCellAttachment.inclusion X x P))
                  (TopCat.toSSetObj₀Equiv.symm x)).symm.trans
                (TopCat.singularMappedVertex_eq (LoopCellAttachment.inclusion X x P) x))).conj a)) :=
  LoopCellNativeCoverCopies.nativeDeckGroupEquiv_canonical X x P a

end
