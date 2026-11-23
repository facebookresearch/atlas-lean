/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellPulledSimplicialModel
public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellNativeCoverCopies
public import MathlibExt.AlgebraicTopology.PlusConstruction.CellFamilyRelativeHomology
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The actual quotient-labelled upstairs two-cell presentation

The complete native copy classification is applied to the SAME original
chosen disk lifts and their boundaries. It gives the literal pulled cell
families, with every quotient label and every original member of the normal
subgroup. Existing realization and colimit transport through the matched
classical disk-boundary Iso identify the entire pulled realization with an
actual classical cell-family attachment on the same old cover. Its full
relative coefficient basis is the established cell-family diagonal Iso.

No identity first-path normalization or expected basis is assumed. Deck
multiplication remains on the left. This presentation is a component of the
quotient-group-ring argument; the native regular-relative transport, Lambda
linear basis and full three-cell/local-coefficient/fiber conclusions are
separate next statements.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Topology.CWComplex
open scoped Simplicial

universe u

namespace OriginalQuotientCellPresentation

private theorem pullbackCongr_fst {A Y Z : SSet.{u}} {f g : A ⟶ Y} (p : Z ⟶ Y)
    (h : f = g) : (pullback.congrHom h rfl).hom ≫ pullback.fst g p = pullback.fst f p := by
  change pullback.lift (pullback.fst f p ≫ 𝟙 A) (pullback.snd f p ≫ 𝟙 Z) _ ≫
    pullback.fst g p = pullback.fst f p
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private theorem pullbackCongr_snd {A Y Z : SSet.{u}} {f g : A ⟶ Y} (p : Z ⟶ Y)
    (h : f = g) : (pullback.congrHom h rfl).hom ≫ pullback.snd g p = pullback.snd f p := by
  change pullback.lift (pullback.fst f p ≫ 𝟙 A) (pullback.snd f p ≫ 𝟙 Z) _ ≫
    pullback.snd g p = pullback.snd f p
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

private theorem transported_projection {A B C D T : SSet.{u}}
    (i : A ⟶ B) (c : B ⟶ C) (e : C ⟶ D) (f : D ⟶ T) (g : C ⟶ T)
    (h : e ≫ f = g) : (i ≫ c ≫ e) ≫ f = (i ≫ c) ≫ g := by
  simp only [Category.assoc, h]

end OriginalQuotientCellPresentation

public section

namespace AlgebraicTopology.LoopCellQuotientCellPresentation

attribute [local instance] TopCat.toSSet_obj_kanComplex

/-- The ACTUAL native deck map for a literal quotient label, using the computed point connector. -/
abbrev nativeDeck (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    LoopCellSphericalGenerators.nativeCover X x P ⟶ LoopCellSphericalGenerators.nativeCover X x P :=
  SSet.KanComplex.nativeCoverDeckMap
    (X := TopCat.toSSet.obj (LoopCellAttachment.space X x P))
    (x := LoopCellSphericalGenerators.nativeTargetPoint X x P)
    ((LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm q)

/-- These deck maps lie over the SAME original projection. -/
theorem nativeDeck_projection (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    nativeDeck X x P q ≫ LoopCellPulledSimplicialModel.projection X x P =
      LoopCellPulledSimplicialModel.projection X x P := by
  exact SSet.KanComplex.nativeCoverDeckMap_projection
    ((LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm q)

/-- The unit deck transformation is the actual identity. -/
theorem nativeDeck_one (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    nativeDeck X x P 1 = 𝟙 (LoopCellSphericalGenerators.nativeCover X x P) := by
  exact (congrArg (fun a => SSet.KanComplex.nativeCoverDeckMap
    (X := TopCat.toSSet.obj (LoopCellAttachment.space X x P))
    (x := LoopCellSphericalGenerators.nativeTargetPoint X x P) a)
      (LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm.map_one).trans
    (SSet.KanComplex.nativeCoverDeckMap_one
      (X := TopCat.toSSet.obj (LoopCellAttachment.space X x P))
      (x := LoopCellSphericalGenerators.nativeTargetPoint X x P))

/-- Noncommutative LEFT multiplication of copy labels is the actual deck composition order. -/
theorem nativeDeck_mul (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q r : FundamentalGroup X x ⧸ P) :
    nativeDeck X x P (q * r) = nativeDeck X x P r ≫ nativeDeck X x P q := by
  exact (congrArg (fun a => SSet.KanComplex.nativeCoverDeckMap
    (X := TopCat.toSSet.obj (LoopCellAttachment.space X x P))
    (x := LoopCellSphericalGenerators.nativeTargetPoint X x P) a)
      ((LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm.map_mul q r)).trans
    (SSet.KanComplex.nativeCoverDeckMap_mul
      ((LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm q)
      ((LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm r))

/-- One literal two-cell for every quotient label and every original member of P. -/
abbrev labels (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :=
  (FundamentalGroup X x ⧸ P) × P

/-- Both original boundary-family constructions use the SAME literal boundary map. -/
theorem boundaryFamilyMap_eq (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    LoopCellNativeCoverCopies.boundarySum X x P = LoopCellSimplicialModel.boundarySum X x P := by
  exact (LoopCellNativeCoverCopies.boundarySum_eq X x P).trans
    (LoopCellSimplicialModel.boundarySum_eq X x P).symm

/-- The chosen whole native disk family projects to the ACTUAL model characteristic family. -/
theorem diskFamilyProjection_eq (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    LoopCellNativeCoverCopies.diskFamilyLift X x P ≫
        LoopCellPulledSimplicialModel.projection X x P =
      LoopCellSimplicialModel.diskMates X x P := by
  apply Sigma.hom_ext
  intro p
  have hArrow : LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2 =
      SSet.boundary.toClassicalCellDiskArrowIso.{u} 2 :=
    LoopCellSphericalGenerators.diskBoundaryArrowIso_eq 2
  have hCharacteristic :
      sSetTopAdj.homEquiv (Δ[2] : SSet.{u}) (LoopCellAttachment.space X x P)
          ((LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).hom.right ≫
            LoopCellAttachment.cell X x P p) =
        sSetTopAdj.homEquiv (Δ[2] : SSet.{u}) (LoopCellAttachment.space X x P)
          ((SSet.boundary.toClassicalCellDiskArrowIso.{u} 2).hom.right ≫
            LoopCellAttachment.cell X x P p) :=
    congrArg (fun e : Arrow.mk (SSet.toTop.map (SSet.boundary.{u} 2).ι) ≅
        Arrow.mk (classicalCellDiskPair.{u} 2).map =>
      sSetTopAdj.homEquiv (Δ[2] : SSet.{u}) (LoopCellAttachment.space X x P)
        (e.hom.right ≫ LoopCellAttachment.cell X x P p)) hArrow
  have hL : Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) p ≫
      LoopCellNativeCoverCopies.diskFamilyLift X x P =
        LoopCellSphericalGenerators.nativeDiskLift X x P p :=
    LoopCellNativeCoverCopies.diskFamilyLift_ι X x P p
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ LoopCellPulledSimplicialModel.projection X x P) hL).trans
      ((LoopCellSphericalGenerators.nativeDiskLift_projection X x P p).trans
        (hCharacteristic.trans (LoopCellSimplicialModel.diskMates_ι X x P p).symm)))

/-- The chosen boundary restrictions project to the ACTUAL model boundary family. -/
theorem boundaryFamilyProjection_eq (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    (LoopCellNativeCoverCopies.boundarySum X x P ≫
        LoopCellNativeCoverCopies.diskFamilyLift X x P) ≫
      LoopCellPulledSimplicialModel.projection X x P =
        LoopCellSimplicialModel.attaching X x P ≫
          LoopCellSphericalGenerators.nativeInclusion X x P := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => LoopCellNativeCoverCopies.boundarySum X x P ≫ h)
      (diskFamilyProjection_eq X x P)).trans
      ((congrArg (fun h => h ≫ LoopCellSimplicialModel.diskMates X x P)
        (boundaryFamilyMap_eq X x P)).trans (LoopCellSimplicialModel.adjunctSquare X x P)))

/-- Every quotient-labelled copy gives the entire literal pulled original disk family. -/
def disksIso (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    (∐ fun _ : FundamentalGroup X x ⧸ P => LoopCellNativeCoverCopies.diskFamily X x P) ≅
      LoopCellPulledSimplicialModel.disks X x P :=
  LoopCellNativeCoverCopies.diskFamilyCopiesIso X x P ≪≫
    pullback.congrHom (diskFamilyProjection_eq X x P) rfl

/-- The boundary copies are restrictions of those SAME chosen lifts, with the SAME labels. -/
def boundariesIso (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    (∐ fun _ : FundamentalGroup X x ⧸ P => LoopCellNativeCoverCopies.boundaryFamily X x P) ≅
      LoopCellPulledSimplicialModel.boundaries X x P :=
  LoopCellNativeCoverCopies.boundaryFamilyCopiesIso X x P ≪≫
    pullback.congrHom (boundaryFamilyProjection_eq X x P) rfl

/-- The entire q-labelled chosen disk family in the literal pulled disks. -/
def diskCopy (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    LoopCellNativeCoverCopies.diskFamily X x P ⟶ LoopCellPulledSimplicialModel.disks X x P :=
  Sigma.ι (fun _ : FundamentalGroup X x ⧸ P => LoopCellNativeCoverCopies.diskFamily X x P) q ≫
    (disksIso X x P).hom

/-- The entire q-labelled boundary family, retaining the chosen first-path shifts. -/
def boundaryCopy (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    LoopCellNativeCoverCopies.boundaryFamily X x P ⟶
        LoopCellPulledSimplicialModel.boundaries X x P :=
  Sigma.ι (fun _ : FundamentalGroup X x ⧸ P => LoopCellNativeCoverCopies.boundaryFamily X x P) q ≫
    (boundariesIso X x P).hom

/-- The original source disk family is unchanged on each whole copy. -/
theorem diskCopy_fst (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    diskCopy X x P q ≫ pullback.fst (LoopCellSimplicialModel.diskMates X x P)
      (LoopCellPulledSimplicialModel.projection X x P) =
        𝟙 (LoopCellNativeCoverCopies.diskFamily X x P) := by
  let p := LoopCellPulledSimplicialModel.projection X x P
  let L : LoopCellNativeCoverCopies.diskFamily X x P ⟶
      LoopCellSphericalGenerators.nativeCover X x P :=
          LoopCellNativeCoverCopies.diskFamilyLift X x P
  let c : (∐ fun _ : FundamentalGroup X x ⧸ P => LoopCellNativeCoverCopies.diskFamily X x P) ≅
      pullback (L ≫ p) p := LoopCellNativeCoverCopies.diskFamilyCopiesIso X x P
  let e : pullback (L ≫ p) p ≅ LoopCellPulledSimplicialModel.disks X x P :=
    pullback.congrHom (diskFamilyProjection_eq X x P) rfl
  let i := Sigma.ι (fun _ : FundamentalGroup X x ⧸ P =>
    LoopCellNativeCoverCopies.diskFamily X x P) q
  let a := (LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm q
  let f : LoopCellPulledSimplicialModel.disks X x P ⟶
      LoopCellNativeCoverCopies.diskFamily X x P :=
          pullback.fst (LoopCellSimplicialModel.diskMates X x P) p
  let g : pullback (L ≫ p) p ⟶
      LoopCellNativeCoverCopies.diskFamily X x P := pullback.fst (L ≫ p) p
  have hE : e.hom ≫ f = g :=
    OriginalQuotientCellPresentation.pullbackCongr_fst p (diskFamilyProjection_eq X x P)
  have hC : i ≫ c.hom = SSet.KanComplex.nativeCoverCopyLift L a :=
    LoopCellNativeCoverCopies.diskFamilyCopiesIso_ι X x P q
  have h : diskCopy X x P q ≫ f = (i ≫ c.hom) ≫ g :=
    OriginalQuotientCellPresentation.transported_projection i c.hom e.hom f g hE
  exact h.trans
    ((congrArg (fun t => t ≫ g) hC).trans (SSet.KanComplex.nativeCoverCopyLift_fst L a))

/-- Each whole disk copy uses exactly the chosen family followed by its actual deck map. -/
theorem diskCopy_snd (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    diskCopy X x P q ≫ pullback.snd (LoopCellSimplicialModel.diskMates X x P)
      (LoopCellPulledSimplicialModel.projection X x P) =
        LoopCellNativeCoverCopies.diskFamilyLift X x P ≫
          nativeDeck X x P q := by
  let p := LoopCellPulledSimplicialModel.projection X x P
  let L : LoopCellNativeCoverCopies.diskFamily X x P ⟶
      LoopCellSphericalGenerators.nativeCover X x P :=
          LoopCellNativeCoverCopies.diskFamilyLift X x P
  let c : (∐ fun _ : FundamentalGroup X x ⧸ P => LoopCellNativeCoverCopies.diskFamily X x P) ≅
      pullback (L ≫ p) p := LoopCellNativeCoverCopies.diskFamilyCopiesIso X x P
  let e : pullback (L ≫ p) p ≅ LoopCellPulledSimplicialModel.disks X x P :=
    pullback.congrHom (diskFamilyProjection_eq X x P) rfl
  let i := Sigma.ι (fun _ : FundamentalGroup X x ⧸ P =>
    LoopCellNativeCoverCopies.diskFamily X x P) q
  let a := (LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm q
  let f : LoopCellPulledSimplicialModel.disks X x P ⟶
      LoopCellSphericalGenerators.nativeCover X x P :=
          pullback.snd (LoopCellSimplicialModel.diskMates X x P) p
  let g : pullback (L ≫ p) p ⟶
      LoopCellSphericalGenerators.nativeCover X x P := pullback.snd (L ≫ p) p
  have hE : e.hom ≫ f = g :=
    OriginalQuotientCellPresentation.pullbackCongr_snd p (diskFamilyProjection_eq X x P)
  have hC : i ≫ c.hom = SSet.KanComplex.nativeCoverCopyLift L a :=
    LoopCellNativeCoverCopies.diskFamilyCopiesIso_ι X x P q
  have h : diskCopy X x P q ≫ f = (i ≫ c.hom) ≫ g :=
    OriginalQuotientCellPresentation.transported_projection i c.hom e.hom f g hE
  exact h.trans
    ((congrArg (fun t => t ≫ g) hC).trans (SSet.KanComplex.nativeCoverCopyLift_snd L a))

/-- The entire source boundary family is unchanged on each whole copy. -/
theorem boundaryCopy_fst (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    boundaryCopy X x P q ≫ pullback.fst
      (LoopCellSimplicialModel.attaching X x P ≫ LoopCellSphericalGenerators.nativeInclusion X x P)
      (LoopCellPulledSimplicialModel.projection X x P) =
        𝟙 (LoopCellNativeCoverCopies.boundaryFamily X x P) := by
  let p := LoopCellPulledSimplicialModel.projection X x P
  let L : LoopCellNativeCoverCopies.boundaryFamily X x P ⟶
      LoopCellSphericalGenerators.nativeCover X x P :=
          LoopCellNativeCoverCopies.boundarySum X x P ≫
          LoopCellNativeCoverCopies.diskFamilyLift X x P
  let c : (∐ fun _ : FundamentalGroup X x ⧸ P => LoopCellNativeCoverCopies.boundaryFamily X x P) ≅
      pullback (L ≫ p) p := LoopCellNativeCoverCopies.boundaryFamilyCopiesIso X x P
  let e : pullback (L ≫ p) p ≅ LoopCellPulledSimplicialModel.boundaries X x P :=
    pullback.congrHom (boundaryFamilyProjection_eq X x P) rfl
  let i := Sigma.ι (fun _ : FundamentalGroup X x ⧸ P =>
    LoopCellNativeCoverCopies.boundaryFamily X x P) q
  let a := (LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm q
  let f : LoopCellPulledSimplicialModel.boundaries X x P ⟶
      LoopCellNativeCoverCopies.boundaryFamily X x P :=
          pullback.fst (LoopCellSimplicialModel.attaching X x P ≫
            LoopCellSphericalGenerators.nativeInclusion X x P) p
  let g : pullback (L ≫ p) p ⟶
      LoopCellNativeCoverCopies.boundaryFamily X x P := pullback.fst (L ≫ p) p
  have hE : e.hom ≫ f = g :=
    OriginalQuotientCellPresentation.pullbackCongr_fst p (boundaryFamilyProjection_eq X x P)
  have hC : i ≫ c.hom = SSet.KanComplex.nativeCoverCopyLift L a :=
    LoopCellNativeCoverCopies.boundaryFamilyCopiesIso_ι X x P q
  have h : boundaryCopy X x P q ≫ f = (i ≫ c.hom) ≫ g :=
    OriginalQuotientCellPresentation.transported_projection i c.hom e.hom f g hE
  exact h.trans
    ((congrArg (fun t => t ≫ g) hC).trans (SSet.KanComplex.nativeCoverCopyLift_fst L a))

/-- The boundary coordinate is the boundary of the SAME chosen translated disk family. -/
theorem boundaryCopy_snd (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    boundaryCopy X x P q ≫ pullback.snd
      (LoopCellSimplicialModel.attaching X x P ≫ LoopCellSphericalGenerators.nativeInclusion X x P)
      (LoopCellPulledSimplicialModel.projection X x P) =
        (LoopCellNativeCoverCopies.boundarySum X x P ≫
          LoopCellNativeCoverCopies.diskFamilyLift X x P) ≫
            nativeDeck X x P q := by
  let p := LoopCellPulledSimplicialModel.projection X x P
  let L : LoopCellNativeCoverCopies.boundaryFamily X x P ⟶
      LoopCellSphericalGenerators.nativeCover X x P :=
          LoopCellNativeCoverCopies.boundarySum X x P ≫
          LoopCellNativeCoverCopies.diskFamilyLift X x P
  let c : (∐ fun _ : FundamentalGroup X x ⧸ P => LoopCellNativeCoverCopies.boundaryFamily X x P) ≅
      pullback (L ≫ p) p := LoopCellNativeCoverCopies.boundaryFamilyCopiesIso X x P
  let e : pullback (L ≫ p) p ≅ LoopCellPulledSimplicialModel.boundaries X x P :=
    pullback.congrHom (boundaryFamilyProjection_eq X x P) rfl
  let i := Sigma.ι (fun _ : FundamentalGroup X x ⧸ P =>
    LoopCellNativeCoverCopies.boundaryFamily X x P) q
  let a := (LoopCellNativeCoverCopies.nativeDeckGroupEquiv X x P).symm q
  let f : LoopCellPulledSimplicialModel.boundaries X x P ⟶
      LoopCellSphericalGenerators.nativeCover X x P :=
          pullback.snd (LoopCellSimplicialModel.attaching X x P ≫
            LoopCellSphericalGenerators.nativeInclusion X x P) p
  let g : pullback (L ≫ p) p ⟶
      LoopCellSphericalGenerators.nativeCover X x P := pullback.snd (L ≫ p) p
  have hE : e.hom ≫ f = g :=
    OriginalQuotientCellPresentation.pullbackCongr_snd p (boundaryFamilyProjection_eq X x P)
  have hC : i ≫ c.hom = SSet.KanComplex.nativeCoverCopyLift L a :=
    LoopCellNativeCoverCopies.boundaryFamilyCopiesIso_ι X x P q
  have h : boundaryCopy X x P q ≫ f = (i ≫ c.hom) ≫ g :=
    OriginalQuotientCellPresentation.transported_projection i c.hom e.hom f g hE
  exact h.trans
    ((congrArg (fun t => t ≫ g) hC).trans (SSet.KanComplex.nativeCoverCopyLift_snd L a))

/-- The entire pulled boundary family enters the SAME labelled disk family. -/
theorem boundaryCopy_toDisks (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    LoopCellNativeCoverCopies.boundarySum X x P ≫ diskCopy X x P q =
      boundaryCopy X x P q ≫ LoopCellPulledSimplicialModel.boundaryToDisks X x P := by
  let b := LoopCellNativeCoverCopies.boundarySum X x P
  let b' := LoopCellSimplicialModel.boundarySum X x P
  let L := LoopCellNativeCoverCopies.diskFamilyLift X x P
  let p := LoopCellPulledSimplicialModel.projection X x P
  let fD := pullback.fst (LoopCellSimplicialModel.diskMates X x P) p
  let fB := pullback.fst
    (LoopCellSimplicialModel.attaching X x P ≫ LoopCellSphericalGenerators.nativeInclusion X x P) p
  let sD := pullback.snd (LoopCellSimplicialModel.diskMates X x P) p
  let sB := pullback.snd
    (LoopCellSimplicialModel.attaching X x P ≫ LoopCellSphericalGenerators.nativeInclusion X x P) p
  let d := diskCopy X x P q
  let e := boundaryCopy X x P q
  let t := LoopCellPulledSimplicialModel.boundaryToDisks X x P
  apply pullback.hom_ext
  · have hL : (b ≫ d) ≫ fD = b :=
      (Category.assoc b d fD).trans
        ((congrArg (fun h => b ≫ h) (diskCopy_fst X x P q)).trans (Category.comp_id b))
    have hR : (e ≫ t) ≫ fD = b' :=
      (Category.assoc e t fD).trans
        ((congrArg (fun h => e ≫ h) (LoopCellPulledSimplicialModel.boundaryToDisks_fst X x P)).trans
          ((Category.assoc e fB b').symm.trans
            ((congrArg (fun h => h ≫ b') (boundaryCopy_fst X x P q)).trans (Category.id_comp b'))))
    exact hL.trans ((boundaryFamilyMap_eq X x P).trans hR.symm)
  · have hL : (b ≫ d) ≫ sD = (b ≫ L) ≫ nativeDeck X x P q :=
      (Category.assoc b d sD).trans
        ((congrArg (fun h => b ≫ h) (diskCopy_snd X x P q)).trans
          (Category.assoc b L (nativeDeck X x P q)).symm)
    have hR : (e ≫ t) ≫ sD = (b ≫ L) ≫ nativeDeck X x P q :=
      (Category.assoc e t sD).trans
        ((congrArg (fun h => e ≫ h) (LoopCellPulledSimplicialModel.boundaryToDisks_snd X x P)).trans
          (boundaryCopy_snd X x P q))
    exact hL.trans hR.symm

/-- The entire original p-disk at the literal quotient label q. -/
def diskCell (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    (Δ[2] : SSet.{u}) ⟶ LoopCellPulledSimplicialModel.disks X x P :=
  Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) i.2 ≫ diskCopy X x P i.1

/-- The entire original p-boundary at the SAME literal quotient label q. -/
def boundaryCell (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    (SSet.boundary.{u} 2).toSSet ⟶ LoopCellPulledSimplicialModel.boundaries X x P :=
  Sigma.ι (fun _ : P => (SSet.boundary.{u} 2).toSSet) i.2 ≫ boundaryCopy X x P i.1

/-- Every whole boundary enters exactly its own original labelled disk. -/
theorem boundaryCell_toDisks (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    boundaryCell X x P i ≫ LoopCellPulledSimplicialModel.boundaryToDisks X x P =
      (SSet.boundary.{u} 2).ι ≫ diskCell X x P i := by
  let b := LoopCellNativeCoverCopies.boundarySum X x P
  let e := boundaryCopy X x P i.1
  let d := diskCopy X x P i.1
  let t := LoopCellPulledSimplicialModel.boundaryToDisks X x P
  let jB := Sigma.ι (fun _ : P => (SSet.boundary.{u} 2).toSSet) i.2
  let jD := Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) i.2
  have hj : jB ≫ b = (SSet.boundary.{u} 2).ι ≫ jD :=
    (congrArg (fun h => jB ≫ h) (LoopCellNativeCoverCopies.boundarySum_eq X x P)).trans
      (Sigma.ι_map (fun _ : P => (SSet.boundary.{u} 2).ι) i.2)
  exact (Category.assoc jB e t).trans
    ((congrArg (fun h => jB ≫ h) (boundaryCopy_toDisks X x P i.1).symm).trans
      ((Category.assoc jB b d).symm.trans
        ((congrArg (fun h => h ≫ d) hj).trans
          (Category.assoc (SSet.boundary.{u} 2).ι jD d))))

/-- The source projection of every original labelled disk remains its actual original summand. -/
theorem diskCell_fst (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    diskCell X x P i ≫ pullback.fst (LoopCellSimplicialModel.diskMates X x P)
      (LoopCellPulledSimplicialModel.projection X x P) =
      Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) i.2 := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) i.2 ≫ h)
      (diskCopy_fst X x P i.1)).trans (Category.comp_id _))

/-- Every labelled disk is the SAME chosen native lift followed by its actual deck
transformation. -/
theorem diskCell_snd (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    diskCell X x P i ≫ pullback.snd (LoopCellSimplicialModel.diskMates X x P)
      (LoopCellPulledSimplicialModel.projection X x P) =
        LoopCellSphericalGenerators.nativeDiskLift X x P i.2 ≫ nativeDeck X x P i.1 := by
  let j := Sigma.ι (fun _ : P => (Δ[2] : SSet.{u})) i.2
  let L := LoopCellNativeCoverCopies.diskFamilyLift X x P
  let D := nativeDeck X x P i.1
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => j ≫ h) (diskCopy_snd X x P i.1)).trans
      ((Category.assoc j L D).symm.trans
        (congrArg (fun h => h ≫ D) (LoopCellNativeCoverCopies.diskFamilyLift_ι X x P i.2))))

/-- Every boundary remains its actual original boundary summand. -/
theorem boundaryCell_fst (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    boundaryCell X x P i ≫ pullback.fst
      (LoopCellSimplicialModel.attaching X x P ≫ LoopCellSphericalGenerators.nativeInclusion X x P)
      (LoopCellPulledSimplicialModel.projection X x P) =
      Sigma.ι (fun _ : P => (SSet.boundary.{u} 2).toSSet) i.2 := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => Sigma.ι (fun _ : P => (SSet.boundary.{u} 2).toSSet) i.2 ≫ h)
      (boundaryCopy_fst X x P i.1)).trans (Category.comp_id _))

/-- The original p-boundary at q is the boundary of the SAME whole chosen disk lift. -/
theorem boundaryCell_snd (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    boundaryCell X x P i ≫ pullback.snd
      (LoopCellSimplicialModel.attaching X x P ≫ LoopCellSphericalGenerators.nativeInclusion X x P)
      (LoopCellPulledSimplicialModel.projection X x P) =
      ((SSet.boundary.{u} 2).ι ≫ LoopCellSphericalGenerators.nativeDiskLift X x P i.2) ≫
        nativeDeck X x P i.1 := by
  let t := LoopCellPulledSimplicialModel.boundaryToDisks X x P
  let p := LoopCellPulledSimplicialModel.projection X x P
  let sD := pullback.snd (LoopCellSimplicialModel.diskMates X x P) p
  have h : boundaryCell X x P i ≫ pullback.snd
      (LoopCellSimplicialModel.attaching X x P ≫
          LoopCellSphericalGenerators.nativeInclusion X x P) p =
        (boundaryCell X x P i ≫ t) ≫ sD :=
    (congrArg (fun h => boundaryCell X x P i ≫ h)
      (LoopCellPulledSimplicialModel.boundaryToDisks_snd X x P).symm).trans
        (Category.assoc _ _ _).symm
  exact h.trans
    ((congrArg (fun h => h ≫ sD) (boundaryCell_toDisks X x P i)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun h => (SSet.boundary.{u} 2).ι ≫ h) (diskCell_snd X x P i)).trans
          (Category.assoc _ _ _).symm)))

/-- The whole old-cover attaching map of the original labelled boundary. -/
def liftedAttachingCell (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    (SSet.boundary.{u} 2).toSSet ⟶ LoopCellSphericalGenerators.nativePullback X x P :=
  boundaryCell X x P i ≫ LoopCellPulledSimplicialModel.attaching X x P

/-- Its source projection is exactly the original matched attaching-map adjoint. -/
theorem liftedAttachingCell_source (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    liftedAttachingCell X x P i ≫ LoopCellSphericalGenerators.nativePullbackProjection X x P =
      sSetTopAdj.homEquiv (SSet.boundary.{u} 2).toSSet X
        ((LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).hom.left ≫
          LoopCellAttachment.attachingMap X x P i.2) := by
  let fB := pullback.fst
    (LoopCellSimplicialModel.attaching X x P ≫ LoopCellSphericalGenerators.nativeInclusion X x P)
    (LoopCellPulledSimplicialModel.projection X x P)
  have hArrow : LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2 =
      SSet.boundary.toClassicalCellDiskArrowIso.{u} 2 :=
    LoopCellSphericalGenerators.diskBoundaryArrowIso_eq 2
  have hCharacteristic :
      sSetTopAdj.homEquiv (SSet.boundary.{u} 2).toSSet X
          ((LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).hom.left ≫
            LoopCellAttachment.attachingMap X x P i.2) =
        sSetTopAdj.homEquiv (SSet.boundary.{u} 2).toSSet X
          ((SSet.boundary.toClassicalCellDiskArrowIso.{u} 2).hom.left ≫
            LoopCellAttachment.attachingMap X x P i.2) :=
    congrArg (fun e : Arrow.mk (SSet.toTop.map (SSet.boundary.{u} 2).ι) ≅
        Arrow.mk (classicalCellDiskPair.{u} 2).map =>
      sSetTopAdj.homEquiv (SSet.boundary.{u} 2).toSSet X
        (e.hom.left ≫ LoopCellAttachment.attachingMap X x P i.2)) hArrow
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => boundaryCell X x P i ≫ h)
      (LoopCellPulledSimplicialModel.attaching_fst X x P)).trans
      ((Category.assoc (boundaryCell X x P i) fB
          (LoopCellSimplicialModel.attaching X x P)).symm.trans
        ((congrArg (fun h => h ≫ LoopCellSimplicialModel.attaching X x P)
          (boundaryCell_fst X x P i)).trans
            ((LoopCellSimplicialModel.attaching_ι X x P i.2).trans hCharacteristic.symm))))

/-- The actual old-cover attaching map has the SAME translated native disk boundary coordinate. -/
theorem liftedAttachingCell_toCover (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    liftedAttachingCell X x P i ≫ LoopCellSphericalGenerators.nativePullbackToCover X x P =
      ((SSet.boundary.{u} 2).ι ≫ LoopCellSphericalGenerators.nativeDiskLift X x P i.2) ≫
        nativeDeck X x P i.1 := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => boundaryCell X x P i ≫ h)
      (LoopCellPulledSimplicialModel.attaching_snd X x P)).trans
        (boundaryCell_snd X x P i))

/-- All original labelled disks form the complete actual pulled disk cofan. -/
def disksCofan (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    Cofan (fun _ : labels X x P => (Δ[2] : SSet.{u})) :=
  Cofan.mk (LoopCellPulledSimplicialModel.disks X x P) (diskCell X x P)

/-- The complete copy classification proves the entire disk cofan universal. -/
def disksCofanIsColimit (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] : IsColimit (disksCofan X x P) := by
  let K := LoopCellNativeCoverCopies.diskFamily X x P
  let c : Cofan (fun _ : FundamentalGroup X x ⧸ P => K) :=
    Cofan.mk (LoopCellPulledSimplicialModel.disks X x P) (diskCopy X x P)
  have hc : IsColimit c := IsColimit.ofIsoColimit
    (coproductIsCoproduct (fun _ : FundamentalGroup X x ⧸ P => K))
    (Cocone.ext (disksIso X x P) (by rintro ⟨q⟩; rfl))
  exact Cofan.IsColimit.prod
    (fun _ : FundamentalGroup X x ⧸ P => Cofan.mk K (Sigma.ι (fun _ : P => (Δ[2] : SSet.{u}))))
    (fun _ => coproductIsCoproduct (fun _ : P => (Δ[2] : SSet.{u}))) c hc

/-- All original labelled boundaries form the complete actual pulled boundary cofan. -/
def boundariesCofan (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    Cofan (fun _ : labels X x P => (SSet.boundary.{u} 2).toSSet) :=
  Cofan.mk (LoopCellPulledSimplicialModel.boundaries X x P) (boundaryCell X x P)

/-- The SAME complete copy classification proves the boundary cofan universal. -/
def boundariesCofanIsColimit (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] : IsColimit (boundariesCofan X x P) := by
  let K := LoopCellNativeCoverCopies.boundaryFamily X x P
  let c : Cofan (fun _ : FundamentalGroup X x ⧸ P => K) :=
    Cofan.mk (LoopCellPulledSimplicialModel.boundaries X x P) (boundaryCopy X x P)
  have hc : IsColimit c := IsColimit.ofIsoColimit
    (coproductIsCoproduct (fun _ : FundamentalGroup X x ⧸ P => K))
    (Cocone.ext (boundariesIso X x P) (by rintro ⟨q⟩; rfl))
  exact Cofan.IsColimit.prod
    (fun _ : FundamentalGroup X x ⧸ P =>
      Cofan.mk K (Sigma.ι (fun _ : P => (SSet.boundary.{u} 2).toSSet)))
    (fun _ => coproductIsCoproduct (fun _ : P => (SSet.boundary.{u} 2).toSSet)) c hc

/-- Realization of the complete disk cofan uses the original labelled disk maps. -/
def realizedDisksCofan (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    Cofan (fun _ : labels X x P => SSet.toTop.obj (Δ[2] : SSet.{u})) :=
  Cofan.mk (SSet.toTop.obj (LoopCellPulledSimplicialModel.disks X x P))
    (fun i => SSet.toTop.map (diskCell X x P i))

/-- The actual realization functor preserves that entire disk coproduct. -/
def realizedDisksCofanIsColimit (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    IsColimit (realizedDisksCofan X x P) :=
  isColimitCofanMkObjOfIsColimit SSet.toTop
    (fun _ : labels X x P => (Δ[2] : SSet.{u})) (diskCell X x P)
    (disksCofanIsColimit X x P)

/-- Realization of the complete boundary cofan uses its SAME labelled restrictions. -/
def realizedBoundariesCofan (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    Cofan (fun _ : labels X x P => SSet.toTop.obj (SSet.boundary.{u} 2).toSSet) :=
  Cofan.mk (SSet.toTop.obj (LoopCellPulledSimplicialModel.boundaries X x P))
    (fun i => SSet.toTop.map (boundaryCell X x P i))

/-- The actual realization functor preserves that entire boundary coproduct. -/
def realizedBoundariesCofanIsColimit (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    IsColimit (realizedBoundariesCofan X x P) :=
  isColimitCofanMkObjOfIsColimit SSet.toTop
    (fun _ : labels X x P => (SSet.boundary.{u} 2).toSSet) (boundaryCell X x P)
    (boundariesCofanIsColimit X x P)

/-- The matched classical disk cofan retains the SAME realized chosen lifts. -/
def classicalDisksCofan (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    Cofan (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).fst) :=
  Cofan.mk (SSet.toTop.obj (LoopCellPulledSimplicialModel.disks X x P))
    (fun i => (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.right ≫
      SSet.toTop.map (diskCell X x P i))

/-- The existing discrete-diagram Iso transports the entire realized cofan through the matched
disks. -/
def classicalDisksCofanIsColimit (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    IsColimit (classicalDisksCofan X x P) := by
  let α : Discrete.functor (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).fst) ≅
      Discrete.functor (fun _ : labels X x P => SSet.toTop.obj (Δ[2] : SSet.{u})) :=
    Discrete.natIso (fun _ =>
      (Arrow.rightFunc.mapIso (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2)).symm)
  exact (IsColimit.precomposeHomEquiv α (realizedDisksCofan X x P)).symm
    (realizedDisksCofanIsColimit X x P)

/-- The matched classical boundary cofan retains the SAME realized native boundary restrictions. -/
def classicalBoundariesCofan (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    Cofan (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).snd) :=
  Cofan.mk (SSet.toTop.obj (LoopCellPulledSimplicialModel.boundaries X x P))
    (fun i => (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.left ≫
      SSet.toTop.map (boundaryCell X x P i))

/-- The SAME matched arrow Iso transports the entire boundary cofan. -/
def classicalBoundariesCofanIsColimit (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    IsColimit (classicalBoundariesCofan X x P) := by
  let α : Discrete.functor (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).snd) ≅
      Discrete.functor (fun _ : labels X x P => SSet.toTop.obj (SSet.boundary.{u} 2).toSSet) :=
    Discrete.natIso (fun _ =>
      (Arrow.leftFunc.mapIso (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2)).symm)
  exact (IsColimit.precomposeHomEquiv α (realizedBoundariesCofan X x P)).symm
    (realizedBoundariesCofanIsColimit X x P)

/-- The full literal classical disk coproduct is the realized ACTUAL pulled disk family. -/
def classicalDisksIso (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    CellFamilyAttachment.disks (labels X x P) 1 ≅
      SSet.toTop.obj (LoopCellPulledSimplicialModel.disks X x P) :=
  IsColimit.coconePointUniqueUpToIso
    (TopCat.sigmaCofanIsColimit.{u, u}
      (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).fst))
    (classicalDisksCofanIsColimit X x P)

/-- Every classical disk component is its SAME chosen labelled whole native disk. -/
theorem classicalDisksIso_ι (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    TopCat.sigmaι (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).fst) i ≫
        (classicalDisksIso X x P).hom =
      (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.right ≫
        SSet.toTop.map (diskCell X x P i) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (TopCat.sigmaCofanIsColimit.{u, u}
      (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).fst))
    (classicalDisksCofanIsColimit X x P) ⟨i⟩

/-- The full literal classical boundary coproduct is the realized ACTUAL pulled boundary family. -/
def classicalBoundariesIso (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    CellFamilyAttachment.boundaries (labels X x P) 1 ≅
      SSet.toTop.obj (LoopCellPulledSimplicialModel.boundaries X x P) :=
  IsColimit.coconePointUniqueUpToIso
    (TopCat.sigmaCofanIsColimit.{u, u}
      (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).snd))
    (classicalBoundariesCofanIsColimit X x P)

/-- Every classical boundary component is the SAME selected translated boundary. -/
theorem classicalBoundariesIso_ι (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    TopCat.sigmaι (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).snd) i ≫
        (classicalBoundariesIso X x P).hom =
      (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.left ≫
        SSet.toTop.map (boundaryCell X x P i) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (TopCat.sigmaCofanIsColimit.{u, u}
      (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).snd))
    (classicalBoundariesCofanIsColimit X x P) ⟨i⟩

/-- The SAME matched arrow Iso carries the complete literal classical boundary map to the pulled
map. -/
theorem classicalBoundaryDisk_comm (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    (classicalBoundariesIso X x P).hom ≫
        SSet.toTop.map (LoopCellPulledSimplicialModel.boundaryToDisks X x P) =
      CellFamilyAttachment.boundaryToDisks (labels X x P) 1 ≫
        (classicalDisksIso X x P).hom := by
  apply (TopCat.sigmaCofanIsColimit.{u, u}
    (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).snd)).hom_ext
  rintro ⟨i⟩
  let jB := TopCat.sigmaι (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).snd) i
  let jD := TopCat.sigmaι (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).fst) i
  let eB := (classicalBoundariesIso X x P).hom
  let eD := (classicalDisksIso X x P).hom
  let B := (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.left
  let D := (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.right
  let δ := (SSet.boundary.{u} 2).ι
  let d := (classicalCellDiskPair.{u} 2).map
  let b := boundaryCell X x P i
  let c := diskCell X x P i
  let t := LoopCellPulledSimplicialModel.boundaryToDisks X x P
  let F := SSet.toTop
  have hReal : F.map b ≫ F.map t = F.map δ ≫ F.map c :=
    (F.map_comp b t).symm.trans
      ((congrArg F.map (boundaryCell_toDisks X x P i)).trans (F.map_comp δ c))
  have hArrow : B ≫ F.map δ = d ≫ D :=
    Arrow.w (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv
  have hL : jB ≫ (eB ≫ F.map t) = d ≫ (D ≫ F.map c) :=
    (Category.assoc jB eB (F.map t)).symm.trans
      ((congrArg (fun h => h ≫ F.map t) (classicalBoundariesIso_ι X x P i)).trans
        ((Category.assoc B (F.map b) (F.map t)).trans
          ((congrArg (fun h => B ≫ h) hReal).trans
            ((Category.assoc B (F.map δ) (F.map c)).symm.trans
              ((congrArg (fun h => h ≫ F.map c) hArrow).trans
                (Category.assoc d D (F.map c)))))))
  have hR : jB ≫ (CellFamilyAttachment.boundaryToDisks (labels X x P) 1 ≫ eD) =
      d ≫ (D ≫ F.map c) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun h => h ≫ eD)
        (CellFamilyAttachment.boundaryι_boundaryToDisks (ι := labels X x P) 1 i)).trans
          ((Category.assoc d jD eD).trans
            (congrArg (fun h => d ≫ h) (classicalDisksIso_ι X x P i))))
  exact hL.trans hR.symm

/-- The classical attaching map for each ACTUAL quotient-labelled original lifted boundary. -/
def attachingCell (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    (classicalCellDiskPair.{u} 2).snd ⟶
      SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P) :=
  (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.left ≫
    SSet.toTop.map (liftedAttachingCell X x P i)

/-- The full original labelled attaching family agrees with the actual pulled boundary map. -/
theorem classicalAttaching_comm (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    (classicalBoundariesIso X x P).hom ≫
        SSet.toTop.map (LoopCellPulledSimplicialModel.attaching X x P) =
      CellFamilyAttachment.attachingMap
        (SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)) 1
          (attachingCell X x P) := by
  apply (TopCat.sigmaCofanIsColimit.{u, u}
    (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).snd)).hom_ext
  rintro ⟨i⟩
  let j := TopCat.sigmaι (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).snd) i
  let B := (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.left
  let b := boundaryCell X x P i
  let t := LoopCellPulledSimplicialModel.attaching X x P
  have hL : j ≫ ((classicalBoundariesIso X x P).hom ≫ SSet.toTop.map t) =
      attachingCell X x P i :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun h => h ≫ SSet.toTop.map t) (classicalBoundariesIso_ι X x P i)).trans
        ((Category.assoc B (SSet.toTop.map b) (SSet.toTop.map t)).trans
          (congrArg (fun h => B ≫ h) (SSet.toTop.map_comp b t).symm)))
  have hR : j ≫ CellFamilyAttachment.attachingMap
      (SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)) 1
        (attachingCell X x P) = attachingCell X x P i :=
    CellFamilyAttachment.boundaryι_desc 1 (attachingCell X x P) i
  exact hL.trans hR.symm

/-- The ENTIRE actual pulled realization is the classical two-cell attachment at EVERY quotient
label. -/
theorem classicalIsPushout (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    IsPushout
      (CellFamilyAttachment.boundaryToDisks (labels X x P) 1)
      (CellFamilyAttachment.attachingMap
        (SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)) 1 (attachingCell X x P))
      ((classicalDisksIso X x P).hom ≫
        SSet.toTop.map (LoopCellPulledSimplicialModel.diskInclusion X x P))
      (SSet.toTop.map (LoopCellPulledSimplicialModel.oldInclusion X x P)) := by
  have h := (LoopCellPulledSimplicialModel.isPushout X x P).map SSet.toTop
  exact h.of_iso' (classicalBoundariesIso X x P) (classicalDisksIso X x P)
    (Iso.refl _) (Iso.refl _)
    (classicalBoundaryDisk_comm X x P)
    (by simpa only [Iso.refl_hom, Category.comp_id] using classicalAttaching_comm X x P)
    (by simp only [Iso.refl_hom, Category.comp_id])
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])

/-- The actual classical attachment on the SAME original old cover. -/
abbrev classicalSpace (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] : TopCat.{u} :=
  CellFamilyAttachment.space
    (SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)) 1 (attachingCell X x P)

/-- Its canonical pushout Iso is the ENTIRE actual pulled realization, not a supplied model. -/
def classicalSpaceIso (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    classicalSpace X x P ≅ SSet.toTop.obj (LoopCellPulledSimplicialModel.space X x P) :=
  (classicalIsPushout X x P).isoPushout.symm

/-- The whole old cover is retained by the actual pushout Iso. -/
theorem classicalSpaceIso_old (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    CellFamilyAttachment.inclusion
        (SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)) 1
            (attachingCell X x P) ≫
      (classicalSpaceIso X x P).hom =
        SSet.toTop.map (LoopCellPulledSimplicialModel.oldInclusion X x P) :=
  (classicalIsPushout X x P).inr_isoPushout_inv

/-- Every original whole closed disk is retained at its literal quotient label by the actual Iso. -/
theorem classicalSpaceIso_disk (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    CellFamilyAttachment.cell
        (SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)) 1
            (attachingCell X x P) i ≫
      (classicalSpaceIso X x P).hom =
        (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.right ≫
          SSet.toTop.map (diskCell X x P i) ≫
            SSet.toTop.map (LoopCellPulledSimplicialModel.diskInclusion X x P) := by
  let j := TopCat.sigmaι (fun _ : labels X x P => (classicalCellDiskPair.{u} 2).fst) i
  let t := CellFamilyAttachment.diskInclusion
    (SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)) 1 (attachingCell X x P)
  let e := classicalSpaceIso X x P
  let D := (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.right
  let c := SSet.toTop.map (diskCell X x P i)
  let m := SSet.toTop.map (LoopCellPulledSimplicialModel.diskInclusion X x P)
  exact (Category.assoc j t e.hom).trans
    ((congrArg (fun h => j ≫ h) (classicalIsPushout X x P).inl_isoPushout_inv).trans
      ((Category.assoc j (classicalDisksIso X x P).hom m).symm.trans
        ((congrArg (fun h => h ≫ m) (classicalDisksIso_ι X x P i)).trans
          (Category.assoc D c m))))

/-- The old inclusion in the actual pulled realization is closed, by the existing realized-mono
theorem. -/
theorem realizedOldInclusion_isClosedEmbedding (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    Topology.IsClosedEmbedding
      (SSet.toTop.map (LoopCellPulledSimplicialModel.oldInclusion X x P)) := by
  let : Mono (LoopCellPulledSimplicialModel.oldInclusion X x P) :=
    LoopCellPulledSimplicialModel.oldInclusion_mono X x P
  exact TopCat.closedT1Embeddings_le_isClosedEmbedding _
    (SSet.closedT1Embeddings_toTop_map_of_mono _)

/-- The literal realized pair, with its original old-cover inclusion. -/
abbrev realizedPair (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : TopPair.{u} :=
  TopPair.of (SSet.toTop.map (LoopCellPulledSimplicialModel.oldInclusion X x P))
    (realizedOldInclusion_isClosedEmbedding X x P).isEmbedding

/-- The actual classical attachment pair on the SAME old cover. -/
abbrev classicalPair (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] : TopPair.{u} :=
  CellCollarDeformation.attachmentPair
    (SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)) 1 (attachingCell X x P)

/-- The genuine pair Iso is identity on the entire old cover and the actual pushout Iso on top. -/
def classicalPairIso (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    classicalPair X x P ≅ realizedPair X x P := by
  let E := SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)
  let e := classicalSpaceIso X x P
  let f := CellFamilyAttachment.inclusion E 1 (attachingCell X x P)
  let g := SSet.toTop.map (LoopCellPulledSimplicialModel.oldInclusion X x P)
  have h : f ≫ e.hom = g := classicalSpaceIso_old X x P
  exact MorphismProperty.Arrow.isoMk (Iso.refl E) e (by
    change (𝟙 E) ≫ g = f ≫ e.hom
    exact (Category.id_comp g).trans h.symm)

/-- The complete coefficient coproduct basis of the ACTUAL pulled realization, at EVERY (q,p). -/
def relativeCoefficientBasisIso (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (R : AddCommGrpCat.{u}) :
    (∐ fun _ : labels X x P => R) ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).obj (realizedPair X x P) :=
  CellFamilyAttachment.attachmentRelativeDiagonalIso
      (SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)) 1
          (attachingCell X x P) R ≪≫
    (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).mapIso (classicalPairIso X x P)

/-- The whole classical disk-pair map of the actual labelled cell in the realized pulled pair. -/
def cellPair (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    classicalCellDiskPair.{u} 2 ⟶ realizedPair X x P :=
  CellFamilyAttachment.cellPairMap
      (SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)) 1
          (attachingCell X x P) i ≫
    (classicalPairIso X x P).hom

/-- The basis is calibrated by the original matched WHOLE closed-disk pair map at each label. -/
theorem relativeCoefficientBasisIso_ι (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (R : AddCommGrpCat.{u}) (i : labels X x P) :
    Sigma.ι (fun _ : labels X x P => R) i ≫ (relativeCoefficientBasisIso X x P R).hom =
      (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u, u} R 2).hom ≫
        (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).map (cellPair X x P i) := by
  let H : TopPair.{u} ⥤ AddCommGrpCat.{u} := relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2
  let E := SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)
  let a := attachingCell X x P
  let e := classicalPairIso X x P
  let g := (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u, u} R 2).hom
  let c := CellFamilyAttachment.cellPairMap E 1 a i
  have h := CellFamilyAttachment.attachmentRelativeCellHom_eq_diskPair E 1 a R i
  have hι : Sigma.ι (fun _ : labels X x P => R) i ≫
      (CellFamilyAttachment.attachmentRelativeDiagonalIso E 1 a R).hom = g ≫ H.map c :=
    (CellFamilyAttachment.coefficient_ι_comp_attachmentRelativeDiagonalIso_hom E 1 a R i).trans h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ H.map e.hom) hι).trans
      ((Category.assoc g (H.map c) (H.map e.hom)).trans
        (congrArg (fun t => g ≫ t) (H.map_comp c e.hom).symm)))

/-- The actual inverse recovers EVERY original coefficient summand. -/
theorem relativeCoefficientBasisIso_inverse_ι (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (R : AddCommGrpCat.{u}) (i : labels X x P) :
    ((classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u, u} R 2).hom ≫
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).map (cellPair X x P i)) ≫
        (relativeCoefficientBasisIso X x P R).inv = Sigma.ι (fun _ : labels X x P => R) i := by
  let e := relativeCoefficientBasisIso X x P R
  let j := Sigma.ι (fun _ : labels X x P => R) i
  exact (congrArg (fun t => t ≫ e.inv) (relativeCoefficientBasisIso_ι X x P R i).symm).trans
    ((Category.assoc j e.hom e.inv).trans
      ((congrArg (fun t => j ≫ t) e.hom_inv_id).trans (Category.comp_id j)))

/-- The ambient component of the actual pair Iso is the SAME canonical pushout Iso. -/
theorem classicalPairIso_fst (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    TopPair.Hom.fst (classicalPairIso X x P).hom = (classicalSpaceIso X x P).hom := by
  rfl

/-- The actual pair Iso fixes the entire old cover. -/
theorem classicalPairIso_snd (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    TopPair.Hom.snd (classicalPairIso X x P).hom =
      𝟙 (SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)) := by
  rfl

/-- Every actual whole closed disk is retained by the characteristic pair map. -/
theorem cellPair_fst (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    TopPair.Hom.fst (cellPair X x P i) =
      (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.right ≫
        SSet.toTop.map (diskCell X x P i) ≫
          SSet.toTop.map (LoopCellPulledSimplicialModel.diskInclusion X x P) := by
  let F : TopPair.{u} ⥤ TopCat.{u} := TopPair.proj₁
  let E := SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)
  let a := attachingCell X x P
  let c := CellFamilyAttachment.cellPairMap E 1 a i
  let e := classicalPairIso X x P
  have hC : F.map c = CellFamilyAttachment.cell E 1 a i :=
    CellFamilyAttachment.cellPairMap_fst E 1 a i
  have hE : F.map e.hom = (classicalSpaceIso X x P).hom := classicalPairIso_fst X x P
  exact (F.map_comp c e.hom).trans
    ((congrArg (fun h => h ≫ F.map e.hom) hC).trans
      ((congrArg (fun h => CellFamilyAttachment.cell E 1 a i ≫ h) hE).trans
        (classicalSpaceIso_disk X x P i)))

/-- Every characteristic pair retains its original chosen labelled attaching map. -/
theorem cellPair_snd (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    TopPair.Hom.snd (cellPair X x P i) = attachingCell X x P i := by
  let F : TopPair.{u} ⥤ TopCat.{u} := TopPair.proj₂
  let E := SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)
  let a := attachingCell X x P
  let c := CellFamilyAttachment.cellPairMap E 1 a i
  let e := classicalPairIso X x P
  have hC : F.map c = a i := CellFamilyAttachment.cellPairMap_snd E 1 a i
  have hE : F.map e.hom = 𝟙 E := classicalPairIso_snd X x P
  exact (F.map_comp c e.hom).trans
    ((congrArg (fun h => h ≫ F.map e.hom) hC).trans
      ((congrArg (fun h => a i ≫ h) hE).trans (Category.comp_id (a i))))

/-- The actual pair comparison to the SAME original realized native cover. -/
def realizedPairToCover (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    realizedPair X x P ⟶ LoopCellSphericalGenerators.liftedPair X x P := by
  let E := SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)
  let m := LoopCellPulledSimplicialModel.oldInclusion X x P
  let c := LoopCellPulledSimplicialModel.toCover X x P
  let i := LoopCellSphericalGenerators.nativePullbackToCover X x P
  have h : SSet.toTop.map m ≫ SSet.toTop.map c = SSet.toTop.map i :=
    (SSet.toTop.map_comp m c).symm.trans
      (congrArg SSet.toTop.map (LoopCellPulledSimplicialModel.oldInclusion_toCover X x P))
  exact TopPair.ofHom (SSet.toTop.map c) (𝟙 E)
    ((Category.id_comp (SSet.toTop.map i)).trans h.symm)

/-- The comparison uses the SAME pulled second projection on the entire ambient space. -/
theorem realizedPairToCover_fst (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    TopPair.Hom.fst (realizedPairToCover X x P) =
      SSet.toTop.map (LoopCellPulledSimplicialModel.toCover X x P) := by
  rfl

/-- It fixes the entire original old cover. -/
theorem realizedPairToCover_snd (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    TopPair.Hom.snd (realizedPairToCover X x P) =
      𝟙 (SSet.toTop.obj (LoopCellSphericalGenerators.nativePullback X x P)) := by
  rfl

/-- The actual labelled characteristic pair, carried into the SAME original native cover. -/
def cellPairToCover (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    classicalCellDiskPair.{u} 2 ⟶ LoopCellSphericalGenerators.liftedPair X x P :=
  cellPair X x P i ≫ realizedPairToCover X x P

/-- Every whole translated characteristic disk uses the SAME native lift and quotient deck map. -/
theorem cellPairToCover_fst (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    TopPair.Hom.fst (cellPairToCover X x P i) =
      (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.right ≫
        SSet.toTop.map (LoopCellSphericalGenerators.nativeDiskLift X x P i.2 ≫
          nativeDeck X x P i.1) := by
  let G : TopPair.{u} ⥤ TopCat.{u} := TopPair.proj₁
  let F := SSet.toTop
  let c := diskCell X x P i
  let m := LoopCellPulledSimplicialModel.diskInclusion X x P
  let f := LoopCellPulledSimplicialModel.toCover X x P
  let D := (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.right
  have hWhole : c ≫ m ≫ f =
      LoopCellSphericalGenerators.nativeDiskLift X x P i.2 ≫ nativeDeck X x P i.1 :=
    (congrArg (fun h => c ≫ h) (LoopCellPulledSimplicialModel.diskInclusion_toCover X x P)).trans
      (diskCell_snd X x P i)
  have hMap : F.map c ≫ F.map m ≫ F.map f =
      F.map (LoopCellSphericalGenerators.nativeDiskLift X x P i.2 ≫ nativeDeck X x P i.1) :=
    (congrArg (fun h => F.map c ≫ h) (F.map_comp m f).symm).trans
      ((F.map_comp c (m ≫ f)).symm.trans (congrArg F.map hWhole))
  have hAssoc : (D ≫ F.map c ≫ F.map m) ≫ F.map f =
      D ≫ (F.map c ≫ F.map m ≫ F.map f) := by
    simp only [Category.assoc]
  have hC := cellPair_fst X x P i
  have hF := realizedPairToCover_fst X x P
  exact (G.map_comp (cellPair X x P i) (realizedPairToCover X x P)).trans
    ((congrArg (fun h => h ≫ G.map (realizedPairToCover X x P)) hC).trans
      ((congrArg (fun h => (D ≫ F.map c ≫ F.map m) ≫ h) hF).trans
        (hAssoc.trans (congrArg (fun h => D ≫ h) hMap))))

/-- Its old-cover boundary is the SAME original translated attaching map. -/
theorem cellPairToCover_snd (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    TopPair.Hom.snd (cellPairToCover X x P i) = attachingCell X x P i := by
  let F : TopPair.{u} ⥤ TopCat.{u} := TopPair.proj₂
  exact (F.map_comp (cellPair X x P i) (realizedPairToCover X x P)).trans
    ((congrArg (fun h => h ≫ F.map (realizedPairToCover X x P)) (cellPair_snd X x P i)).trans
      ((congrArg (fun h => attachingCell X x P i ≫ h) (realizedPairToCover_snd X x P)).trans
        (Category.comp_id (attachingCell X x P i))))

/-- The unit-labelled boundary is the original chosen native boundary, regardless of its first-path
shift. -/
theorem liftedAttachingCell_unit (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (p : P) :
    liftedAttachingCell X x P (1, p) = LoopCellSphericalGenerators.nativeBoundaryLift X x P p := by
  apply pullback.hom_ext
  · exact (liftedAttachingCell_source X x P (1, p)).trans
      (LoopCellSphericalGenerators.nativeBoundaryLift_source X x P p).symm
  · have h : ((SSet.boundary.{u} 2).ι ≫ LoopCellSphericalGenerators.nativeDiskLift X x P p) ≫
        nativeDeck X x P 1 =
        (SSet.boundary.{u} 2).ι ≫ LoopCellSphericalGenerators.nativeDiskLift X x P p :=
      (congrArg (fun h => ((SSet.boundary.{u} 2).ι ≫
        LoopCellSphericalGenerators.nativeDiskLift X x P p) ≫ h) (nativeDeck_one X x P)).trans
          (Category.comp_id _)
    exact (liftedAttachingCell_toCover X x P (1, p)).trans
      (h.trans (LoopCellSphericalGenerators.nativeBoundaryLift_toCover X x P p).symm)

/-- The unit characteristic pair is EXACTLY the original chosen lifted disk pair, not a normalized
replacement. -/
theorem cellPairToCover_unit (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (p : P) :
    cellPairToCover X x P (1,
        p) = LoopCellSphericalGenerators.liftedCharacteristicDiskPair X x P p := by
  apply MorphismProperty.Arrow.Hom.ext
  · have hA : attachingCell X x P (1, p) =
        (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.left ≫
          SSet.toTop.map (LoopCellSphericalGenerators.nativeBoundaryLift X x P p) :=
      congrArg (fun h => (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.left ≫
        SSet.toTop.map h) (liftedAttachingCell_unit X x P p)
    exact (cellPairToCover_snd X x P (1, p)).trans
      (hA.trans (LoopCellSphericalGenerators.liftedCharacteristicDiskPair_snd X x P p).symm)
  · have hD : LoopCellSphericalGenerators.nativeDiskLift X x P p ≫ nativeDeck X x P 1 =
        LoopCellSphericalGenerators.nativeDiskLift X x P p :=
      (congrArg (fun h => LoopCellSphericalGenerators.nativeDiskLift X x P p ≫ h)
        (nativeDeck_one X x P)).trans (Category.comp_id _)
    exact (cellPairToCover_fst X x P (1, p)).trans
      ((congrArg (fun h => (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.right ≫
        SSet.toTop.map h) hD).trans
          (LoopCellSphericalGenerators.liftedCharacteristicDiskPair_fst X x P p).symm)

/-- The ACTUAL deck action on the old native pullback, over the same original singular source. -/
def oldDeck (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    LoopCellSphericalGenerators.nativePullback X x P ⟶
      LoopCellSphericalGenerators.nativePullback X x P :=
  pullback.lift (LoopCellSphericalGenerators.nativePullbackProjection X x P)
    (LoopCellSphericalGenerators.nativePullbackToCover X x P ≫ nativeDeck X x P q) (by
      let f := LoopCellSphericalGenerators.nativeInclusion X x P
      let p := LoopCellPulledSimplicialModel.projection X x P
      let a := LoopCellSphericalGenerators.nativePullbackProjection X x P
      let b := LoopCellSphericalGenerators.nativePullbackToCover X x P
      exact (pullback.condition (f := f) (g := p)).trans
        ((congrArg (fun h => b ≫ h) (nativeDeck_projection X x P q).symm).trans
          (Category.assoc b (nativeDeck X x P q) p).symm))

/-- The deck action retains the original old-space projection. -/
theorem oldDeck_source (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    oldDeck X x P q ≫ LoopCellSphericalGenerators.nativePullbackProjection X x P =
      LoopCellSphericalGenerators.nativePullbackProjection X x P := by
  exact pullback.lift_fst _ _ _

/-- The old-cover action has the SAME native deck coordinate. -/
theorem oldDeck_toCover (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    oldDeck X x P q ≫ LoopCellSphericalGenerators.nativePullbackToCover X x P =
      LoopCellSphericalGenerators.nativePullbackToCover X x P ≫ nativeDeck X x P q := by
  exact pullback.lift_snd _ _ _

/-- The old-cover unit action is the actual identity. -/
theorem oldDeck_one (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    oldDeck X x P 1 = 𝟙 (LoopCellSphericalGenerators.nativePullback X x P) := by
  apply pullback.hom_ext
  · exact (oldDeck_source X x P 1).trans (Category.id_comp _).symm
  · exact (oldDeck_toCover X x P 1).trans
      ((congrArg (fun h => LoopCellSphericalGenerators.nativePullbackToCover X x P ≫ h)
        (nativeDeck_one X x P)).trans
          ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- The noncommutative old-cover deck law uses LEFT label multiplication. -/
theorem oldDeck_mul (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q r : FundamentalGroup X x ⧸ P) :
    oldDeck X x P (q * r) = oldDeck X x P r ≫ oldDeck X x P q := by
  let f := LoopCellSphericalGenerators.nativePullbackProjection X x P
  let g := LoopCellSphericalGenerators.nativePullbackToCover X x P
  let d := oldDeck X x P r
  let e := oldDeck X x P q
  apply pullback.hom_ext
  · have h : (d ≫ e) ≫ f = f :=
      (Category.assoc d e f).trans
        ((congrArg (fun h => d ≫ h) (oldDeck_source X x P q)).trans (oldDeck_source X x P r))
    exact (oldDeck_source X x P (q * r)).trans h.symm
  · have hL : oldDeck X x P (q * r) ≫ g = g ≫ (nativeDeck X x P r ≫ nativeDeck X x P q) :=
      (oldDeck_toCover X x P (q * r)).trans
        (congrArg (fun h => g ≫ h) (nativeDeck_mul X x P q r))
    have hR : (d ≫ e) ≫ g = g ≫ (nativeDeck X x P r ≫ nativeDeck X x P q) :=
      (Category.assoc d e g).trans
        ((congrArg (fun h => d ≫ h) (oldDeck_toCover X x P q)).trans
          ((Category.assoc d g (nativeDeck X x P q)).symm.trans
            ((congrArg (fun h => h ≫ nativeDeck X x P q) (oldDeck_toCover X x P r)).trans
              (Category.assoc g (nativeDeck X x P r) (nativeDeck X x P q)))))
    exact hL.trans hR.symm

/-- Every boundary is the SAME chosen native boundary followed by its actual old-cover deck map. -/
theorem liftedAttachingCell_eq_deck (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    liftedAttachingCell X x P i =
      LoopCellSphericalGenerators.nativeBoundaryLift X x P i.2 ≫ oldDeck X x P i.1 := by
  let B := LoopCellSphericalGenerators.nativeBoundaryLift X x P i.2
  let f := LoopCellSphericalGenerators.nativePullbackProjection X x P
  let g := LoopCellSphericalGenerators.nativePullbackToCover X x P
  let d := oldDeck X x P i.1
  apply pullback.hom_ext
  · have h : (B ≫ d) ≫ f = B ≫ f :=
      (Category.assoc B d f).trans (congrArg (fun h => B ≫ h) (oldDeck_source X x P i.1))
    exact (liftedAttachingCell_source X x P i).trans
      ((LoopCellSphericalGenerators.nativeBoundaryLift_source X x P i.2).symm.trans h.symm)
  · have h : (B ≫ d) ≫ g =
        ((SSet.boundary.{u} 2).ι ≫ LoopCellSphericalGenerators.nativeDiskLift X x P i.2) ≫
          nativeDeck X x P i.1 :=
      (Category.assoc B d g).trans
        ((congrArg (fun h => B ≫ h) (oldDeck_toCover X x P i.1)).trans
          ((Category.assoc B g (nativeDeck X x P i.1)).symm.trans
            (congrArg (fun h => h ≫ nativeDeck X x P i.1)
              (LoopCellSphericalGenerators.nativeBoundaryLift_toCover X x P i.2))))
    exact (liftedAttachingCell_toCover X x P i).trans h.symm

/-- The original labelled attaching maps retain the actual noncommutative deck composition. -/
theorem liftedAttachingCell_deck (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q r : FundamentalGroup X x ⧸ P) (p : P) :
    liftedAttachingCell X x P (q * r, p) =
      liftedAttachingCell X x P (r, p) ≫ oldDeck X x P q := by
  let B := LoopCellSphericalGenerators.nativeBoundaryLift X x P p
  exact (liftedAttachingCell_eq_deck X x P (q * r, p)).trans
    ((congrArg (fun h => B ≫ h) (oldDeck_mul X x P q r)).trans
      ((Category.assoc B (oldDeck X x P r) (oldDeck X x P q)).symm.trans
        (congrArg (fun h => h ≫ oldDeck X x P q)
          (liftedAttachingCell_eq_deck X x P (r, p)).symm)))

/-- The actual native-cover deck map is a map of the SAME original lifted pair. -/
def nativeDeckPair (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    LoopCellSphericalGenerators.liftedPair X x P ⟶ LoopCellSphericalGenerators.liftedPair X x P :=
  TopPair.ofHom (SSet.toTop.map (nativeDeck X x P q)) (SSet.toTop.map (oldDeck X x P q)) (by
    let f := LoopCellSphericalGenerators.nativePullbackToCover X x P
    exact (SSet.toTop.map_comp (oldDeck X x P q) f).symm.trans
      ((congrArg SSet.toTop.map (oldDeck_toCover X x P q)).trans
        (SSet.toTop.map_comp f (nativeDeck X x P q))))

/-- The pair deck map retains the SAME full ambient native transformation. -/
theorem nativeDeckPair_fst (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    TopPair.Hom.fst (nativeDeckPair X x P q) = SSet.toTop.map (nativeDeck X x P q) := by
  rfl

/-- Its old-space component is the SAME actual pullback transformation. -/
theorem nativeDeckPair_snd (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) :
    TopPair.Hom.snd (nativeDeckPair X x P q) = SSet.toTop.map (oldDeck X x P q) := by
  rfl

/-- The actual pair action has its genuine unit law. -/
theorem nativeDeckPair_one (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    nativeDeckPair X x P 1 = 𝟙 (LoopCellSphericalGenerators.liftedPair X x P) := by
  apply MorphismProperty.Arrow.Hom.ext
  · exact (congrArg SSet.toTop.map (oldDeck_one X x P)).trans (SSet.toTop.map_id _)
  · exact (congrArg SSet.toTop.map (nativeDeck_one X x P)).trans (SSet.toTop.map_id _)

/-- The pair action preserves the exact LEFT multiplication order of quotient labels. -/
theorem nativeDeckPair_mul (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q r : FundamentalGroup X x ⧸ P) :
    nativeDeckPair X x P (q * r) = nativeDeckPair X x P r ≫ nativeDeckPair X x P q := by
  apply MorphismProperty.Arrow.Hom.ext
  · exact (congrArg SSet.toTop.map (oldDeck_mul X x P q r)).trans
      (SSet.toTop.map_comp (oldDeck X x P r) (oldDeck X x P q))
  · exact (congrArg SSet.toTop.map (nativeDeck_mul X x P q r)).trans
      (SSet.toTop.map_comp (nativeDeck X x P r) (nativeDeck X x P q))

/-- Every ACTUAL whole labelled characteristic pair transforms by LEFT multiplication, with no path
normalization. -/
theorem cellPairToCover_deck (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q r : FundamentalGroup X x ⧸ P) (p : P) :
    cellPairToCover X x P (q * r, p) = cellPairToCover X x P (r, p) ≫ nativeDeckPair X x P q := by
  let F := SSet.toTop
  let B := (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.left
  let D := (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.right
  apply MorphismProperty.Arrow.Hom.ext
  · have hMap : F.map (liftedAttachingCell X x P (q * r, p)) =
        F.map (liftedAttachingCell X x P (r, p)) ≫ F.map (oldDeck X x P q) :=
      (congrArg F.map (liftedAttachingCell_deck X x P q r p)).trans
        (F.map_comp (liftedAttachingCell X x P (r, p)) (oldDeck X x P q))
    have hL : TopPair.Hom.snd (cellPairToCover X x P (q * r, p)) =
        (B ≫ F.map (liftedAttachingCell X x P (r, p))) ≫ F.map (oldDeck X x P q) :=
      (cellPairToCover_snd X x P (q * r, p)).trans
        ((congrArg (fun h => B ≫ h) hMap).trans
          ((Category.assoc B (F.map (liftedAttachingCell X x P (r, p)))
            (F.map (oldDeck X x P q))).symm))
    exact hL.trans
      (congrArg (fun h => h ≫ F.map (oldDeck X x P q)) (cellPairToCover_snd X x P (r, p)).symm)
  · let L := LoopCellSphericalGenerators.nativeDiskLift X x P p
    let dr := nativeDeck X x P r
    let dq := nativeDeck X x P q
    have hMap : F.map (L ≫ nativeDeck X x P (q * r)) =
        F.map (L ≫ dr) ≫ F.map dq :=
      (congrArg (fun h => F.map (L ≫ h)) (nativeDeck_mul X x P q r)).trans
        ((congrArg F.map (Category.assoc L dr dq).symm).trans (F.map_comp (L ≫ dr) dq))
    have hL : TopPair.Hom.fst (cellPairToCover X x P (q * r, p)) =
        (D ≫ F.map (L ≫ dr)) ≫ F.map dq :=
      (cellPairToCover_fst X x P (q * r, p)).trans
        ((congrArg (fun h => D ≫ h) hMap).trans
            ((Category.assoc D (F.map (L ≫ dr)) (F.map dq)).symm))
    exact hL.trans
      (congrArg (fun h => h ≫ F.map dq) (cellPairToCover_fst X x P (r, p)).symm)

/-- The characteristic pair in the native cover is the SAME actual comparison composite. -/
theorem cellPairToCover_eq (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (i : labels X x P) :
    cellPairToCover X x P i = cellPair X x P i ≫ realizedPairToCover X x P := by
  rfl

end AlgebraicTopology.LoopCellQuotientCellPresentation

end
