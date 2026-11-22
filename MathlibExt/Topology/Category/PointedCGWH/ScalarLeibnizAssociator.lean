/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeOriginalParametrizedMapping
public import MathlibExt.CategoryTheory.Enriched.ScalarCorners
public import MathlibExt.CategoryTheory.Enriched.ScalarCoherence
public import MathlibExt.CategoryTheory.Limits.Shapes.Pullback.LeibnizPushoutMaps
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Associativity of actual scalar Leibniz pushouts

The full scalar and diagram arrows and every given pushout square are retained.
Both directions use the actual scalar associator and the two actual adjunctions.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace PointedCGWH.EnrichedScalarLeibnizAssociator

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

/-- The category of enriched diagrams valued in pointed CGWH spaces. -/
abbrev Diagram := EnrichedFunctorCat PointedCGWH.{u, v} I
/-- The scalar tensor bifunctor on pointed CGWH enriched diagrams. -/
abbrev scalar := ScalarLeibniz.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I)

private instance preservesScalarTensorPushouts (Y : Diagram (I := I)) :
    PreservesColimitsOfShape WalkingSpan (scalar.flip.obj Y) :=
  (Adjunction.leftAdjoint_preservesColimits
    (PointedCGWH.NativeOriginalParametrizedMapping.adjunction.adj Y)).preservesColimitsOfShape

private theorem tensorMap_comp (M : PointedCGWH.{u, v})
    {X Y Z : Diagram (I := I)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    tensorLeftMap M (f ≫ g) = tensorLeftMap M f ≫ tensorLeftMap M g :=
  (EnrichedFunctorCat.tensorLeft M).map_comp f g

variable {M N A B : PointedCGWH.{u, v}} (j : M ⟶ N) (i : A ⟶ B)
  {X Y : Diagram (I := I)} (f : X ⟶ Y)
  (base : (curriedTensor PointedCGWH.{u, v}).PushoutObjObj j i)
  (inner : scalar.PushoutObjObj i f)
  (left : scalar.PushoutObjObj base.ι f)
  (right : scalar.PushoutObjObj j inner.ι)

/-- The left injection into the inner pushout. -/
abbrev innerInl : tensorLeftObject B X ⟶ inner.pt := inner.inl
/-- The right injection into the inner pushout. -/
abbrev innerInr : tensorLeftObject A Y ⟶ inner.pt := inner.inr
/-- The comparison arrow from the inner pushout to the target tensor. -/
abbrev innerArrow : inner.pt ⟶ tensorLeftObject B Y := inner.ι
/-- The left injection into the right-associated pushout. -/
abbrev rightInl : tensorLeftObject N inner.pt ⟶ right.pt := right.inl
/-- The right injection into the right-associated pushout. -/
abbrev rightInr : tensorLeftObject M (tensorLeftObject B Y) ⟶ right.pt := right.inr
/-- The left injection into the left-associated pushout. -/
abbrev leftInl : tensorLeftObject (N ⊗ B) X ⟶ left.pt := left.inl
/-- The right injection into the left-associated pushout. -/
abbrev leftInr : tensorLeftObject base.pt Y ⟶ left.pt := left.inr

local notation "iL" => innerInl i f inner
local notation "iR" => innerInr i f inner
local notation "iArr" => innerArrow i f inner
local notation "rL" => rightInl j i f inner right
local notation "rR" => rightInr j i f inner right
local notation "lL" => leftInl j i f base left
local notation "lR" => leftInr j i f base left

private theorem baseInl_arrow : base.inl ≫ base.ι = N ◁ i := base.inl_ι
private theorem baseInr_arrow : base.inr ≫ base.ι = j ▷ B := base.inr_ι
private theorem innerSquare : IsPushout (scalarTensorMap i X) (tensorLeftMap A f) iL iR :=
  inner.isPushout
private theorem rightSquare :
    IsPushout (scalarTensorMap j inner.pt) (tensorLeftMap M iArr) rL rR := right.isPushout
private theorem leftSquare :
    IsPushout (scalarTensorMap base.ι X) (tensorLeftMap base.pt f) lL lR := left.isPushout
private theorem innerInl_arrow : iL ≫ iArr = tensorLeftMap B f := inner.inl_ι
private theorem innerInr_arrow : iR ≫ iArr = scalarTensorMap i Y := inner.inr_ι

private theorem mappedBaseSquare (Z : Diagram (I := I)) :
    IsPushout (scalarTensorMap (j ▷ A) Z) (scalarTensorMap (M ◁ i) Z)
      (scalarTensorMap base.inl Z) (scalarTensorMap base.inr Z) :=
  (scalar.flip.obj Z).map_isPushout base.isPushout

private theorem rightLeg_condition :
    scalarTensorMap (j ▷ A) Y ≫
      (scalarAssociatorIso N A Y).hom ≫ tensorLeftMap N iR ≫ rL =
    scalarTensorMap (M ◁ i) Y ≫
      (scalarAssociatorIso M B Y).hom ≫ rR := by
  calc
    _ = (scalarAssociatorIso M A Y).hom ≫
        scalarTensorMap j (tensorLeftObject A Y) ≫ tensorLeftMap N iR ≫ rL := by
      simpa only [Category.assoc] using congrArg
        (fun q => q ≫ tensorLeftMap N iR ≫ rL)
        (scalarAssociatorIso_scalar_left j A Y)
    _ = (scalarAssociatorIso M A Y).hom ≫ tensorLeftMap M iR ≫
        scalarTensorMap j inner.pt ≫ rL := by
      simpa only [Category.assoc] using congrArg
        (fun q => (scalarAssociatorIso M A Y).hom ≫ q ≫ rL)
        (scalarTensorMap_diagram_naturality j iR).symm
    _ = (scalarAssociatorIso M A Y).hom ≫ tensorLeftMap M iR ≫
        tensorLeftMap M iArr ≫ rR := by
      rw [(rightSquare j i f inner right).w]
    _ = (scalarAssociatorIso M A Y).hom ≫ tensorLeftMap M (iR ≫ iArr) ≫ rR := by
      simp only [tensorMap_comp, Category.assoc]
    _ = (scalarAssociatorIso M A Y).hom ≫ tensorLeftMap M (scalarTensorMap i Y) ≫ rR := by
      rw [innerInr_arrow]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ rR)
        (scalarAssociatorIso_scalar_right M i Y).symm

/-- The comparison leg from the base tensor to the right-associated pushout. -/
def rightLeg : tensorLeftObject base.pt Y ⟶ right.pt := by
  let h : IsPushout (scalarTensorMap (j ▷ A) Y) (scalarTensorMap (M ◁ i) Y)
      (scalarTensorMap base.inl Y) (scalarTensorMap base.inr Y) :=
    (by exact mappedBaseSquare j i base Y)
  exact h.desc
    ((scalarAssociatorIso N A Y).hom ≫ tensorLeftMap N iR ≫ rL)
    ((scalarAssociatorIso M B Y).hom ≫ rR)
    (by exact rightLeg_condition j i f inner right)

private theorem rightLeg_inl :
    scalarTensorMap base.inl Y ≫ rightLeg j i f base inner right =
      (scalarAssociatorIso N A Y).hom ≫ tensorLeftMap N iR ≫ rL :=
  (mappedBaseSquare j i base Y).inl_desc _ _ _

private theorem rightLeg_inr :
    scalarTensorMap base.inr Y ≫ rightLeg j i f base inner right =
      (scalarAssociatorIso M B Y).hom ≫ rR :=
  (mappedBaseSquare j i base Y).inr_desc _ _ _

private theorem associatorHom_condition :
    scalarTensorMap base.ι X ≫
      (scalarAssociatorIso N B X).hom ≫ tensorLeftMap N iL ≫ rL =
      tensorLeftMap base.pt f ≫ rightLeg j i f base inner right := by
  apply (mappedBaseSquare j i base X).hom_ext
  · change scalarTensorMap base.inl X ≫ scalarTensorMap base.ι X ≫
        (scalarAssociatorIso N B X).hom ≫ tensorLeftMap N iL ≫ rL =
      scalarTensorMap base.inl X ≫ tensorLeftMap base.pt f ≫ rightLeg j i f base inner right
    have hb : scalarTensorMap base.inl X ≫ scalarTensorMap base.ι X =
        scalarTensorMap (N ◁ i) X := by
      rw [← scalarTensorMap_comp, baseInl_arrow]
    calc
      _ = scalarTensorMap (N ◁ i) X ≫ (scalarAssociatorIso N B X).hom ≫
          tensorLeftMap N iL ≫ rL := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ (scalarAssociatorIso N B X).hom ≫ tensorLeftMap N iL ≫ rL) hb
      _ = (scalarAssociatorIso N A X).hom ≫ tensorLeftMap N (scalarTensorMap i X) ≫
          tensorLeftMap N iL ≫ rL := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ tensorLeftMap N iL ≫ rL) (scalarAssociatorIso_scalar_right N i X)
      _ = (scalarAssociatorIso N A X).hom ≫
          tensorLeftMap N (scalarTensorMap i X ≫ iL) ≫ rL := by
        simp only [tensorMap_comp, Category.assoc]
      _ = (scalarAssociatorIso N A X).hom ≫ tensorLeftMap N (tensorLeftMap A f ≫ iR) ≫ rL := by
        rw [(innerSquare i f inner).w]
      _ = tensorLeftMap (N ⊗ A) f ≫ (scalarAssociatorIso N A Y).hom ≫
          tensorLeftMap N iR ≫ rL := by
        simpa only [tensorMap_comp, Category.assoc] using congrArg
          (fun q => q ≫ tensorLeftMap N iR ≫ rL) (scalarAssociatorIso_naturality N A f).symm
      _ = tensorLeftMap (N ⊗ A) f ≫ scalarTensorMap base.inl Y ≫
          rightLeg j i f base inner right := by
        rw [rightLeg_inl]
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ rightLeg j i f base inner right)
          (scalarTensorMap_diagram_naturality (M := N ⊗ A) (N := base.pt) base.inl f)
  · change scalarTensorMap base.inr X ≫ scalarTensorMap base.ι X ≫
        (scalarAssociatorIso N B X).hom ≫ tensorLeftMap N iL ≫ rL =
      scalarTensorMap base.inr X ≫ tensorLeftMap base.pt f ≫ rightLeg j i f base inner right
    have hb : scalarTensorMap base.inr X ≫ scalarTensorMap base.ι X =
        scalarTensorMap (j ▷ B) X := by
      rw [← scalarTensorMap_comp, baseInr_arrow]
    calc
      _ = scalarTensorMap (j ▷ B) X ≫ (scalarAssociatorIso N B X).hom ≫
          tensorLeftMap N iL ≫ rL := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ (scalarAssociatorIso N B X).hom ≫ tensorLeftMap N iL ≫ rL) hb
      _ = (scalarAssociatorIso M B X).hom ≫ scalarTensorMap j (tensorLeftObject B X) ≫
          tensorLeftMap N iL ≫ rL := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ tensorLeftMap N iL ≫ rL) (scalarAssociatorIso_scalar_left j B X)
      _ = (scalarAssociatorIso M B X).hom ≫ tensorLeftMap M iL ≫
          scalarTensorMap j inner.pt ≫ rL := by
        simpa only [Category.assoc] using congrArg
          (fun q => (scalarAssociatorIso M B X).hom ≫ q ≫ rL)
          (scalarTensorMap_diagram_naturality j iL).symm
      _ = (scalarAssociatorIso M B X).hom ≫ tensorLeftMap M iL ≫ tensorLeftMap M iArr ≫ rR := by
        rw [(rightSquare j i f inner right).w]
      _ = (scalarAssociatorIso M B X).hom ≫ tensorLeftMap M (iL ≫ iArr) ≫ rR := by
        simp only [tensorMap_comp, Category.assoc]
      _ = tensorLeftMap (M ⊗ B) f ≫ (scalarAssociatorIso M B Y).hom ≫ rR := by
        rw [innerInl_arrow]
        simpa only [Category.assoc] using congrArg (fun q => q ≫ rR)
          (scalarAssociatorIso_naturality M B f).symm
      _ = tensorLeftMap (M ⊗ B) f ≫ scalarTensorMap base.inr Y ≫
          rightLeg j i f base inner right := by
        rw [rightLeg_inr]
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ rightLeg j i f base inner right)
          (scalarTensorMap_diagram_naturality (M := M ⊗ B) (N := base.pt) base.inr f)

/-- The entire forward associator map uses every actual given pushout and scalar arrow. -/
def associatorHom : left.pt ⟶ right.pt :=
  left.isPushout.desc
    ((scalarAssociatorIso N B X).hom ≫ tensorLeftMap N iL ≫ rL)
    (rightLeg j i f base inner right)
    (by exact associatorHom_condition j i f base inner right)

private instance preservesDiagramTensorPushouts (T : PointedCGWH.{u, v}) :
    PreservesColimitsOfShape WalkingSpan (EnrichedFunctorCat.tensorLeft (A := I) T) :=
  (Adjunction.leftAdjoint_preservesColimits (ScalarLeibniz.adjunction T)).preservesColimitsOfShape

private theorem mappedInnerSquare (T : PointedCGWH.{u, v}) :
    IsPushout (tensorLeftMap T (scalarTensorMap i X)) (tensorLeftMap T (tensorLeftMap A f))
      (tensorLeftMap T iL) (tensorLeftMap T iR) :=
  (EnrichedFunctorCat.tensorLeft T).map_isPushout (innerSquare i f inner)

private theorem inverseInnerLeg_condition :
    tensorLeftMap N (scalarTensorMap i X) ≫ (scalarAssociatorIso N B X).inv ≫ lL =
      tensorLeftMap N (tensorLeftMap A f) ≫ (scalarAssociatorIso N A Y).inv ≫
        scalarTensorMap base.inl Y ≫ lR := by
  have hs : tensorLeftMap N (scalarTensorMap i X) ≫ (scalarAssociatorIso N B X).inv =
      (scalarAssociatorIso N A X).inv ≫ scalarTensorMap (N ◁ i) X :=
    (CommSq.vert_inv (g := scalarAssociatorIso N A X) (h := scalarAssociatorIso N B X)
      ⟨scalarAssociatorIso_scalar_right N i X⟩).w
  have hf : tensorLeftMap N (tensorLeftMap A f) ≫ (scalarAssociatorIso N A Y).inv =
      (scalarAssociatorIso N A X).inv ≫ tensorLeftMap (N ⊗ A) f :=
    (CommSq.vert_inv (g := scalarAssociatorIso N A X) (h := scalarAssociatorIso N A Y)
      ⟨scalarAssociatorIso_naturality N A f⟩).w
  have hb : scalarTensorMap base.inl X ≫ scalarTensorMap base.ι X =
      scalarTensorMap (N ◁ i) X := by rw [← scalarTensorMap_comp, baseInl_arrow]
  calc
    _ = (scalarAssociatorIso N A X).inv ≫ scalarTensorMap (N ◁ i) X ≫ lL := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ lL) hs
    _ = (scalarAssociatorIso N A X).inv ≫ scalarTensorMap base.inl X ≫
        scalarTensorMap base.ι X ≫ lL := by
      simpa only [Category.assoc] using congrArg
        (fun q => (scalarAssociatorIso N A X).inv ≫ q ≫ lL) hb.symm
    _ = (scalarAssociatorIso N A X).inv ≫ scalarTensorMap base.inl X ≫
        tensorLeftMap base.pt f ≫ lR := by rw [(leftSquare j i f base left).w]
    _ = (scalarAssociatorIso N A X).inv ≫ tensorLeftMap (N ⊗ A) f ≫
        scalarTensorMap base.inl Y ≫ lR := by
      simpa only [Category.assoc] using congrArg
        (fun q => (scalarAssociatorIso N A X).inv ≫ q ≫ lR)
        (scalarTensorMap_diagram_naturality (M := N ⊗ A) (N := base.pt) base.inl f).symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun q => q ≫ scalarTensorMap base.inl Y ≫ lR) hf.symm

/-- The comparison leg from the inner tensor to the left-associated pushout. -/
def inverseInnerLeg : tensorLeftObject N inner.pt ⟶ left.pt := by
  let h : IsPushout (tensorLeftMap N (scalarTensorMap i X))
      (tensorLeftMap N (tensorLeftMap A f)) (tensorLeftMap N iL) (tensorLeftMap N iR) :=
    (by exact mappedInnerSquare i f inner N)
  exact h.desc
    ((scalarAssociatorIso N B X).inv ≫ lL)
    ((scalarAssociatorIso N A Y).inv ≫ scalarTensorMap base.inl Y ≫ lR)
    (by exact inverseInnerLeg_condition j i f base left)

private theorem inverseInnerLeg_inl :
    tensorLeftMap N iL ≫ inverseInnerLeg j i f base inner left =
      (scalarAssociatorIso N B X).inv ≫ lL :=
  (mappedInnerSquare i f inner N).inl_desc _ _ _

private theorem inverseInnerLeg_inr :
    tensorLeftMap N iR ≫ inverseInnerLeg j i f base inner left =
      (scalarAssociatorIso N A Y).inv ≫ scalarTensorMap base.inl Y ≫ lR :=
  (mappedInnerSquare i f inner N).inr_desc _ _ _

private theorem associatorInv_condition :
    scalarTensorMap j inner.pt ≫ inverseInnerLeg j i f base inner left =
      tensorLeftMap M iArr ≫ (scalarAssociatorIso M B Y).inv ≫
        scalarTensorMap base.inr Y ≫ lR := by
  apply (mappedInnerSquare i f inner M).hom_ext
  · have hs : scalarTensorMap j (tensorLeftObject B X) ≫ (scalarAssociatorIso N B X).inv =
        (scalarAssociatorIso M B X).inv ≫ scalarTensorMap (j ▷ B) X :=
      (CommSq.vert_inv (g := scalarAssociatorIso M B X) (h := scalarAssociatorIso N B X)
        ⟨scalarAssociatorIso_scalar_left j B X⟩).w
    have hf : tensorLeftMap M (tensorLeftMap B f) ≫ (scalarAssociatorIso M B Y).inv =
        (scalarAssociatorIso M B X).inv ≫ tensorLeftMap (M ⊗ B) f :=
      (CommSq.vert_inv (g := scalarAssociatorIso M B X) (h := scalarAssociatorIso M B Y)
        ⟨scalarAssociatorIso_naturality M B f⟩).w
    have hb : scalarTensorMap base.inr X ≫ scalarTensorMap base.ι X =
        scalarTensorMap (j ▷ B) X := by rw [← scalarTensorMap_comp, baseInr_arrow]
    calc
      _ = scalarTensorMap j (tensorLeftObject B X) ≫ tensorLeftMap N iL ≫
          inverseInnerLeg j i f base inner left := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ inverseInnerLeg j i f base inner left)
          (scalarTensorMap_diagram_naturality j iL)
      _ = scalarTensorMap j (tensorLeftObject B X) ≫ (scalarAssociatorIso N B X).inv ≫ lL := by
        rw [inverseInnerLeg_inl]
      _ = (scalarAssociatorIso M B X).inv ≫ scalarTensorMap (j ▷ B) X ≫ lL := by
        simpa only [Category.assoc] using congrArg (fun q => q ≫ lL) hs
      _ = (scalarAssociatorIso M B X).inv ≫ scalarTensorMap base.inr X ≫
          scalarTensorMap base.ι X ≫ lL := by
        simpa only [Category.assoc] using congrArg
          (fun q => (scalarAssociatorIso M B X).inv ≫ q ≫ lL) hb.symm
      _ = (scalarAssociatorIso M B X).inv ≫ scalarTensorMap base.inr X ≫
          tensorLeftMap base.pt f ≫ lR := by rw [(leftSquare j i f base left).w]
      _ = (scalarAssociatorIso M B X).inv ≫ tensorLeftMap (M ⊗ B) f ≫
          scalarTensorMap base.inr Y ≫ lR := by
        simpa only [Category.assoc] using congrArg
          (fun q => (scalarAssociatorIso M B X).inv ≫ q ≫ lR)
          (scalarTensorMap_diagram_naturality (M := M ⊗ B) (N := base.pt) base.inr f).symm
      _ = tensorLeftMap M (tensorLeftMap B f) ≫ (scalarAssociatorIso M B Y).inv ≫
          scalarTensorMap base.inr Y ≫ lR := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ scalarTensorMap base.inr Y ≫ lR) hf.symm
      _ = _ := by
        simpa only [tensorMap_comp, Category.assoc] using congrArg
          (fun q => tensorLeftMap M q ≫ (scalarAssociatorIso M B Y).inv ≫
            scalarTensorMap base.inr Y ≫ lR) (innerInl_arrow i f inner).symm
  · have hs : scalarTensorMap j (tensorLeftObject A Y) ≫ (scalarAssociatorIso N A Y).inv =
        (scalarAssociatorIso M A Y).inv ≫ scalarTensorMap (j ▷ A) Y :=
      (CommSq.vert_inv (g := scalarAssociatorIso M A Y) (h := scalarAssociatorIso N A Y)
        ⟨scalarAssociatorIso_scalar_left j A Y⟩).w
    have ht : tensorLeftMap M (scalarTensorMap i Y) ≫ (scalarAssociatorIso M B Y).inv =
        (scalarAssociatorIso M A Y).inv ≫ scalarTensorMap (M ◁ i) Y :=
      (CommSq.vert_inv (g := scalarAssociatorIso M A Y) (h := scalarAssociatorIso M B Y)
        ⟨scalarAssociatorIso_scalar_right M i Y⟩).w
    have hb : scalarTensorMap (j ▷ A) Y ≫ scalarTensorMap base.inl Y =
        scalarTensorMap (M ◁ i) Y ≫ scalarTensorMap base.inr Y := by
      rw [← scalarTensorMap_comp, ← scalarTensorMap_comp]
      have hw : (j ▷ A) ≫ base.inl = (M ◁ i) ≫ base.inr := base.isPushout.w
      rw [hw]
    calc
      _ = scalarTensorMap j (tensorLeftObject A Y) ≫ tensorLeftMap N iR ≫
          inverseInnerLeg j i f base inner left := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ inverseInnerLeg j i f base inner left)
          (scalarTensorMap_diagram_naturality j iR)
      _ = scalarTensorMap j (tensorLeftObject A Y) ≫ (scalarAssociatorIso N A Y).inv ≫
          scalarTensorMap base.inl Y ≫ lR := by rw [inverseInnerLeg_inr]
      _ = (scalarAssociatorIso M A Y).inv ≫ scalarTensorMap (j ▷ A) Y ≫
          scalarTensorMap base.inl Y ≫ lR := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ scalarTensorMap base.inl Y ≫ lR) hs
      _ = (scalarAssociatorIso M A Y).inv ≫ scalarTensorMap (M ◁ i) Y ≫
          scalarTensorMap base.inr Y ≫ lR := by
        simpa only [Category.assoc] using congrArg
          (fun q => (scalarAssociatorIso M A Y).inv ≫ q ≫ lR) hb
      _ = tensorLeftMap M (scalarTensorMap i Y) ≫ (scalarAssociatorIso M B Y).inv ≫
          scalarTensorMap base.inr Y ≫ lR := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ scalarTensorMap base.inr Y ≫ lR) ht.symm
      _ = _ := by
        simpa only [tensorMap_comp, Category.assoc] using congrArg
          (fun q => tensorLeftMap M q ≫ (scalarAssociatorIso M B Y).inv ≫
            scalarTensorMap base.inr Y ≫ lR) (innerInr_arrow i f inner).symm

/-- The entire reverse associator map retains all actual tensor and pushout projections. -/
def associatorInv : right.pt ⟶ left.pt :=
  right.isPushout.desc (inverseInnerLeg j i f base inner left)
    ((scalarAssociatorIso M B Y).inv ≫ scalarTensorMap base.inr Y ≫ lR)
    (by exact associatorInv_condition j i f base inner left)

/-- The target arrow of the left-associated pushout product. -/
abbrev leftArrow : left.pt ⟶ tensorLeftObject (N ⊗ B) Y := left.ι
/-- The target arrow of the right-associated pushout product. -/
abbrev rightArrow : right.pt ⟶ tensorLeftObject N (tensorLeftObject B Y) := right.ι
local notation "lArr" => leftArrow j i f base left
local notation "rArr" => rightArrow j i f inner right

private theorem leftInl_arrow : lL ≫ lArr = tensorLeftMap (N ⊗ B) f := left.inl_ι
private theorem leftInr_arrow : lR ≫ lArr = scalarTensorMap base.ι Y := left.inr_ι
private theorem rightInl_arrow : rL ≫ rArr = tensorLeftMap N iArr := right.inl_ι
private theorem rightInr_arrow : rR ≫ rArr = scalarTensorMap j (tensorLeftObject B Y) := right.inr_ι

private theorem associatorHom_inl :
    lL ≫ associatorHom j i f base inner left right =
      (scalarAssociatorIso N B X).hom ≫ tensorLeftMap N iL ≫ rL :=
  (leftSquare j i f base left).inl_desc _ _ _

private theorem associatorHom_inr :
    lR ≫ associatorHom j i f base inner left right = rightLeg j i f base inner right :=
  (leftSquare j i f base left).inr_desc _ _ _

private theorem associatorInv_inl :
    rL ≫ associatorInv j i f base inner left right = inverseInnerLeg j i f base inner left :=
  (rightSquare j i f inner right).inl_desc _ _ _

private theorem associatorInv_inr :
    rR ≫ associatorInv j i f base inner left right =
      (scalarAssociatorIso M B Y).inv ≫ scalarTensorMap base.inr Y ≫ lR :=
  (rightSquare j i f inner right).inr_desc _ _ _

private theorem rightLeg_associatorInv :
    rightLeg j i f base inner right ≫ associatorInv j i f base inner left right = lR := by
  apply (mappedBaseSquare j i base Y).hom_ext
  · calc
      _ = (scalarAssociatorIso N A Y).hom ≫ tensorLeftMap N iR ≫ rL ≫
          associatorInv j i f base inner left right := by
        rw [← Category.assoc, rightLeg_inl]
        simp only [Category.assoc]
      _ = _ := by
        rw [associatorInv_inl, inverseInnerLeg_inr]
        simp only [Iso.hom_inv_id_assoc]
  · calc
      _ = (scalarAssociatorIso M B Y).hom ≫ rR ≫
          associatorInv j i f base inner left right := by
        rw [← Category.assoc, rightLeg_inr]
        simp only [Category.assoc]
      _ = _ := by
        rw [associatorInv_inr]
        simp only [Iso.hom_inv_id_assoc]

private theorem inverseInnerLeg_associatorHom :
    inverseInnerLeg j i f base inner left ≫ associatorHom j i f base inner left right = rL := by
  apply (mappedInnerSquare i f inner N).hom_ext
  · calc
      _ = (scalarAssociatorIso N B X).inv ≫ lL ≫
          associatorHom j i f base inner left right := by
        rw [← Category.assoc, inverseInnerLeg_inl]
        simp only [Category.assoc]
      _ = _ := by
        rw [associatorHom_inl]
        simp only [Iso.inv_hom_id_assoc]
  · calc
      _ = (scalarAssociatorIso N A Y).inv ≫ scalarTensorMap base.inl Y ≫ lR ≫
          associatorHom j i f base inner left right := by
        rw [← Category.assoc, inverseInnerLeg_inr]
        simp only [Category.assoc]
      _ = _ := by
        rw [associatorHom_inr, rightLeg_inl]
        simp only [Iso.inv_hom_id_assoc]

/-- Both complete original associator functions return every actual left pushout input. -/
theorem associatorHom_inv :
    associatorHom j i f base inner left right ≫ associatorInv j i f base inner left right =
      𝟙 left.pt := by
  apply (leftSquare j i f base left).hom_ext
  · calc
      _ = (scalarAssociatorIso N B X).hom ≫ tensorLeftMap N iL ≫ rL ≫
          associatorInv j i f base inner left right := by
        rw [← Category.assoc, associatorHom_inl]
        simp only [Category.assoc]
      _ = _ := by
        rw [associatorInv_inl, inverseInnerLeg_inl]
        simp only [Iso.hom_inv_id_assoc, Category.comp_id]
  · rw [← Category.assoc, associatorHom_inr, rightLeg_associatorInv, Category.comp_id]

/-- Both complete original associator functions return every actual right pushout input. -/
theorem associatorInv_hom :
    associatorInv j i f base inner left right ≫ associatorHom j i f base inner left right =
      𝟙 right.pt := by
  apply (rightSquare j i f inner right).hom_ext
  · rw [← Category.assoc, associatorInv_inl, inverseInnerLeg_associatorHom, Category.comp_id]
  · calc
      _ = (scalarAssociatorIso M B Y).inv ≫ scalarTensorMap base.inr Y ≫ lR ≫
          associatorHom j i f base inner left right := by
        rw [← Category.assoc, associatorInv_inr]
        simp only [Category.assoc]
      _ = _ := by
        rw [associatorHom_inr, rightLeg_inr]
        simp only [Iso.inv_hom_id_assoc, Category.comp_id]

private theorem rightLeg_arrow :
    rightLeg j i f base inner right ≫ rArr =
      scalarTensorMap base.ι Y ≫ (scalarAssociatorIso N B Y).hom := by
  apply (mappedBaseSquare j i base Y).hom_ext
  · have hb : scalarTensorMap base.inl Y ≫ scalarTensorMap base.ι Y =
        scalarTensorMap (N ◁ i) Y := by rw [← scalarTensorMap_comp, baseInl_arrow]
    calc
      _ = (scalarAssociatorIso N A Y).hom ≫ tensorLeftMap N iR ≫ rL ≫ rArr := by
        rw [← Category.assoc, rightLeg_inl]
        simp only [Category.assoc]
      _ = (scalarAssociatorIso N A Y).hom ≫ tensorLeftMap N (iR ≫ iArr) := by
        rw [rightInl_arrow]
        simp only [tensorMap_comp]
      _ = scalarTensorMap (N ◁ i) Y ≫ (scalarAssociatorIso N B Y).hom := by
        rw [innerInr_arrow]
        exact (scalarAssociatorIso_scalar_right N i Y).symm
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ (scalarAssociatorIso N B Y).hom) hb.symm
  · have hb : scalarTensorMap base.inr Y ≫ scalarTensorMap base.ι Y =
        scalarTensorMap (j ▷ B) Y := by rw [← scalarTensorMap_comp, baseInr_arrow]
    calc
      _ = (scalarAssociatorIso M B Y).hom ≫ rR ≫ rArr := by
        rw [← Category.assoc, rightLeg_inr]
        simp only [Category.assoc]
      _ = scalarTensorMap (j ▷ B) Y ≫ (scalarAssociatorIso N B Y).hom := by
        rw [rightInr_arrow]
        exact (scalarAssociatorIso_scalar_left j B Y).symm
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ (scalarAssociatorIso N B Y).hom) hb.symm

/-- The full forward map commutes with the original given Leibniz arrows. -/
theorem associatorHom_arrow :
    associatorHom j i f base inner left right ≫ rArr =
      lArr ≫ (scalarAssociatorIso N B Y).hom := by
  apply (leftSquare j i f base left).hom_ext
  · calc
      _ = (scalarAssociatorIso N B X).hom ≫ tensorLeftMap N iL ≫ rL ≫ rArr := by
        rw [← Category.assoc, associatorHom_inl]
        simp only [Category.assoc]
      _ = (scalarAssociatorIso N B X).hom ≫ tensorLeftMap N (iL ≫ iArr) := by
        rw [rightInl_arrow]
        simp only [tensorMap_comp]
      _ = tensorLeftMap (N ⊗ B) f ≫ (scalarAssociatorIso N B Y).hom := by
        rw [innerInl_arrow]
        exact (scalarAssociatorIso_naturality N B f).symm
      _ = _ := by rw [← Category.assoc, leftInl_arrow]
  · rw [← Category.assoc, associatorHom_inr, rightLeg_arrow,
      ← Category.assoc, leftInr_arrow]

/-- The complete actual scalar pushout associator retains both entire map functions. -/
def associatorIso : Arrow.mk left.ι ≅ Arrow.mk right.ι :=
  Arrow.isoMk
    { hom := associatorHom j i f base inner left right
      inv := associatorInv j i f base inner left right
      hom_inv_id := associatorHom_inv j i f base inner left right
      inv_hom_id := associatorInv_hom j i f base inner left right }
    (scalarAssociatorIso N B Y) (associatorHom_arrow j i f base inner left right)

end PointedCGWH.EnrichedScalarLeibnizAssociator




/-!
## Naturality of the complete scalar Leibniz associator

Every original arrow and every given pushout square is retained. Canonical mapping
tensor squares are taken from the flipped bifunctor, as in the actual functor.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u₁ u₂ u₃ v₁ v₂ v₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed



namespace PointedCGWH.EnrichedScalarLeibnizAssociator

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private theorem tensor_map_comp (M : PointedCGWH.{u, v})
    {X Y Z : Diagram (I := I)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    tensorLeftMap M (f ≫ g) = tensorLeftMap M f ≫ tensorLeftMap M g :=
  (EnrichedFunctorCat.tensorLeft M).map_comp f g

section Faces

variable {M N A B : PointedCGWH.{u, v}} (j : M ⟶ N) (i : A ⟶ B)
  {X Y : Diagram (I := I)} (f : X ⟶ Y)
  (base : (curriedTensor PointedCGWH.{u, v}).PushoutObjObj j i)
  (inner : scalar.PushoutObjObj i f)
  (left : scalar.PushoutObjObj base.ι f)
  (right : scalar.PushoutObjObj j inner.ι)

/-- The left injection into the base pushout. -/
abbrev bL : N ⊗ A ⟶ base.pt := base.inl
/-- The right injection into the base pushout. -/
abbrev bR : M ⊗ B ⟶ base.pt := base.inr
/-- The left injection into the left-associated pushout. -/
abbrev lL : tensorLeftObject (N ⊗ B) X ⟶ left.pt := left.inl
/-- The right injection into the left-associated pushout. -/
abbrev lR : tensorLeftObject base.pt Y ⟶ left.pt := left.inr
/-- The left injection into the inner pushout. -/
abbrev iL : tensorLeftObject B X ⟶ inner.pt := inner.inl
/-- The right injection into the inner pushout. -/
abbrev iR : tensorLeftObject A Y ⟶ inner.pt := inner.inr
/-- The left injection into the right-associated pushout. -/
abbrev rL : tensorLeftObject N inner.pt ⟶ right.pt := right.inl
/-- The right injection into the right-associated pushout. -/
abbrev rR : tensorLeftObject M (tensorLeftObject B Y) ⟶ right.pt := right.inr

/-- The complete forward associator retains the left pushout inclusion. -/
@[reassoc]
theorem associatorHom_inl_eq :
    lL j i f base left ≫ associatorHom j i f base inner left right =
      (scalarAssociatorIso N B X).hom ≫ tensorLeftMap N (iL i f inner) ≫
        rL j i f inner right :=
  associatorHom_inl j i f base inner left right

/-- The first face of the mapped original base pushout is preserved. -/
@[reassoc]
theorem associatorHom_inr_inl_eq :
    scalarTensorMap (bL j i base) Y ≫ lR j i f base left ≫
        associatorHom j i f base inner left right =
      (scalarAssociatorIso N A Y).hom ≫ tensorLeftMap N (iR i f inner) ≫
        rL j i f inner right := by
  exact (congrArg (fun q => scalarTensorMap (bL j i base) Y ≫ q)
    (associatorHom_inr j i f base inner left right)).trans
    (rightLeg_inl j i f base inner right)

/-- The second face retains the original scalar map and right inclusion. -/
@[reassoc]
theorem associatorHom_inr_inr_eq :
    scalarTensorMap (bR j i base) Y ≫ lR j i f base left ≫
        associatorHom j i f base inner left right =
      (scalarAssociatorIso M B Y).hom ≫ rR j i f inner right := by
  exact (congrArg (fun q => scalarTensorMap (bR j i base) Y ≫ q)
    (associatorHom_inr j i f base inner left right)).trans
    (rightLeg_inr j i f base inner right)

end Faces

section Naturality

variable {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
  {X Y : Diagram (I := I)} (f : X ⟶ Y)
  {i₁ i₂ : Arrow PointedCGWH.{u, v}} (a : i₁ ⟶ i₂)
  (base₁ : (curriedTensor PointedCGWH.{u, v}).PushoutObjObj j i₁.hom)
  (base₂ : (curriedTensor PointedCGWH.{u, v}).PushoutObjObj j i₂.hom)
  (inner₁ : scalar.PushoutObjObj i₁.hom f)
  (inner₂ : scalar.PushoutObjObj i₂.hom f)
  (left₁ : scalar.PushoutObjObj base₁.ι f)
  (left₂ : scalar.PushoutObjObj base₂.ι f)
  (right₁ : scalar.PushoutObjObj j inner₁.ι)
  (right₂ : scalar.PushoutObjObj j inner₂.ι)

open Functor.PushoutObjObj

/-- The map between base pushouts induced by a morphism of the original input diagram. -/
abbrev bMap (a : i₁ ⟶ i₂)
    (base₁ : (curriedTensor PointedCGWH.{u, v}).PushoutObjObj j i₁.hom)
    (base₂ : (curriedTensor PointedCGWH.{u, v}).PushoutObjObj j i₂.hom) :
    Arrow.mk base₁.ι ⟶ Arrow.mk base₂.ι :=
  mapArrowRight (F := curriedTensor PointedCGWH.{u, v})
    (f₁ := Arrow.mk j) (f₂ := i₁) (f₂' := i₂) base₁ base₂ a

/-- The map between inner pushouts induced by a morphism of the original input diagram. -/
abbrev iMap (a : i₁ ⟶ i₂)
    (inner₁ : scalar.PushoutObjObj i₁.hom f) (inner₂ : scalar.PushoutObjObj i₂.hom f) :
    Arrow.mk inner₁.ι ⟶ Arrow.mk inner₂.ι :=
  mapArrowLeft (F := scalar) (f₁ := i₁) (f₁' := i₂) (f₂ := Arrow.mk f) inner₁ inner₂ a

/-- The map between left-associated pushouts induced by a morphism of the input diagram. -/
abbrev lMap (a : i₁ ⟶ i₂)
    (base₁ : (curriedTensor PointedCGWH.{u, v}).PushoutObjObj j i₁.hom)
    (base₂ : (curriedTensor PointedCGWH.{u, v}).PushoutObjObj j i₂.hom)
    (left₁ : scalar.PushoutObjObj base₁.ι f) (left₂ : scalar.PushoutObjObj base₂.ι f) :
    Arrow.mk left₁.ι ⟶ Arrow.mk left₂.ι :=
  mapArrowLeft (F := scalar) (f₁ := Arrow.mk base₁.ι) (f₁' := Arrow.mk base₂.ι)
    (f₂ := Arrow.mk f) left₁ left₂ (bMap j a base₁ base₂)

/-- The map between right-associated pushouts induced by a morphism of the input diagram. -/
abbrev rMap (a : i₁ ⟶ i₂)
    (inner₁ : scalar.PushoutObjObj i₁.hom f) (inner₂ : scalar.PushoutObjObj i₂.hom f)
    (right₁ : scalar.PushoutObjObj j inner₁.ι) (right₂ : scalar.PushoutObjObj j inner₂.ι) :
    Arrow.mk right₁.ι ⟶ Arrow.mk right₂.ι :=
  mapArrowRight (F := scalar) (f₁ := Arrow.mk j)
    (f₂ := Arrow.mk inner₁.ι) (f₂' := Arrow.mk inner₂.ι) right₁ right₂
    (iMap f a inner₁ inner₂)

/-- Naturality retains both full source functions and all eight given squares. -/
theorem associatorHom_naturality :
    (lMap j f a base₁ base₂ left₁ left₂).left ≫
        associatorHom j i₂.hom f base₂ inner₂ left₂ right₂ =
      associatorHom j i₁.hom f base₁ inner₁ left₁ right₁ ≫
        (rMap j f a inner₁ inner₂ right₁ right₂).left := by
  apply left₁.hom_ext
  · change (lL j i₁.hom f base₁ left₁) ≫ (lMap j f a base₁ base₂ left₁ left₂).left ≫
        associatorHom j i₂.hom f base₂ inner₂ left₂ right₂ =
      (lL j i₁.hom f base₁ left₁) ≫ associatorHom j i₁.hom f base₁ inner₁ left₁ right₁ ≫
        (rMap j f a inner₁ inner₂ right₁ right₂).left
    have hLeft :
        (lL j i₁.hom f base₁ left₁) ≫ (lMap j f a base₁ base₂ left₁ left₂).left =
          scalarTensorMap (N ◁ a.right) X ≫ (lL j i₂.hom f base₂ left₂) :=
      inl_mapArrowLeft (F := scalar) (f₁ := Arrow.mk base₁.ι)
        (f₁' := Arrow.mk base₂.ι) (f₂ := Arrow.mk f) left₁ left₂ (bMap j a base₁ base₂)
    have hInner :
        (iL i₁.hom f inner₁) ≫ (iMap f a inner₁ inner₂).left =
          scalarTensorMap a.right X ≫ (iL i₂.hom f inner₂) :=
      inl_mapArrowLeft (F := scalar) (f₁ := i₁) (f₁' := i₂)
          (f₂ := Arrow.mk f) inner₁ inner₂ a
    have hRight :
        (rL j i₁.hom f inner₁ right₁) ≫ (rMap j f a inner₁ inner₂ right₁ right₂).left =
          tensorLeftMap N (iMap f a inner₁ inner₂).left ≫ (rL j i₂.hom f inner₂ right₂) :=
      inl_mapArrowRight (F := scalar) (f₁ := Arrow.mk j)
          (f₂ := Arrow.mk inner₁.ι) (f₂' := Arrow.mk inner₂.ι) right₁ right₂
          (iMap f a inner₁ inner₂)
    calc
      _ = scalarTensorMap (N ◁ a.right) X ≫ (lL j i₂.hom f base₂ left₂) ≫
          associatorHom j i₂.hom f base₂ inner₂ left₂ right₂ := by
        rw [← Category.assoc, hLeft]
        simp only [Category.assoc]
      _ = scalarTensorMap (N ◁ a.right) X ≫ (scalarAssociatorIso N i₂.right X).hom ≫
          tensorLeftMap N (iL i₂.hom f inner₂) ≫ (rL j i₂.hom f inner₂ right₂) := by
        rw [associatorHom_inl_eq]
      _ = (scalarAssociatorIso N i₁.right X).hom ≫
          tensorLeftMap N (scalarTensorMap a.right X) ≫
          tensorLeftMap N (iL i₂.hom f inner₂) ≫ (rL j i₂.hom f inner₂ right₂) := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ tensorLeftMap N (iL i₂.hom f inner₂) ≫ (rL j i₂.hom f inner₂ right₂))
          (scalarAssociatorIso_scalar_right N a.right X)
      _ = (scalarAssociatorIso N i₁.right X).hom ≫
          tensorLeftMap N ((iL i₁.hom f inner₁) ≫ (iMap f a inner₁ inner₂).left) ≫ (rL j i₂.hom f
              inner₂ right₂) := by
        rw [hInner]
        simp only [tensor_map_comp, Category.assoc]
      _ = (scalarAssociatorIso N i₁.right X).hom ≫ tensorLeftMap N (iL i₁.hom f inner₁) ≫
          (rL j i₁.hom f inner₁ right₁) ≫ (rMap j f a inner₁ inner₂ right₁ right₂).left := by
        rw [hRight]
        simp only [tensor_map_comp, Category.assoc]
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ (rMap j f a inner₁ inner₂ right₁ right₂).left)
          (associatorHom_inl_eq j i₁.hom f base₁ inner₁ left₁ right₁).symm
  · change (lR j i₁.hom f base₁ left₁) ≫ (lMap j f a base₁ base₂ left₁ left₂).left ≫
        associatorHom j i₂.hom f base₂ inner₂ left₂ right₂ =
      (lR j i₁.hom f base₁ left₁) ≫ associatorHom j i₁.hom f base₁ inner₁ left₁ right₁ ≫
        (rMap j f a inner₁ inner₂ right₁ right₂).left
    have hLeft :
        (lR j i₁.hom f base₁ left₁) ≫ (lMap j f a base₁ base₂ left₁ left₂).left =
          scalarTensorMap (bMap j a base₁ base₂).left Y ≫ (lR j i₂.hom f base₂ left₂) :=
      inr_mapArrowLeft (F := scalar) (f₁ := Arrow.mk base₁.ι)
        (f₁' := Arrow.mk base₂.ι) (f₂ := Arrow.mk f) left₁ left₂ (bMap j a base₁ base₂)
    apply (mappedBaseSquare j i₁.hom base₁ Y).hom_ext
    · change scalarTensorMap (bL j i₁.hom base₁) Y ≫
          (lR j i₁.hom f base₁ left₁) ≫ (lMap j f a base₁ base₂ left₁ left₂).left ≫
            associatorHom j i₂.hom f base₂ inner₂ left₂ right₂ =
        scalarTensorMap (bL j i₁.hom base₁) Y ≫
          (lR j i₁.hom f base₁ left₁) ≫ associatorHom j i₁.hom f base₁ inner₁ left₁ right₁ ≫
            (rMap j f a inner₁ inner₂ right₁ right₂).left
      have hBase :
          scalarTensorMap (bL j i₁.hom base₁) Y ≫ scalarTensorMap (bMap j a base₁ base₂).left Y =
            scalarTensorMap (N ◁ a.left) Y ≫ scalarTensorMap (bL j i₂.hom base₂) Y := by
        rw [← scalarTensorMap_comp, ← scalarTensorMap_comp]
        exact congrArg (fun q => scalarTensorMap q Y) (inl_mapArrowRight (F := curriedTensor
            PointedCGWH.{u, v})
            (f₁ := Arrow.mk j) (f₂ := i₁) (f₂' := i₂) base₁ base₂ a)
      have hInner :
          (iR i₁.hom f inner₁) ≫ (iMap f a inner₁ inner₂).left =
            scalarTensorMap a.left Y ≫ (iR i₂.hom f inner₂) :=
        inr_mapArrowLeft (F := scalar) (f₁ := i₁) (f₁' := i₂)
          (f₂ := Arrow.mk f) inner₁ inner₂ a
      have hRight :
          (rL j i₁.hom f inner₁ right₁) ≫ (rMap j f a inner₁ inner₂ right₁ right₂).left =
            tensorLeftMap N (iMap f a inner₁ inner₂).left ≫ (rL j i₂.hom f inner₂ right₂) :=
        inl_mapArrowRight (F := scalar) (f₁ := Arrow.mk j)
          (f₂ := Arrow.mk inner₁.ι) (f₂' := Arrow.mk inner₂.ι) right₁ right₂
          (iMap f a inner₁ inner₂)
      calc
        _ = scalarTensorMap (N ◁ a.left) Y ≫ scalarTensorMap (bL j i₂.hom base₂) Y ≫
            (lR j i₂.hom f base₂ left₂) ≫ associatorHom j i₂.hom f base₂ inner₂ left₂ right₂ := by
          rw [reassoc_of% hLeft]
          simpa only [Category.assoc] using congrArg
            (fun q => q ≫ (lR j i₂.hom f base₂ left₂) ≫ associatorHom j i₂.hom f base₂ inner₂ left₂
                right₂)
            hBase
        _ = scalarTensorMap (N ◁ a.left) Y ≫ (scalarAssociatorIso N i₂.left Y).hom ≫
            tensorLeftMap N (iR i₂.hom f inner₂) ≫ (rL j i₂.hom f inner₂ right₂) := by
          rw [associatorHom_inr_inl_eq]
        _ = (scalarAssociatorIso N i₁.left Y).hom ≫
            tensorLeftMap N (scalarTensorMap a.left Y) ≫
            tensorLeftMap N (iR i₂.hom f inner₂) ≫ (rL j i₂.hom f inner₂ right₂) := by
          simpa only [Category.assoc] using congrArg
            (fun q => q ≫ tensorLeftMap N (iR i₂.hom f inner₂) ≫ (rL j i₂.hom f inner₂ right₂))
            (scalarAssociatorIso_scalar_right N a.left Y)
        _ = (scalarAssociatorIso N i₁.left Y).hom ≫
            tensorLeftMap N ((iR i₁.hom f inner₁) ≫ (iMap f a inner₁ inner₂).left) ≫ (rL j i₂.hom f
                inner₂ right₂) := by
          rw [hInner]
          simp only [tensor_map_comp, Category.assoc]
        _ = (scalarAssociatorIso N i₁.left Y).hom ≫ tensorLeftMap N (iR i₁.hom f inner₁) ≫
            (rL j i₁.hom f inner₁ right₁) ≫ (rMap j f a inner₁ inner₂ right₁ right₂).left := by
          rw [hRight]
          simp only [tensor_map_comp, Category.assoc]
        _ = _ := by
          simpa only [Category.assoc] using congrArg
            (fun q => q ≫ (rMap j f a inner₁ inner₂ right₁ right₂).left)
            (associatorHom_inr_inl_eq j i₁.hom f base₁ inner₁ left₁ right₁).symm
    · change scalarTensorMap (bR j i₁.hom base₁) Y ≫
          (lR j i₁.hom f base₁ left₁) ≫ (lMap j f a base₁ base₂ left₁ left₂).left ≫
            associatorHom j i₂.hom f base₂ inner₂ left₂ right₂ =
        scalarTensorMap (bR j i₁.hom base₁) Y ≫
          (lR j i₁.hom f base₁ left₁) ≫ associatorHom j i₁.hom f base₁ inner₁ left₁ right₁ ≫
            (rMap j f a inner₁ inner₂ right₁ right₂).left
      have hBase :
          scalarTensorMap (bR j i₁.hom base₁) Y ≫ scalarTensorMap (bMap j a base₁ base₂).left Y =
            scalarTensorMap (M ◁ a.right) Y ≫ scalarTensorMap (bR j i₂.hom base₂) Y := by
        rw [← scalarTensorMap_comp, ← scalarTensorMap_comp]
        exact congrArg (fun q => scalarTensorMap q Y) (inr_mapArrowRight (F := curriedTensor
            PointedCGWH.{u, v})
            (f₁ := Arrow.mk j) (f₂ := i₁) (f₂' := i₂) base₁ base₂ a)
      have hRight :
          (rR j i₁.hom f inner₁ right₁) ≫ (rMap j f a inner₁ inner₂ right₁ right₂).left =
            tensorLeftMap M (scalarTensorMap a.right Y) ≫ (rR j i₂.hom f inner₂ right₂) :=
        inr_mapArrowRight (F := scalar) (f₁ := Arrow.mk j)
          (f₂ := Arrow.mk inner₁.ι) (f₂' := Arrow.mk inner₂.ι) right₁ right₂
          (iMap f a inner₁ inner₂)
      calc
        _ = scalarTensorMap (M ◁ a.right) Y ≫ scalarTensorMap (bR j i₂.hom base₂) Y ≫
            (lR j i₂.hom f base₂ left₂) ≫ associatorHom j i₂.hom f base₂ inner₂ left₂ right₂ := by
          rw [reassoc_of% hLeft]
          simpa only [Category.assoc] using congrArg
            (fun q => q ≫ (lR j i₂.hom f base₂ left₂) ≫ associatorHom j i₂.hom f base₂ inner₂ left₂
                right₂)
            hBase
        _ = scalarTensorMap (M ◁ a.right) Y ≫ (scalarAssociatorIso M i₂.right Y).hom ≫
            (rR j i₂.hom f inner₂ right₂) := by rw [associatorHom_inr_inr_eq]
        _ = (scalarAssociatorIso M i₁.right Y).hom ≫
            tensorLeftMap M (scalarTensorMap a.right Y) ≫ (rR j i₂.hom f inner₂ right₂) := by
          simpa only [Category.assoc] using congrArg (fun q => q ≫ (rR j i₂.hom f inner₂ right₂))
            (scalarAssociatorIso_scalar_right M a.right Y)
        _ = (scalarAssociatorIso M i₁.right Y).hom ≫ (rR j i₁.hom f inner₁ right₁) ≫
            (rMap j f a inner₁ inner₂ right₁ right₂).left := by rw [hRight]
        _ = _ := by
          simpa only [Category.assoc] using congrArg
            (fun q => q ≫ (rMap j f a inner₁ inner₂ right₁ right₂).left)
            (associatorHom_inr_inr_eq j i₁.hom f base₁ inner₁ left₁ right₁).symm

/-- The complete Arrow isomorphism is natural on every original Arrow morphism. -/
theorem associatorIso_naturality :
    lMap j f a base₁ base₂ left₁ left₂ ≫
        (associatorIso j i₂.hom f base₂ inner₂ left₂ right₂).hom =
      (associatorIso j i₁.hom f base₁ inner₁ left₁ right₁).hom ≫
        rMap j f a inner₁ inner₂ right₁ right₂ := by
  apply Arrow.hom_ext
  · exact associatorHom_naturality j f a base₁ base₂ inner₁ inner₂ left₁ left₂ right₁ right₂
  · change scalarTensorMap (N ◁ a.right) Y ≫ (scalarAssociatorIso N i₂.right Y).hom =
      (scalarAssociatorIso N i₁.right Y).hom ≫ tensorLeftMap N (scalarTensorMap a.right Y)
    exact scalarAssociatorIso_scalar_right N a.right Y

end Naturality

/-- The actual base scalar pushout functor uses its original canonical squares. -/
abbrev basePushout {M N : PointedCGWH.{u, v}} (j : M ⟶ N) :
    Arrow PointedCGWH.{u, v} ⥤ Arrow PointedCGWH.{u, v} :=
  (curriedTensor PointedCGWH.{u, v}).leibnizPushout.obj (Arrow.mk j)

/-- The actual mapping tensor functor uses the flipped scalar bifunctor. -/
abbrev mappingTensor {X Y : Diagram (I := I)} (f : X ⟶ Y) :
    Arrow PointedCGWH.{u, v} ⥤ Arrow (Diagram (I := I)) :=
  scalar.flip.leibnizPushout.obj (Arrow.mk f)

/-- The actual scalar pushout functor retains every diagram Arrow map. -/
abbrev scalarPushout {M N : PointedCGWH.{u, v}} (j : M ⟶ N) :
    Arrow (Diagram (I := I)) ⥤ Arrow (Diagram (I := I)) :=
  scalar.leibnizPushout.obj (Arrow.mk j)

/-- The component uses exactly the given choices of the two canonical functors. -/
def canonicalAssociatorIso {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {X Y : Diagram (I := I)} (f : X ⟶ Y) (i : Arrow PointedCGWH.{u, v}) :
    (basePushout j ⋙ mappingTensor f).obj i ≅ (mappingTensor f ⋙ scalarPushout j).obj i :=
  let base := Functor.PushoutObjObj.ofHasPushout (curriedTensor PointedCGWH.{u, v}) j i.hom
  let inner := Functor.PushoutObjObj.ofHasPushout scalar.flip f i.hom
  associatorIso j i.hom f base inner.flip
    (Functor.PushoutObjObj.ofHasPushout scalar.flip f base.ι).flip
    (Functor.PushoutObjObj.ofHasPushout scalar j inner.ι)

/-- Whole Arrow naturality uses the exact flipped canonical mapping squares. -/
theorem canonicalAssociatorIso_naturality {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {X Y : Diagram (I := I)} (f : X ⟶ Y) {i₁ i₂ : Arrow PointedCGWH.{u, v}}
    (a : i₁ ⟶ i₂) :
    (basePushout j ⋙ mappingTensor f).map a ≫ (canonicalAssociatorIso j f i₂).hom =
      (canonicalAssociatorIso j f i₁).hom ≫ (mappingTensor f ⋙ scalarPushout j).map a := by
  let base₁ := Functor.PushoutObjObj.ofHasPushout (curriedTensor PointedCGWH.{u, v}) j i₁.hom
  let base₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor PointedCGWH.{u, v}) j i₂.hom
  let inner₁ := Functor.PushoutObjObj.ofHasPushout scalar.flip f i₁.hom
  let inner₂ := Functor.PushoutObjObj.ofHasPushout scalar.flip f i₂.hom
  let left₁ := Functor.PushoutObjObj.ofHasPushout scalar.flip f base₁.ι
  let left₂ := Functor.PushoutObjObj.ofHasPushout scalar.flip f base₂.ι
  let right₁ := Functor.PushoutObjObj.ofHasPushout scalar j inner₁.ι
  let right₂ := Functor.PushoutObjObj.ofHasPushout scalar j inner₂.ι
  change Functor.PushoutObjObj.mapArrowRight (F := scalar.flip)
        (f₁ := Arrow.mk f) (f₂ := Arrow.mk base₁.ι) (f₂' := Arrow.mk base₂.ι) left₁ left₂
        (bMap j a base₁ base₂) ≫
      (associatorIso j i₂.hom f base₂ inner₂.flip left₂.flip right₂).hom =
    (associatorIso j i₁.hom f base₁ inner₁.flip left₁.flip right₁).hom ≫
      Functor.PushoutObjObj.mapArrowRight (F := scalar)
        (f₁ := Arrow.mk j) (f₂ := Arrow.mk inner₁.ι) (f₂' := Arrow.mk inner₂.ι) right₁ right₂
        (Functor.PushoutObjObj.mapArrowRight (F := scalar.flip)
          (f₁ := Arrow.mk f) (f₂ := i₁) (f₂' := i₂) inner₁ inner₂ a)
  have hLeft := Functor.PushoutObjObj.mapArrowLeft_flip (F := scalar.flip)
    (f₁ := Arrow.mk f) (f₂ := Arrow.mk base₁.ι) (f₂' := Arrow.mk base₂.ι) left₁ left₂
    (bMap j a base₁ base₂)
  have hInner := Functor.PushoutObjObj.mapArrowLeft_flip (F := scalar.flip)
    (f₁ := Arrow.mk f) (f₂ := i₁) (f₂' := i₂) inner₁ inner₂ a
  calc
    _ = lMap j f a base₁ base₂ left₁.flip left₂.flip ≫
      (associatorIso j i₂.hom f base₂ inner₂.flip left₂.flip right₂).hom :=
        congrArg (fun q => q ≫
          (associatorIso j i₂.hom f base₂ inner₂.flip left₂.flip right₂).hom) hLeft.symm
    _ = (associatorIso j i₁.hom f base₁ inner₁.flip left₁.flip right₁).hom ≫
      Functor.PushoutObjObj.mapArrowRight (F := scalar)
        (f₁ := Arrow.mk j) (f₂ := Arrow.mk inner₁.ι) (f₂' := Arrow.mk inner₂.ι) right₁ right₂
        (iMap f a inner₁.flip inner₂.flip) :=
          associatorIso_naturality j f a base₁ base₂ inner₁.flip inner₂.flip
            left₁.flip left₂.flip right₁ right₂
    _ = _ := congrArg (fun q =>
      (associatorIso j i₁.hom f base₁ inner₁.flip left₁.flip right₁).hom ≫
        Functor.PushoutObjObj.mapArrowRight (F := scalar)
        (f₁ := Arrow.mk j) (f₂ := Arrow.mk inner₁.ι) (f₂' := Arrow.mk inner₂.ι) right₁ right₂ q)
            hInner

/-- The complete scalar Leibniz associator is an isomorphism of actual Arrow functors. -/
def associatorNatIso {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {X Y : Diagram (I := I)} (f : X ⟶ Y) :
    basePushout j ⋙ mappingTensor f ≅ mappingTensor f ⋙ scalarPushout j :=
  NatIso.ofComponents (canonicalAssociatorIso j f) (canonicalAssociatorIso_naturality j f)

end PointedCGWH.EnrichedScalarLeibnizAssociator
