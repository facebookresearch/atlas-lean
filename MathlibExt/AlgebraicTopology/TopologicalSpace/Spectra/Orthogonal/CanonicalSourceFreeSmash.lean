/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Enriched.RightModuleFreeEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceSmash
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereSmashFree
import Lean.Util.ShareCommon

/-!
# Actual free smash on canonical orthogonal spectra

The original free right sphere modules are smashed using their actual
relative tensor. The genuine enriched Day free-pair comparison identifies
the result with the original free module at the tensor index. The complete
native/source equivalence and its original free/evaluation comparisons
then reconstruct the canonical free smash. Both input comparisons, both
equivalence units and the original target free comparison remain in the
maps. Their source includes every continuous isometry coefficient.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.Spectra CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.Primitive

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D] (E : C ≌ D)

/-- The complete ordinary Iso type on the monoidal structure transported through the actual E. -/
def PairIsoType (A B T : D) :=
  letI := Monoidal.transport E
  A ⊗ B ≅ T

/-- Reconstruction of the source tensor retains both complete original equivalence units. -/
def reconstructionIso (P Q : C) :
    letI := Monoidal.transport E
    E.functor.obj P ⊗ E.functor.obj Q ≅ E.functor.obj (P ⊗ Q) := by
  letI := Monoidal.transport E
  exact E.functor.mapIso
    (tensorIso (E.unitIso.app P).symm (E.unitIso.app Q).symm)

/-- Compose the actual source pair with its three actual reconstruction comparisons. -/
def ofIso {P Q R : C} {A B T : D}
    (eP : E.functor.obj P ≅ A) (eQ : E.functor.obj Q ≅ B)
    (eR : E.functor.obj R ≅ T) (e : P ⊗ Q ≅ R) : PairIsoType E A B T := by
  letI := Monoidal.transport E
  exact tensorIso eP.symm eQ.symm ≪≫ reconstructionIso E P Q ≪≫
    E.functor.mapIso e ≪≫ eR

/-- The entire reconstruction carrier map contains the two original inverse unit maps. -/
theorem reconstructionIso_hom (P Q : C) :
    letI := Monoidal.transport E
    (reconstructionIso E P Q).hom =
      E.functor.map ((E.unitIso.inv.app P) ⊗ₘ (E.unitIso.inv.app Q)) := rfl

/-- The entire inverse reconstruction contains both original forward unit maps. -/
theorem reconstructionIso_inv (P Q : C) :
    letI := Monoidal.transport E
    (reconstructionIso E P Q).inv =
      E.functor.map ((E.unitIso.hom.app P) ⊗ₘ (E.unitIso.hom.app Q)) := rfl

/-- The entire native forward map retains both input inverses and the original target map. -/
theorem ofIso_hom {P Q R : C} {A B T : D}
    (eP : E.functor.obj P ≅ A) (eQ : E.functor.obj Q ≅ B)
    (eR : E.functor.obj R ≅ T) (e : P ⊗ Q ≅ R) :
    letI := Monoidal.transport E
    (ofIso E eP eQ eR e).hom =
      (eP.inv ⊗ₘ eQ.inv) ≫
        E.functor.map ((E.unitIso.inv.app P) ⊗ₘ (E.unitIso.inv.app Q)) ≫
          E.functor.map e.hom ≫ eR.hom := by
  let := Monoidal.transport E
  rfl

/-- The entire native inverse retains the original source inverse and both original input maps. -/
theorem ofIso_inv {P Q R : C} {A B T : D}
    (eP : E.functor.obj P ≅ A) (eQ : E.functor.obj Q ≅ B)
    (eR : E.functor.obj R ≅ T) (e : P ⊗ Q ≅ R) :
    letI := Monoidal.transport E
    (ofIso E eP eQ eR e).inv =
      eR.inv ≫ E.functor.map e.inv ≫
        E.functor.map ((E.unitIso.hom.app P) ⊗ₘ (E.unitIso.hom.app Q)) ≫
          (eP.hom ⊗ₘ eQ.hom) := by
  let := Monoidal.transport E
  simp only [ofIso, Iso.trans_inv, Functor.mapIso_inv, reconstructionIso_inv,
    tensorIso_inv, Iso.symm_inv, Category.assoc]

/-- The original unit naturality gives natural reconstruction under both whole source maps. -/
theorem reconstructionIso_naturality {P P' Q Q' : C} (f : P ⟶ P') (g : Q ⟶ Q') :
    letI := Monoidal.transport E
    (E.functor.map f ⊗ₘ E.functor.map g) ≫ (reconstructionIso E P' Q').hom =
      (reconstructionIso E P Q).hom ≫ E.functor.map (f ⊗ₘ g) := by
  let := Monoidal.transport E
  have hp := E.unitIso.inv.naturality f
  have hq := E.unitIso.inv.naturality g
  have ht :
      (E.inverse.map (E.functor.map f) ⊗ₘ E.inverse.map (E.functor.map g)) ≫
          (E.unitIso.inv.app P' ⊗ₘ E.unitIso.inv.app Q') =
        (E.unitIso.inv.app P ⊗ₘ E.unitIso.inv.app Q) ≫ (f ⊗ₘ g) := by
    rw [tensorHom_comp_tensorHom]
    change ((E.functor ⋙ E.inverse).map f ≫ E.unitIso.inv.app P') ⊗ₘ
        ((E.functor ⋙ E.inverse).map g ≫ E.unitIso.inv.app Q') = _
    rw [hp, hq, ← tensorHom_comp_tensorHom]
    rfl
  change E.functor.map _ ≫ E.functor.map _ = E.functor.map _ ≫ E.functor.map _
  rw [← E.functor.map_comp, ← E.functor.map_comp]
  exact congrArg E.functor.map ht


private theorem composeSquare {W : Type uC} [Category.{vC} W]
    {A A' B B' T T' : W} (f : A ⟶ A') (p : A ⟶ B) (p' : A' ⟶ B')
    (g : B ⟶ B') (q : B ⟶ T) (q' : B' ⟶ T') (r : T ⟶ T')
    (hp : f ≫ p' = p ≫ g) (hq : g ≫ q' = q ≫ r) :
    f ≫ (p' ≫ q') = (p ≫ q) ≫ r :=
  (Category.assoc f p' q').symm.trans
    ((congrArg (fun t => t ≫ q') hp).trans
      ((Category.assoc p g q').trans
        ((congrArg (fun t => p ≫ t) hq).trans (Category.assoc p q r).symm)))

/-- All original input, source and target squares preserve the entire reconstructed pair map. -/
theorem ofIso_naturality {P P' Q Q' R R' : C} {A A' B B' T T' : D}
    (f : P ⟶ P') (g : Q ⟶ Q') (r : R ⟶ R')
    (f' : A ⟶ A') (g' : B ⟶ B') (r' : T ⟶ T')
    (eP : E.functor.obj P ≅ A) (eP' : E.functor.obj P' ≅ A')
    (eQ : E.functor.obj Q ≅ B) (eQ' : E.functor.obj Q' ≅ B')
    (eR : E.functor.obj R ≅ T) (eR' : E.functor.obj R' ≅ T')
    (e : P ⊗ Q ≅ R) (e' : P' ⊗ Q' ≅ R')
    (hf : f' ≫ eP'.inv = eP.inv ≫ E.functor.map f)
    (hg : g' ≫ eQ'.inv = eQ.inv ≫ E.functor.map g)
    (hr : E.functor.map r ≫ eR'.hom = eR.hom ≫ r')
    (he : (f ⊗ₘ g) ≫ e'.hom = e.hom ≫ r) :
    letI := Monoidal.transport E
    (f' ⊗ₘ g') ≫ (ofIso E eP' eQ' eR' e').hom =
      (ofIso E eP eQ eR e).hom ≫ r' := by
  let := Monoidal.transport E
  have ht : (f' ⊗ₘ g') ≫ (eP'.inv ⊗ₘ eQ'.inv) =
      (eP.inv ⊗ₘ eQ.inv) ≫ (E.functor.map f ⊗ₘ E.functor.map g) := by
    rw [tensorHom_comp_tensorHom, hf, hg, ← tensorHom_comp_tensorHom]
  have hm := congrArg E.functor.map he
  rw [E.functor.map_comp, E.functor.map_comp] at hm
  have h12 := composeSquare (f' ⊗ₘ g') (eP.inv ⊗ₘ eQ.inv) (eP'.inv ⊗ₘ eQ'.inv)
    (E.functor.map f ⊗ₘ E.functor.map g)
    (reconstructionIso E P Q).hom (reconstructionIso E P' Q').hom
    (E.functor.map (f ⊗ₘ g)) ht (reconstructionIso_naturality E f g)
  have h123 := composeSquare (f' ⊗ₘ g')
    ((eP.inv ⊗ₘ eQ.inv) ≫ (reconstructionIso E P Q).hom)
    ((eP'.inv ⊗ₘ eQ'.inv) ≫ (reconstructionIso E P' Q').hom)
    (E.functor.map (f ⊗ₘ g)) (E.functor.map e.hom) (E.functor.map e'.hom)
    (E.functor.map r) h12 hm
  have h1234 := composeSquare (f' ⊗ₘ g')
    (((eP.inv ⊗ₘ eQ.inv) ≫ (reconstructionIso E P Q).hom) ≫ E.functor.map e.hom)
    (((eP'.inv ⊗ₘ eQ'.inv) ≫ (reconstructionIso E P' Q').hom) ≫ E.functor.map e'.hom)
    (E.functor.map r) eR.hom eR'.hom r' h123 hr
  simpa only [ofIso, Iso.trans_hom, Functor.mapIso_hom, tensorIso_hom,
    Iso.symm_hom, Category.assoc] using h1234

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.Primitive


namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.ModuleStage

universe uV vV uI uJ
open EnrichedFunctorCat
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)]
  [SymmetricCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {J : Type uJ} [EnrichedCategory V J]
  (E : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
  (a : I → J)
  (h : ∀ n, E.functor ⋙ EnrichedFunctorCat.evaluation (a n) ≅
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)

/-- The complete native free pair in the original selected module tensor transported by E. -/
def PairIsoType (n m r : I) (X Y : V) :=
  letI := RightModuleFree.tensorMonoidal S
  letI := Monoidal.transport E
  Free.object (a n) X ⊗ Free.object (a m) Y ≅ Free.object (a r) (X ⊗ Y)

/-- The full source free/evaluation adjunction constructs the actual native free comparison. -/
def sourceComparison (n : I) :
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n ⋙ E.functor ≅
      Free.functor (a n) :=
  FreeAdjunctionSource.operatorIso E (a n)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n) (h n)

/-- Construct the actual stock free pair before any native module-object conversion. -/
def sourcePair (n m r : I) (X Y : V)
    (e : Free.object n X ⊗ Free.object m Y ≅ Free.object r (X ⊗ Y)) :
    SphereSmashFree.Evaluation.PairIsoType S n m r X Y :=
  SphereSmashFree.Evaluation.ofIso S n m r X Y e

/-- The actual relative tensor and original free adjunction reconstruct the complete native pair. -/
def ofIso (n m r : I) (X Y : V)
    (e : Free.object n X ⊗ Free.object m Y ≅ Free.object r (X ⊗ Y)) :
    PairIsoType S E a n m r X Y := by
  letI := RightModuleFree.tensorMonoidal S
  exact Primitive.ofIso E ((sourceComparison S E a h n).app X)
    ((sourceComparison S E a h m).app Y) ((sourceComparison S E a h r).app (X ⊗ Y))
    (sourcePair S n m r X Y e)

/-- The full forward formula retains both complete source units and original adjunction maps. -/
theorem ofIso_hom (n m r : I) (X Y : V)
    (e : Free.object n X ⊗ Free.object m Y ≅ Free.object r (X ⊗ Y)) :
    letI := RightModuleFree.tensorMonoidal S
    letI := Monoidal.transport E
    (ofIso S E a h n m r X Y e).hom =
      ((sourceComparison S E a h n).inv.app X ⊗ₘ
        (sourceComparison S E a h m).inv.app Y) ≫
        E.functor.map
          ((E.unitIso.inv.app
            ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj X)) ⊗ₘ
            (E.unitIso.inv.app
              ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S m).obj Y))) ≫
          E.functor.map (sourcePair S n m r X Y e).hom ≫
            (sourceComparison S E a h r).hom.app (X ⊗ Y) := by
  let := RightModuleFree.tensorMonoidal S
  let := Monoidal.transport E
  exact Primitive.ofIso_hom E ((sourceComparison S E a h n).app X)
    ((sourceComparison S E a h m).app Y) ((sourceComparison S E a h r).app (X ⊗ Y))
    (sourcePair S n m r X Y e)

/-- The full inverse retains the original source inverse, both units and all adjunction inverses. -/
theorem ofIso_inv (n m r : I) (X Y : V)
    (e : Free.object n X ⊗ Free.object m Y ≅ Free.object r (X ⊗ Y)) :
    letI := RightModuleFree.tensorMonoidal S
    letI := Monoidal.transport E
    (ofIso S E a h n m r X Y e).inv =
      (sourceComparison S E a h r).inv.app (X ⊗ Y) ≫
        E.functor.map (sourcePair S n m r X Y e).inv ≫
          E.functor.map
            ((E.unitIso.hom.app
              ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj X)) ⊗ₘ
              (E.unitIso.hom.app
                ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S m).obj Y))) ≫
            ((sourceComparison S E a h n).hom.app X ⊗ₘ
              (sourceComparison S E a h m).hom.app Y) := by
  let := RightModuleFree.tensorMonoidal S
  let := Monoidal.transport E
  exact Primitive.ofIso_inv E ((sourceComparison S E a h n).app X)
    ((sourceComparison S E a h m).app Y) ((sourceComparison S E a h r).app (X ⊗ Y))
    (sourcePair S n m r X Y e)

/-- Each source prequotient coefficient keeps both sphere factors and their actual multiplication. -/
theorem sourcePair_projection (n m r : I) (X Y : V)
    (e : Free.object n X ⊗ Free.object m Y ≅ Free.object r (X ⊗ Y)) :
    letI := RightModuleFree.tensorMonoidal S
    RightModuleFree.relativeTensorπ S
        ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj X)
        ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S m).obj Y) ≫
      (sourcePair S n m r X Y e).hom.hom =
        tensorμ (Free.object n X) S (Free.object m Y) S ≫
          ((Free.object n X ⊗ Free.object m Y) ◁ MonObj.mul (X := S)) ≫ (e.hom ▷ S) := by
  let := RightModuleFree.tensorMonoidal S
  exact SphereSmashFree.Primitive.ofIso_projection S
    (Free.object n X) (Free.object m Y) (Free.object r (X ⊗ Y)) e


/-- Both entire coefficient maps preserve the actual stock source pair. -/
theorem sourcePair_coefficient (n m r : I) {X X' Y Y' : V}
    (f : X ⟶ X') (g : Y ⟶ Y')
    (e : Free.object n X ⊗ Free.object m Y ≅ Free.object r (X ⊗ Y))
    (e' : Free.object n X' ⊗ Free.object m Y' ≅ Free.object r (X' ⊗ Y'))
    (he : SphereSmashFree.Primitive.Compatible (Free.coefficientMap n f)
      (Free.coefficientMap m g) (Free.coefficientMap r (f ⊗ₘ g)) e e') :
    letI := RightModuleFree.tensorMonoidal S
    ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).map f ⊗ₘ
        (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S m).map g) ≫
      (sourcePair S n m r X' Y' e').hom =
        (sourcePair S n m r X Y e).hom ≫
          (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S r).map (f ⊗ₘ g) := by
  let := RightModuleFree.tensorMonoidal S
  exact SphereSmashFree.Primitive.ofIso_naturality S
    (Free.coefficientMap n f) (Free.coefficientMap m g)
    (Free.coefficientMap r (f ⊗ₘ g)) e e' he

/-- The simultaneous original coefficient equation on the reconstructed native free pair. -/
def CoefficientProperty (n m r : I) {X X' Y Y' : V}
    (f : X ⟶ X') (g : Y ⟶ Y')
    (e : Free.object n X ⊗ Free.object m Y ≅ Free.object r (X ⊗ Y))
    (e' : Free.object n X' ⊗ Free.object m Y' ≅ Free.object r (X' ⊗ Y')) : Prop :=
  letI := RightModuleFree.tensorMonoidal S
  letI := Monoidal.transport E
  (Free.coefficientMap (a n) f ⊗ₘ Free.coefficientMap (a m) g) ≫
      (ofIso S E a h n m r X' Y' e').hom =
    (ofIso S E a h n m r X Y e).hom ≫ Free.coefficientMap (a r) (f ⊗ₘ g)

/-- Original Day compatibility and original adjunction naturality give the full native equation. -/
theorem coefficient_spec (n m r : I) {X X' Y Y' : V}
    (f : X ⟶ X') (g : Y ⟶ Y')
    (e : Free.object n X ⊗ Free.object m Y ≅ Free.object r (X ⊗ Y))
    (e' : Free.object n X' ⊗ Free.object m Y' ≅ Free.object r (X' ⊗ Y'))
    (he : SphereSmashFree.Primitive.Compatible (Free.coefficientMap n f)
      (Free.coefficientMap m g) (Free.coefficientMap r (f ⊗ₘ g)) e e') :
    CoefficientProperty S E a h n m r f g e e' := by
  let := RightModuleFree.tensorMonoidal S
  let := Monoidal.transport E
  have hf := (sourceComparison S E a h n).inv.naturality f
  have hg := (sourceComparison S E a h m).inv.naturality g
  have hr := (sourceComparison S E a h r).hom.naturality (f ⊗ₘ g)
  have hp := sourcePair_coefficient S n m r f g e e' he
  exact Primitive.ofIso_naturality E
    ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).map f)
    ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S m).map g)
    ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S r).map (f ⊗ₘ g))
    (Free.coefficientMap (a n) f) (Free.coefficientMap (a m) g)
    (Free.coefficientMap (a r) (f ⊗ₘ g))
    ((sourceComparison S E a h n).app X) ((sourceComparison S E a h n).app X')
    ((sourceComparison S E a h m).app Y) ((sourceComparison S E a h m).app Y')
    ((sourceComparison S E a h r).app (X ⊗ Y))
    ((sourceComparison S E a h r).app (X' ⊗ Y'))
    (sourcePair S n m r X Y e) (sourcePair S n m r X' Y' e') hf hg hr hp

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.ModuleStage


namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.ModuleStage.SymbolicMaps22

universe uV vV uI uJ
open EnrichedFunctorCat
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)]
  [SymmetricCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {J : Type uJ} [EnrichedCategory V J]
  (E : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
  (a : I → J)
  (h : ∀ n, E.functor ⋙ EnrichedFunctorCat.evaluation (a n) ≅
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)

/-- The complete original forward equation for the full source-selected free pair family. -/
def PairIsoHomFamilyType (r : I → I → I)
    (comparison : ∀ (n m : I) (X Y : V),
      Free.object n X ⊗ Free.object m Y ≅ Free.object (r n m) (X ⊗ Y)) : Prop :=
  ∀ (n m : I) (X Y : V),
    letI := RightModuleFree.tensorMonoidal S
    letI := Monoidal.transport E
    (ofIso S E a h n m (r n m) X Y (comparison n m X Y)).hom =
      ((sourceComparison S E a h n).inv.app X ⊗ₘ
        (sourceComparison S E a h m).inv.app Y) ≫
        E.functor.map
          ((E.unitIso.inv.app
            ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj X)) ⊗ₘ
            (E.unitIso.inv.app
              ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S m).obj Y))) ≫
          E.functor.map (sourcePair S n m (r n m) X Y (comparison n m X Y)).hom ≫
            (sourceComparison S E a h (r n m)).hom.app (X ⊗ Y)

/-- The original complete source theorem supplies every original forward comparison at once. -/
abbrev pairIsoHomFamily (r : I → I → I)
    (comparison : ∀ (n m : I) (X Y : V),
      Free.object n X ⊗ Free.object m Y ≅ Free.object (r n m) (X ⊗ Y)) :
    PairIsoHomFamilyType S E a h r comparison :=
  fun n m X Y => ofIso_hom S E a h n m (r n m) X Y (comparison n m X Y)

/-- The complete original inverse equation for the same full source-selected free pair family. -/
def PairIsoInvFamilyType (r : I → I → I)
    (comparison : ∀ (n m : I) (X Y : V),
      Free.object n X ⊗ Free.object m Y ≅ Free.object (r n m) (X ⊗ Y)) : Prop :=
  ∀ (n m : I) (X Y : V),
    letI := RightModuleFree.tensorMonoidal S
    letI := Monoidal.transport E
    (ofIso S E a h n m (r n m) X Y (comparison n m X Y)).inv =
      (sourceComparison S E a h (r n m)).inv.app (X ⊗ Y) ≫
        E.functor.map (sourcePair S n m (r n m) X Y (comparison n m X Y)).inv ≫
          E.functor.map
            ((E.unitIso.hom.app
              ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj X)) ⊗ₘ
              (E.unitIso.hom.app
                ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S m).obj Y))) ≫
            ((sourceComparison S E a h n).hom.app X ⊗ₘ
              (sourceComparison S E a h m).hom.app Y)

/-- The original complete source theorem supplies every original inverse comparison at once. -/
abbrev pairIsoInvFamily (r : I → I → I)
    (comparison : ∀ (n m : I) (X Y : V),
      Free.object n X ⊗ Free.object m Y ≅ Free.object (r n m) (X ⊗ Y)) :
    PairIsoInvFamilyType S E a h r comparison :=
  fun n m X Y => ofIso_inv S E a h n m (r n m) X Y (comparison n m X Y)

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.ModuleStage.SymbolicMaps22

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.ModuleStage.SymbolicCoefficient22

universe uV vV uI uJ
open EnrichedFunctorCat
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)]
  [SymmetricCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {J : Type uJ} [EnrichedCategory V J]
  (E : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
  (a : I → J)
  (h : ∀ n, E.functor ⋙ evaluation (a n) ≅
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)

/-- Every original coefficient and both complete reconstructed pair components occur in this Eq. -/
def EquationFamily
    (t : I → I → I)
    (comparison : ∀ (r s : I) (X Y : V),
      Free.object r X ⊗ Free.object s Y ≅ Free.object (t r s) (X ⊗ Y)) : Prop :=
  ∀ (r s : I) {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y'),
    letI := RightModuleFree.tensorMonoidal S
    letI := Monoidal.transport E
    (Free.coefficientMap (a r) f ⊗ₘ Free.coefficientMap (a s) g) ≫
        (ofIso S E a h r s (t r s) X' Y' (comparison r s X' Y')).hom =
      (ofIso S E a h r s (t r s) X Y (comparison r s X Y)).hom ≫
        Free.coefficientMap (a (t r s)) (f ⊗ₘ g)

/-- The entire original source equation supplies the independently specified Eq family. -/
abbrev ofComparison
    (t : I → I → I)
    (comparison : ∀ (r s : I) (X Y : V),
      Free.object r X ⊗ Free.object s Y ≅ Free.object (t r s) (X ⊗ Y))
    (compatible : ∀ (r s : I) ⦃X X' Y Y' : V⦄ (f : X ⟶ X') (g : Y ⟶ Y'),
      SphereSmashFree.Primitive.Compatible
        (Free.coefficientMap r f) (Free.coefficientMap s g)
        (Free.coefficientMap (t r s) (f ⊗ₘ g))
        (comparison r s X Y) (comparison r s X' Y')) :
    EquationFamily S E a h t comparison :=
  fun r s X X' Y Y' f g =>
    coefficient_spec S E a h r s (t r s) f g
      (comparison r s X Y) (comparison r s X' Y') (compatible r s f g)

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.ModuleStage.SymbolicCoefficient22

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.ModuleStage.SymbolicPair

universe uV vV uI uJ
open EnrichedFunctorCat
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)]
  [SymmetricCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {J : Type uJ} [EnrichedCategory V J]
  (E : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
  (a : I → J)
  (h : ∀ n, E.functor ⋙ EnrichedFunctorCat.evaluation (a n) ≅
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)

/-- The entire reconstructed pair Iso type at the original abstract module boundary. -/
def FamilyType (t : I → I → I) : Type _ :=
  ∀ (n m : I) (X Y : V), PairIsoType S E a n m (t n m) X Y

/-- The full original source constructor supplies every pair Iso and both its maps. -/
def pair (t : I → I → I)
    (comparison : ∀ (n m : I) (X Y : V),
      Free.object n X ⊗ Free.object m Y ≅ Free.object (t n m) (X ⊗ Y)) :
    FamilyType S E a t :=
  fun n m X Y => ofIso S E a h n m (t n m) X Y (comparison n m X Y)

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.ModuleStage.SymbolicPair

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.SelectedPair

universe uV vV uI vI uJ
open EnrichedFunctorCat
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]

/-- All actual source, target, evaluation and Day comparison data for the whole free pair. -/
structure Context (q : Enriched.ModuleMappingR.SelectedSource V I)
    (J : Type uJ) [EnrichedCategory V J] where
  /-- The complete equivalence from the selected source modules to the original enriched target. -/
  sourceEquivalence : q.Module ≌ EnrichedFunctorCat V J
  /-- The original map from source indices to target evaluation indices. -/
  indexMap : I → J
  /-- The whole comparison between target evaluation and source free-module evaluation. -/
  evaluationComparison :
    letI := q.dayMonoidal
    letI := q.coefficientMonObj
    ∀ n, sourceEquivalence.functor ⋙ evaluation (indexMap n) ≅
      CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation q.coefficient n
  /-- The selected original target index for each pair of source indices. -/
  tensorIndex : I → I → I
  /-- The entire original Day free-pair comparison for every pair of indices and coefficients. -/
  diagramPair :
    letI := q.dayMonoidal
    ∀ (n m : I) (X Y : V),
      Free.object n X ⊗ Free.object m Y ≅ Free.object (tensorIndex n m) (X ⊗ Y)
  diagramPairCoefficient :
    letI := q.dayMonoidal
    ∀ (n m : I) ⦃X X' Y Y' : V⦄ (f : X ⟶ X') (g : Y ⟶ Y'),
      SphereSmashFree.Primitive.Compatible
        (Free.coefficientMap n f) (Free.coefficientMap m g)
        (Free.coefficientMap (tensorIndex n m) (f ⊗ₘ g))
        (diagramPair n m X Y) (diagramPair n m X' Y')

variable {q : Enriched.ModuleMappingR.SelectedSource V I}
  {J : Type uJ} [EnrichedCategory V J] (c : Context q J)

open Lean Lean.Meta Lean.Elab Term

/-- Memoize the original source initializer's declared remaining Iso argument
before applying that complete comparison. The independent type and entire
application keep their original expression trees for the normal kernel check. -/
syntax (name := originalSourceProjectionProofSharing)
  "originalSourceProjectionProof% " term:max term:max : term

@[term_elab originalSourceProjectionProofSharing]
private def elabOriginalSourceProjectionProofSharing : TermElab := fun stx expectedType? => do
  let some expectedType := expectedType? |
    throwError "The complete original source projection type must be stated independently"
  let originalType ← instantiateMVars expectedType
  let constructor ← instantiateMVars (← elabTerm stx[1] none)
  unless constructor.getAppFn.isConstOf ``ModuleStage.sourcePair_projection do
    throwError "The original complete source projection initializer changed"
  let declaredSignature ← inferType constructor
  let .forallE _ _ _ _ := declaredSignature |
    throwError "The original complete source comparison argument is absent"
  let comparison ← instantiateMVars (← elabTerm stx[2] none)
  let originalProof := mkApp constructor comparison
  let shared := Lean.ShareCommon.shareCommon (originalType, originalProof)
  unless shared.1 == originalType && shared.2 == originalProof do
    throwError "Sharing changed the entire original projection type or proof expression"
  return shared.2

/-- The complete ordinary native free-pair Iso family on the selected source tensor. -/
def PairIsoType : Type _ :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  ModuleStage.SymbolicPair.FamilyType q.coefficient c.sourceEquivalence c.indexMap c.tensorIndex

/-- The original complete source supplier at its separately stated selected pair type. -/
def pairIso : PairIsoType c := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  exact ModuleStage.SymbolicPair.pair q.coefficient c.sourceEquivalence c.indexMap
    c.evaluationComparison c.tensorIndex c.diagramPair

/-- The complete original hom map formula, including all source units and free comparisons. -/
def HomFormulaType : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  ModuleStage.SymbolicMaps22.PairIsoHomFamilyType q.coefficient c.sourceEquivalence c.indexMap
    c.evaluationComparison c.tensorIndex c.diagramPair

/-- The whole original hom equation supplied at the independent selected formula. -/
theorem hom : HomFormulaType c := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  exact ModuleStage.SymbolicMaps22.pairIsoHomFamily q.coefficient c.sourceEquivalence c.indexMap
    c.evaluationComparison c.tensorIndex c.diagramPair

/-- The complete original inv map formula, including all source units and free comparisons. -/
def InvFormulaType : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  ModuleStage.SymbolicMaps22.PairIsoInvFamilyType q.coefficient c.sourceEquivalence c.indexMap
    c.evaluationComparison c.tensorIndex c.diagramPair

/-- The whole original inv equation supplied at the independent selected formula. -/
theorem inv : InvFormulaType c := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  exact ModuleStage.SymbolicMaps22.pairIsoInvFamily q.coefficient c.sourceEquivalence c.indexMap
    c.evaluationComparison c.tensorIndex c.diagramPair

/-- Both entire native coefficient maps and both actual reconstructed pair components. -/
def CoefficientFormulaType : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  ModuleStage.SymbolicCoefficient22.EquationFamily q.coefficient c.sourceEquivalence c.indexMap
    c.evaluationComparison c.tensorIndex c.diagramPair

/-- The entire original source naturality proves the separately stated full coefficient formula. -/
theorem coefficient : CoefficientFormulaType c := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  exact ModuleStage.SymbolicCoefficient22.ofComparison q.coefficient c.sourceEquivalence c.indexMap
    c.evaluationComparison c.tensorIndex c.diagramPair c.diagramPairCoefficient

/-- The independent full coefficient Eq family with the original public r/s binders. -/
def CoefficientEquationFormulaType : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  ModuleStage.SymbolicCoefficient22.EquationFamily q.coefficient c.sourceEquivalence c.indexMap
    c.evaluationComparison c.tensorIndex c.diagramPair

/-- Both actual pair components satisfy the entire independent coefficient equation. -/
theorem coefficientEquation : CoefficientEquationFormulaType c := coefficient c

/-- The complete prequotient equation on the original free/evaluation source carrier. -/
def SourceProjectionFormulaType : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  letI := RightModuleFree.tensorMonoidal q.coefficient
  ∀ (n m : I) (X Y : V),
    RightModuleFree.relativeTensorπ q.coefficient
        ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free q.coefficient n).obj X)
        ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free q.coefficient m).obj Y) ≫
      (ModuleStage.sourcePair q.coefficient n m (c.tensorIndex n m) X Y
        (c.diagramPair n m X Y)).hom.hom =
      tensorμ (Free.object n X) q.coefficient (Free.object m Y) q.coefficient ≫
        ((Free.object n X ⊗ Free.object m Y) ◁ MonObj.mul (X := q.coefficient)) ≫
        ((c.diagramPair n m X Y).hom ▷ q.coefficient)

/-- The original full source projection theorem supplies every prequotient coefficient. -/
theorem sourceProjection : SourceProjectionFormulaType c := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  let := RightModuleFree.tensorMonoidal q.coefficient
  intro n m X Y
  exact originalSourceProjectionProof%
    (ModuleStage.sourcePair_projection q.coefficient n m (c.tensorIndex n m) X Y)
    (c.diagramPair n m X Y)

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.SelectedPair

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash

/-- The continuous isometry category used by the original orthogonal source. -/
local instance : Category.{v} OrthogonalIndex := SphereSmashStructure.indexCategory.{u, v}
/-- The original direct sum tensor on the continuous orthogonal index. -/
local instance : MonoidalCategory OrthogonalIndex :=
  SphereSmashStructure.indexMonoidalCategory.{u, v}
/-- The pointed continuous enrichment of the original orthogonal index. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  SphereSmashStructure.indexEnrichedOrdinaryCategory.{u, v}
/-- The original block symmetry of the continuous orthogonal index. -/
local instance : SymmetricCategory OrthogonalIndex :=
  SphereSmashStructure.indexSymmetricCategory.{u, v}
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction

/-- Continuous orthogonal spaces with their original enriched Hom actions. -/
abbrev ISpace := EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex
/-- The continuous Day tensor on the original orthogonal spaces. -/
local instance : MonoidalCategory ISpace.{u, v} := SphereSmashStructure.dayMonoidalCategory.{u, v}
/-- The original continuous Day symmetry on orthogonal spaces. -/
local instance : SymmetricCategory ISpace.{u, v} := SphereSmashStructure.daySymmetricCategory.{u, v}
/-- The original representation sphere monoid for the continuous Day tensor. -/
local instance : MonObj sphereISpace.{u, v} := SphereSmashStructure.sphereMonoid.{u, v}
local instance : IsCommMonObj sphereISpace.{u, v} :=
  SphereSmashStructure.sphereCommutativeMonoid.{u, v}
local instance : HasCoequalizers ISpace.{u, v} := SphereSmashStructure.spaceCoequalizers.{u, v}
/-- The relative sphere tensor selected by the complete native factory. -/
local instance : MonoidalCategory NativeSphereModule.Carrier.{u, v} :=
  SphereSmashStructure.monoidalCategory.{u, v}
/-- The native sphere tensor transported through the original source equivalence. -/
local instance : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The original native enriched free spectrum, with its complete continuous operator action. -/
abbrev freeObject (n : OrthogonalIndex) (X : PointedCGWH.{u, v}) :=
  EnrichedFunctorCat.Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) X

/-- The entire original native enriched free functor, with its original coefficient maps. -/
abbrev freeFunctor (n : OrthogonalIndex) :=
  EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
    (OrthogonalOperatorIndex.ofIndex.{u, v} n)

local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}

/-- The entire actual native/source context, including both coefficient naturality maps. -/
def pairData : SelectedPair.Context (SphereSmash.sourceData.{u, v}) OrthogonalOperatorIndex.{u, v} where
  sourceEquivalence := CanonicalSourceSmash.sourceEquivalence.{u, v}
  indexMap := fun i => OrthogonalOperatorIndex.ofIndex.{u, v} i
  evaluationComparison := CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v}
  tensorIndex := SphereSmashFree.tensorIndex.{u, v}
  diagramPair := SphereSmashFree.diagramPair.{u, v}
  diagramPairCoefficient := fun n m {_ _ _ _} f g =>
    SphereSmashFree.Internal.diagramPair_coefficient_spec
      OrthogonalIndex.enrichedMonoidalData.{u, v} n m f g

/-- The entire complete native pair type at the actual typed source context. -/
def PairIsoFormulaType : Type _ := SelectedPair.PairIsoType pairData.{u, v}

/-- The canonical free smash reconstructs the actual right-module pair through the actual E. -/
abbrev pairIso : PairIsoFormulaType.{u, v} := SelectedPair.pairIso pairData.{u, v}

/-- The complete native forward formula, with every original comparison and unit. -/
def PairIsoHomFormulaType : Prop := SelectedPair.HomFormulaType pairData.{u, v}

/-- The complete canonical forward family retains its two source units and original free maps. -/
abbrev pairIsoHom : PairIsoHomFormulaType.{u, v} := SelectedPair.hom pairData.{u, v}

/-- The complete native inverse formula, with every original comparison and unit. -/
def PairIsoInvFormulaType : Prop := SelectedPair.InvFormulaType pairData.{u, v}

/-- The canonical inverse retains the original target inverse and both source units. -/
abbrev pairIsoInv : PairIsoInvFormulaType.{u, v} := SelectedPair.inv pairData.{u, v}

/-- The entire simultaneous native coefficient equation at the actual source context. -/
def PairIsoCoefficientFormulaType : Prop := SelectedPair.CoefficientFormulaType pairData.{u, v}

/-- Every simultaneous original coefficient map preserves the actual canonical free smash. -/
abbrev pairIsoCoefficient : PairIsoCoefficientFormulaType.{u, v} :=
  SelectedPair.coefficient pairData.{u, v}

/-- The full original source prequotient projection formula. -/
def SourcePairProjectionFormulaType : Prop := SelectedPair.SourceProjectionFormulaType pairData.{u, v}

/-- The complete original source quotient coefficients underlying the canonical free comparison. -/
abbrev sourcePairProjection : SourcePairProjectionFormulaType.{u, v} :=
  SelectedPair.sourceProjection pairData.{u, v}

/-- The independently stated full equation on both actual public pair components. -/
def PairIsoCoefficientEquationFormulaType : Prop :=
  SelectedPair.CoefficientEquationFormulaType pairData.{u, v}

/-- Both complete original coefficient maps preserve both complete actual canonical pair components. -/
theorem pairIsoCoefficient_eq : PairIsoCoefficientEquationFormulaType.{u, v} :=
  SelectedPair.coefficientEquation pairData.{u, v}

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash
