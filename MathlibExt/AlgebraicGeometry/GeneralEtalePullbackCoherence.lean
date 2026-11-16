/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralEtaleDerivedEnhancements
public import MathlibExt.AlgebraicGeometry.EtaleComplexesPullbackCoherence
public import Mathlib.CategoryTheory.Bicategory.Grothendieck

/-!
# Canonical constant-Λ étale pullback coherence

Site identities use the existing actual étale unit source and composition
uses native pullback pasting. Direct-image comparisons are native continuous
site comparisons. Inverse-image identities/compositors are their native
adjunction mates, and their cochain action is the native mapHomologicalComplex
comparison. No O-linear or commutative coefficient restriction is introduced.

The normalized pseudofunctor source fixes objects, every cochain functor,
unit and compositor. Its native Grothendieck category will supply the
full weak-equivalence localization underlying coherent derived pullbacks.
Arc/hypercover descent is not a field of this source.

Source: Bhatt--Mathew arXiv:1807.04725v4, Notation 5.8;
native Mathlib sites, adjunction mates and Grothendieck construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralEtalePullbackCoherence

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open GeneralArcCoverModels GeneralEtaleCoefficientModels
open ClassicalComplexesSourceModels EtaleComplexesPullbackCoherence
open scoped CategoryTheory.Bicategory

variable (Λ : Type) [Ring Λ]
  [∀ X : Scheme.{0}, HasSheafify X.smallEtaleTopology (ModuleCat.{1} Λ)]
  (S : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y), EtalePullbackSource Λ f)
  (U : ∀ X : Scheme.{0}, EtaleBaseChangeUnitSource X)

/-- The native inverse/direct-image adjunction on the actual left modules. -/
def adjunction {X Y : Scheme.{0}} (f : X ⟶ Y) :
    pullback Λ (S f) ⊣ pushforward Λ (S f) :=
  letI : (etaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
    (S f).continuous
  letI : ((etaleBaseChange f).sheafPushforwardContinuous
    (ModuleCat.{1} Λ) Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint :=
    (S f).rightAdjoint
  Functor.sheafAdjunctionContinuous (etaleBaseChange f)
    (ModuleCat.{1} Λ) Y.smallEtaleTopology X.smallEtaleTopology

/-- Identity direct image is fixed by the prescribed native site unit. -/
def pushforwardId (X : Scheme.{0}) :
    pushforward Λ (S (𝟙 X)) ≅ 𝟭 (CoefficientSheaves Λ X) :=
  letI : (etaleBaseChange (𝟙 X)).IsContinuous X.smallEtaleTopology X.smallEtaleTopology :=
    (S (𝟙 X)).continuous
  Functor.sheafPushforwardContinuousId' (U X).iso
    (ModuleCat.{1} Λ) X.smallEtaleTopology

/-- Native continuous-site pushforward composition, on every test module map. -/
def pushforwardComp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforward Λ (S f) ⋙ pushforward Λ (S g) ≅ pushforward Λ (S (f ≫ g)) :=
  letI : (etaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
    (S f).continuous
  letI : (etaleBaseChange g).IsContinuous Z.smallEtaleTopology Y.smallEtaleTopology :=
    (S g).continuous
  letI : (etaleBaseChange (f ≫ g)).IsContinuous Z.smallEtaleTopology X.smallEtaleTopology :=
    (S (f ≫ g)).continuous
  Functor.sheafPushforwardContinuousComp' (etaleBaseChangeComp f g).symm
    (ModuleCat.{1} Λ) Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

/-- Inverse-image identity is the native mate of that same direct-image unit. -/
def pullbackId (X : Scheme.{0}) :
    pullback Λ (S (𝟙 X)) ≅ 𝟭 (CoefficientSheaves Λ X) :=
  (adjunction (Λ := Λ) (S := S) (𝟙 X)).leftAdjointIdIso
    (pushforwardId (Λ := Λ) (S := S) (U := U) X)

/-- Inverse-image composition is the native adjunction mate of pullback pasting. -/
def pullbackComp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback Λ (S g) ⋙ pullback Λ (S f) ≅ pullback Λ (S (f ≫ g)) :=
  Adjunction.leftAdjointCompIso (adjunction Λ S g) (adjunction Λ S f)
    (adjunction Λ S (f ≫ g)) (pushforwardComp Λ S f g)

/-- The unit mate on all actual cochain terms and differentials. -/
def complexId (X : Scheme.{0}) :
    complexPullback Λ (S (𝟙 X)) ≅ 𝟭 (CoefficientComplexes Λ X) :=
  NatIso.mapHomologicalComplex (pullbackId (Λ := Λ) (S := S) (U := U) X)
    (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)

/-- The same composition mate on all actual cochain maps. -/
def complexComp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    complexPullback Λ (S g) ⋙ complexPullback Λ (S f) ≅
      complexPullback Λ (S (f ≫ g)) :=
  Functor.mapHomologicalComplexCompIso (pullbackComp Λ S f g) (ComplexShape.up ℤ)

/-- A full ordinary coefficient pseudofunctor with its entire source
data fixed by native sheaf inverse image and the specified mates.
All higher weak-equivalence localization is constructed from this source. -/
structure CoefficientPseudofunctorSource where
  functor : LocallyDiscrete QcqsSchemeᵒᵖ ⥤ᵖ Cat.{1, 2}
  object : ∀ X : QcqsSchemeᵒᵖ,
    functor.obj ⟨X⟩ = Cat.of (CoefficientComplexes Λ X.unop.scheme)
  transport : ∀ {X Y : QcqsSchemeᵒᵖ} (f : X ⟶ Y),
    HEq (functor.map f.toLoc).toFunctor (complexPullback Λ (S f.unop))
  identity : ∀ X : QcqsSchemeᵒᵖ,
    HEq ((functor.mapId ⟨X⟩).hom.toNatTrans)
      (complexId (Λ := Λ) (S := S) (U := U) X.unop.scheme).hom
  composition : ∀ {X Y Z : QcqsSchemeᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z),
    HEq ((functor.mapComp f.toLoc g.toLoc).hom.toNatTrans)
      (complexComp Λ S g.unop f.unop).inv

/-- The actual native Grothendieck category of complexes and base-change maps. -/
abbrev CoefficientFamilies (C : CoefficientPseudofunctorSource Λ S U) :=
  Pseudofunctor.Grothendieck C.functor

/-- Its native projection retains every actual qcqs base arrow. -/
def familyProjection (C : CoefficientPseudofunctorSource Λ S U) :
    CoefficientFamilies Λ S U C ⥤ QcqsSchemeᵒᵖ :=
  Pseudofunctor.Grothendieck.forget C.functor

end MathlibExt.AlgebraicGeometry.GeneralEtalePullbackCoherence
