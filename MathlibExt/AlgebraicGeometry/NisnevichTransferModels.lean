/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteTransferProductModels
public import MathlibExt.AlgebraicGeometry.NisnevichSiteModels
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Actual Nisnevich presheaves and sheaves with finite transfers

The source category is the cycle category of smooth separated field schemes.
The topology is the native Nisnevich topology induced on those actual schemes.
Transfer sheaves are the full category of additive module-valued functors on
the correspondence category whose graph restriction is a Nisnevich sheaf.

Representables are normalized at every scheme by the actual integral cycle
module, including every correspondence action and every target map.
Transfer sheafification is compared to the native ordinary sheafification
functor on all objects and morphisms, with its actual unit.

References: Mazza--Voevodsky--Weibel, Lectures 2 and 13;
Voevodsky, arXiv:math/0107109v1, §2 pp.3--4.
The native Nisnevich covering and residue-field source ports retain their
Apache provenance in NisnevichSiteModels.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NisnevichTransferModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels

variable {k : Type} [Field k]

def nisnevichTopology : GrothendieckTopology (SmoothScheme k) :=
  schemeFunctor.inducedTopology MathlibExt.NisSource.AlgebraicGeometry.Scheme.nisnevichTopology

abbrev NisModules :=
  Sheaf (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)

variable (D : CompositionSystem k) (G : GraphSystem k)
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]

abbrev TransferPresheaves := (CorrespondenceObject D G)ᵒᵖ ⥤ ModuleCat.{1} ℤ

def graphRestriction (F : TransferPresheaves D G) : (SmoothScheme k)ᵒᵖ ⥤ ModuleCat.{1} ℤ :=
  (graphFunctor D G).op ⋙ F

def IsTransferSheaf : ObjectProperty (TransferPresheaves D G) := fun F =>
  F.Additive ∧ Presheaf.IsSheaf (nisnevichTopology (k := k)) (graphRestriction D G F)

def IsAdditiveTransferPresheaf : ObjectProperty (TransferPresheaves D G) := fun F => F.Additive

abbrev AdditiveTransferPresheaves :=
  (IsAdditiveTransferPresheaf D G).FullSubcategory

abbrev TransferSheaves := (IsTransferSheaf D G).FullSubcategory

def forgetTransfer : TransferSheaves D G ⥤ TransferPresheaves D G :=
  (IsTransferSheaf D G).ι

def forgetNisnevich : TransferSheaves D G ⥤ NisModules (k := k) where
  obj F := ⟨graphRestriction D G F.obj, F.property.2⟩
  map a := ⟨Functor.whiskerLeft (graphFunctor D G).op a.hom⟩

def inclusionAdditive : TransferSheaves D G ⥤ AdditiveTransferPresheaves D G where
  obj F := ⟨F.obj, F.property.1⟩
  map a := ObjectProperty.homMk a.hom

def graphRestrictionFunctor : AdditiveTransferPresheaves D G ⥤ ((SmoothScheme k)ᵒᵖ ⥤ ModuleCat.{1} ℤ) where
  obj F := graphRestriction D G F.obj
  map a := Functor.whiskerLeft (graphFunctor D G).op a.hom

def liftedCycleModule (U X : SmoothScheme k) : ModuleCat.{1} ℤ :=
  ModuleCat.of ℤ (ULift.{1} (Cycles U X))

/-- The genuine represented finite-transfer presheaf, normalized on all cycle elements. -/
structure RepresentableModel (X : CorrespondenceObject D G) where
  object : AdditiveTransferPresheaves D G
  valueIso : ∀ U : CorrespondenceObject D G, object.obj.obj (op U) ≅ liftedCycleModule U.scheme X.scheme
  action_eq : ∀ (U V : CorrespondenceObject D G) (a : V ⟶ U) (b : Cycles U.scheme X.scheme),
    (valueIso V).hom ((object.obj.map a.op) ((valueIso U).inv (ULift.up b))) =
      ULift.up (composeCycles D (show Cycles V.scheme U.scheme from a) b)

/-- Target morphisms are actual postcomposition of the same finite cycle module. -/
structure RepresentableSystem where
  functor : CorrespondenceObject D G ⥤ AdditiveTransferPresheaves D G
  model : ∀ X : CorrespondenceObject D G, RepresentableModel D G X
  object_eq : ∀ X : CorrespondenceObject D G, (model X).object = functor.obj X
  target_eq : ∀ (X Y U : CorrespondenceObject D G) (a : X ⟶ Y) (b : Cycles U.scheme X.scheme),
    ((model Y).valueIso U).hom
      ((eqToHom (object_eq X) ≫ functor.map a ≫ eqToHom (object_eq Y).symm).hom.app (op U)
        (((model X).valueIso U).inv (ULift.up b))) =
      ULift.up (composeCycles D b (show Cycles X.scheme Y.scheme from a))

/-- Transfer sheafification has the fixed native ordinary sheafification and its unit. -/
structure TransferSheafificationModel
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] where
  functor : AdditiveTransferPresheaves D G ⥤ TransferSheaves D G
  adjunction : functor ⊣ inclusionAdditive D G
  underlyingIso : functor ⋙ forgetNisnevich D G ≅
    graphRestrictionFunctor D G ⋙
      presheafToSheaf (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)
  unit_eq : ∀ F : AdditiveTransferPresheaves D G,
    Functor.whiskerLeft (graphFunctor D G).op (adjunction.unit.app F).hom ≫
      (sheafToPresheaf (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)).map (underlyingIso.app F).hom =
    (sheafificationAdjunction (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)).unit.app
      (graphRestriction D G F.obj)

def ztr [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (R : RepresentableSystem D G) (S : TransferSheafificationModel D G)
    (X : CorrespondenceObject D G) : TransferSheaves D G :=
  S.functor.obj (R.functor.obj X)

/-- A transfer sheaf's derived operations use the same actual Nisnevich module sheaf. -/
def ztrNis [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (R : RepresentableSystem D G) (S : TransferSheafificationModel D G)
    (X : CorrespondenceObject D G) : NisModules (k := k) :=
  (forgetNisnevich D G).obj (ztr D G R S X)

end MathlibExt.AlgebraicGeometry.NisnevichTransferModels
