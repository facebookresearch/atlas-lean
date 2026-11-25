/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import MathlibExt.AlgebraicGeometry.EtaleLocalAcyclicityModels
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Native derived constant/global-section evaluation

The constant functor is Mathlib's sheafification of the literal constant
module presheaf. Its ordinary adjunction is the native terminal-section
adjunction. A derived adjunction is fixed on every cochain by that ordinary
unit and both native right-derived units. Thus its evaluation counit cannot
be independently rescaled.

The evaluation arrow Delta_Y RΓ(X,F) → Rf_*F uses the same native units,
the constant pullback mate of the global-section pushforward comparison,
and that source-normalized counit. Its cone is formed over the base before
any geometric generic stalk is taken.

Sources: Saito, arXiv:1510.03018v4, Section 1.1; Mathlib ConstantSheaf.lean
and the generic exact-derived adjunction construction. No unrelated
vanishing representation or cohomology space is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EtaleConstantDerivedModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open AdicDerivedContracts ProEtaleCohomologyFunctoriality

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ]

def constantFunctor (X : Scheme.{0}) : ModuleCat.{1} Λ ⥤ ModuleSheaf Λ X :=
  constantSheaf (ProEt.topology X) (ModuleCat.{1} Λ)

def constantAdjunction (X : Scheme.{0}) : constantFunctor Λ X ⊣ sections Λ X :=
  constantSheafAdj (ProEt.topology X) (ModuleCat.{1} Λ) terminalIsTerminal

instance constant_additive (X : Scheme.{0}) : (constantFunctor Λ X).Additive := by
  dsimp only [constantFunctor, constantSheaf]
  infer_instance

def derivedConstant (X : Scheme.{0}) :
    DerivedCategory.Plus (ModuleCat.{1} Λ) ⥤ Derived Λ X :=
  (constantFunctor Λ X).rightDerivedFunctorPlus

def cochainConstantUnit (X : Scheme.{0}) :
    𝟭 (CochainComplex.Plus (ModuleCat.{1} Λ)) ⟶
      (constantFunctor Λ X).mapCochainComplexPlus ⋙ (sections Λ X).mapCochainComplexPlus where
  app K := ObjectProperty.homMk
    { f n := (constantAdjunction Λ X).unit.app (K.obj.X n)
      comm' i j _ := ((constantAdjunction Λ X).unit.naturality (K.obj.d i j)).symm }
  naturality K L f := by
    apply ObjectProperty.hom_ext
    ext n x
    exact ConcreteCategory.congr_hom
      ((constantAdjunction Λ X).unit.naturality (f.hom.f n)) x

def derivedConstantUnit (X : Scheme.{0}) (K : CochainComplex.Plus (ModuleCat.{1} Λ)) :
    DerivedCategory.Plus.Q.obj K ⟶
      (derivedSections Λ X).obj ((derivedConstant Λ X).obj (DerivedCategory.Plus.Q.obj K)) :=
  DerivedCategory.Plus.Q.map ((cochainConstantUnit Λ X).app K) ≫
    (sections Λ X).rightDerivedFunctorPlusUnit.app
      ((constantFunctor Λ X).mapCochainComplexPlus.obj K) ≫
    (derivedSections Λ X).map ((constantFunctor Λ X).rightDerivedFunctorPlusUnit.app K)

/-- A generic derived adjunction fixed on every actual cochain unit. -/
class DerivedConstantAdjunction (X : Scheme.{0}) where
  adjunction : derivedConstant Λ X ⊣ derivedSections Λ X
  normalized : ∀ K : CochainComplex.Plus (ModuleCat.{1} Λ),
    adjunction.unit.app (DerivedCategory.Plus.Q.obj K) = derivedConstantUnit Λ X K

variable [DerivedFunctorTheory Λ]

def constantPullbackIso {X Y : Scheme.{0}} (f : X ⟶ Y)
    [DerivedConstantAdjunction Λ X] [DerivedConstantAdjunction Λ Y] :
    derivedConstant Λ Y ⋙ derivedPullback Λ f ≅ derivedConstant Λ X :=
  (((DerivedConstantAdjunction.adjunction (Λ := Λ) (X := Y)).comp
    (DerivedAdjunction.adjunction (R := Λ) (f := f))).ofNatIsoRight
      (GlobalSectionsPushforward.comparison (R := Λ) (f := f))).leftAdjointUniq
        (DerivedConstantAdjunction.adjunction (Λ := Λ) (X := X))

/-- The exact base-sheaf evaluation of the same global-section complex. -/
def evaluationArrow {X Y : Scheme.{0}} (f : X ⟶ Y) (F : Derived Λ X)
    [DerivedConstantAdjunction Λ X] [DerivedConstantAdjunction Λ Y] :
    (derivedConstant Λ Y).obj ((derivedSections Λ X).obj F) ⟶
      (derivedPushforward Λ f).obj F :=
  (DerivedAdjunction.adjunction (R := Λ) (f := f)).unit.app _ ≫
    (derivedPushforward Λ f).map ((constantPullbackIso Λ f).hom.app
      ((derivedSections Λ X).obj F)) ≫
    (derivedPushforward Λ f).map
      ((DerivedConstantAdjunction.adjunction (Λ := Λ) (X := X)).counit.app F)

/-- A native cochain enhancement of the base evaluation arrow. Its cone is
formed in the base's sheaf category, preserving field Galois descent. -/
structure BaseVanishingModel {X Y : Scheme.{0}} (f : X ⟶ Y) (F : Derived Λ X)
    [DerivedConstantAdjunction Λ X] [DerivedConstantAdjunction Λ Y] where
  source : Cochains Λ Y
  target : Cochains Λ Y
  sourceIso : DerivedCategory.Plus.Q.obj source ≅
    (derivedConstant Λ Y).obj ((derivedSections Λ X).obj F)
  targetIso : DerivedCategory.Plus.Q.obj target ≅ (derivedPushforward Λ f).obj F
  arrow : source ⟶ target
  normalized : DerivedCategory.Plus.Q.map arrow ≫ targetIso.hom =
    sourceIso.hom ≫ evaluationArrow Λ f F
  boundedCone : ∃ n : ℤ, (CochainComplex.mappingCone arrow.hom).IsStrictlyGE n

def BaseVanishingModel.object {X Y : Scheme.{0}} {f : X ⟶ Y} {F : Derived Λ X}
    [DerivedConstantAdjunction Λ X] [DerivedConstantAdjunction Λ Y]
    (V : BaseVanishingModel Λ f F) : Derived Λ Y :=
  DerivedCategory.Plus.Q.obj ⟨CochainComplex.mappingCone V.arrow.hom, V.boundedCone⟩

/-- The actual generic-field sheaf cone, before taking its geometric stalk. -/
def BaseVanishingModel.generic {X Y : Scheme.{0}} {f : X ⟶ Y} {F : Derived Λ X}
    [DerivedConstantAdjunction Λ X] [DerivedConstantAdjunction Λ Y]
    (V : BaseVanishingModel Λ f F) (K : Type) [Field K] (j : Spec (.of K) ⟶ Y) :
    Derived Λ (Spec (.of K)) := (derivedPullback Λ j).obj V.object

end MathlibExt.AlgebraicGeometry.EtaleConstantDerivedModels
