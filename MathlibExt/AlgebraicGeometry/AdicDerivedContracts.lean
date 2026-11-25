/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/ProEtale/SiteFunctoriality/MorphismComposition.lean`
(AxiomMath/Stacks, revision c496df0d9beea9deaeabcea8492605f9a0a2313b), for the comparisons of base
change and composition:
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: small pro-étale sites and sheaves of modules from
`ProEtaleCohomologyFunctoriality`.
-/

module

public import MathlibExt.AlgebraicGeometry.AdicLinearFunctoriality
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject

/-!
# Derived functors on the pro-étale site and nearby cycles

All categories are sheaves of `R`-modules on small pro-étale sites, and `Derived R X` is the
bounded-below derived category. Derived inverse image, direct image and global sections are
Mathlib's right derived functors (`Functor.rightDerivedFunctorPlus`). Inverse image is exact, so
its derived unit is an isomorphism (`pullbackDerivedNormalization`).

The classes `DerivedPullbackPasting`, `DerivedAdjunction` and `GlobalSectionsPushforward` specify
the composition of derived inverse images, the adjunction between derived inverse and direct
image, and the comparison of derived global sections with derived direct image, each normalized by
the corresponding underived map on every complex. The first always holds
(`derivedPullbackPasting`); the other two are hypotheses of the constructions that use them, and
their constructions are tracked as the `def_wanted` requests `derivedAdjunction` and
`globalSectionsPushforward` in `WantedExt.AlgebraicGeometry.AdicDerivedComparisonsWanted`.

For an open immersion `j` and a closed immersion `i` into the same scheme, the nearby object is
`i^* Rj_*` of the continuous coefficients, specialization is the map from the coefficients
induced by the adjunction units, and a cochain model of specialization has a vanishing object,
the mapping cone.

References: Bhatt--Scholze, *The pro-etale topology for schemes*, section
6.8; SGA 7 I, section 2; Illusie, Astérisque 223, Exposé I, section 3.1.
https://arxiv.org/abs/1309.1198
https://www.numdam.org/item/AST_1994__223__9_0/
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.AdicDerivedContracts

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open ContinuousAdicCoefficients ProEtaleCohomologyFunctoriality

attribute [local instance] HasDerivedCategory.standard

variable (R : Type) [CommRing R]

/-- Sheaves of `R`-modules on the small pro-étale site of `X`. -/
abbrev ModuleSheaf (X : Scheme) := CoefficientSheaf X R

/-- Bounded-below cochain complexes of sheaves of modules. -/
abbrev Cochains (X : Scheme) := CochainComplex.Plus (ModuleSheaf R X)

/-- The bounded-below derived category of sheaves of modules. -/
abbrev Derived (X : Scheme) := DerivedCategory.Plus (ModuleSheaf R X)

/-- Global sections: sections over the terminal object of the small pro-étale site. -/
abbrev sections (X : Scheme) : ModuleSheaf R X ⥤ ModuleCat.{1} R :=
  (sheafSections (ProEt.topology X) (ModuleCat.{1} R)).obj (op (⊤_ X.ProEt))

instance sections_additive (X : Scheme) : (sections R X).Additive where
  map_add := rfl

/-- Derived global sections. -/
def derivedSections (X : Scheme) :
    Derived R X ⥤ DerivedCategory.Plus (ModuleCat.{1} R) :=
  (sections R X).rightDerivedFunctorPlus

/-- Derived inverse image. -/
def derivedPullback {Y X : Scheme} (f : Y ⟶ X) :
    Derived R X ⥤ Derived R Y :=
  (pullback R f).rightDerivedFunctorPlus

/-- Derived direct image. -/
def derivedPushforward {Y X : Scheme} (f : Y ⟶ X) :
    Derived R Y ⥤ Derived R X :=
  (pushforward R f).rightDerivedFunctorPlus

/-- A sheaf as a complex concentrated in degree zero. -/
def singleCochain {X : Scheme} (F : ModuleSheaf R X) : Cochains R X :=
  ⟨(CochainComplex.singleFunctor (ModuleSheaf R X) 0).obj F,
    ⟨0, inferInstance⟩⟩

/-- A sheaf as an object of the derived category, in degree zero. -/
def single {X : Scheme} (F : ModuleSheaf R X) : Derived R X :=
  DerivedCategory.Plus.Q.obj (singleCochain R F)

/-- The ordinary single-complex functor with its explicit strict bound. -/
def singleCochainFunctor (X : Scheme) :
    ModuleSheaf R X ⥤ Cochains R X where
  obj F := singleCochain R F
  map a := ObjectProperty.homMk
    ((CochainComplex.singleFunctor (ModuleSheaf R X) 0).map a)
  map_id F := by
    apply ObjectProperty.hom_ext
    exact (CochainComplex.singleFunctor (ModuleSheaf R X) 0).map_id F
  map_comp a b := by
    apply ObjectProperty.hom_ext
    exact (CochainComplex.singleFunctor (ModuleSheaf R X) 0).map_comp a b

/-- The map of single complexes induced by a map of sheaves. -/
def singleMap {X : Scheme} {F G : ModuleSheaf R X} (a : F ⟶ G) :
    single R F ⟶ single R G :=
  (singleCochainFunctor R X ⋙ DerivedCategory.Plus.Q).map a

instance singleMap_isIso {X : Scheme} {F G : ModuleSheaf R X}
    (a : F ⟶ G) [IsIso a] : IsIso (singleMap R a) := by
  dsimp only [singleMap]
  infer_instance

/-- The unit of the ordinary inverse/direct-image adjunction on cochains. -/
def cochainUnit {Y X : Scheme} (f : Y ⟶ X) :
    𝟭 (Cochains R X) ⟶
      (pullback R f).mapCochainComplexPlus ⋙
        (pushforward R f).mapCochainComplexPlus where
  app K := ObjectProperty.homMk
    (((pullbackAdjunction R f).unit.mapHomologicalComplex (.up ℤ)).app K.obj)
  naturality K L a := by
    apply ObjectProperty.hom_ext
    exact ((pullbackAdjunction R f).unit.mapHomologicalComplex
      (.up ℤ)).naturality a.hom

/-- The expected unit of the derived adjunction on a complex `K`: the underived unit followed by
the derived units of direct and inverse image. -/
def normalizedDerivedUnit {Y X : Scheme} (f : Y ⟶ X)
    (K : Cochains R X) :
    DerivedCategory.Plus.Q.obj K ⟶
      (derivedPushforward R f).obj
        ((derivedPullback R f).obj (DerivedCategory.Plus.Q.obj K)) :=
  DerivedCategory.Plus.Q.map ((cochainUnit R f).app K) ≫
    (pushforward R f).rightDerivedFunctorPlusUnit.app
      ((pullback R f).mapCochainComplexPlus.obj K) ≫
    (derivedPushforward R f).map
      ((pullback R f).rightDerivedFunctorPlusUnit.app K)

/-- The derived unit of inverse image along `f` is an isomorphism on every complex: the derived
inverse image is computed degreewise. Always true (`pullbackDerivedNormalization`). -/
class PullbackDerivedNormalization {Y X : Scheme} (f : Y ⟶ X) : Prop where
  unit_isIso (K : Cochains R X) :
    IsIso ((pullback R f).rightDerivedFunctorPlusUnit.app K)

attribute [instance] PullbackDerivedNormalization.unit_isIso

/-- Inverse image is exact, so it preserves quasi-isomorphisms and its right derived functor is
computed by applying it degreewise: the derived unit is an isomorphism. -/
instance pullbackDerivedNormalization {Y X : Scheme} (f : Y ⟶ X) :
    PullbackDerivedNormalization R f where
  unit_isIso K := by
    have hF : (CochainComplex.Plus.quasiIso (ModuleSheaf R X)).IsInvertedBy
        ((pullback R f).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) := by
      intro K L φ hφ
      rw [CochainComplex.Plus.quasiIso_iff] at hφ
      refine Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso _) _ ?_
      rw [CochainComplex.Plus.quasiIso_iff]
      change QuasiIso (((pullback R f).mapHomologicalComplex _).map φ.hom)
      infer_instance
    have := Functor.isIso_of_isRightDerivedFunctor_of_inverts _
      (pullback R f).rightDerivedFunctorPlusUnit hF
    infer_instance

/-- An adjunction between derived inverse and direct image along `f`, on the bounded-below derived
categories of pro-étale sheaves of `R`-modules, whose unit on every bounded-below complex is the
expected one, `normalizedDerivedUnit`: the underived unit followed by the derived units of direct
and inverse image. -/
class DerivedAdjunction {Y X : Scheme} (f : Y ⟶ X) where
  adjunction : derivedPullback R f ⊣ derivedPushforward R f
  unit_normalization : ∀ K : Cochains R X,
    adjunction.unit.app (DerivedCategory.Plus.Q.obj K) =
      normalizedDerivedUnit R f K

/-- An additive functor applied to a single complex is the single complex of its value. -/
def singleCochainComparison {Y X : Scheme}
    (F : ModuleSheaf R Y ⥤ ModuleSheaf R X) [F.Additive]
    (A : ModuleSheaf R Y) :
    F.mapCochainComplexPlus.obj (singleCochain R A) ≅
      singleCochain R (F.obj A) :=
  (CochainComplex.Plus.fullyFaithfulι (ModuleSheaf R X)).preimageIso
    ((F.mapCochainComplexSingleFunctor 0).app A)

/-- The fixed derived unit on a sheaf, through the single-complex comparison. -/
def pullbackUnitOfSheaf {Y X : Scheme} (f : Y ⟶ X)
    (A : ModuleSheaf R X) :
    single R ((pullback R f).obj A) ⟶
      (derivedPullback R f).obj (single R A) :=
  (DerivedCategory.Plus.Q.mapIso
    (singleCochainComparison R (pullback R f) A)).inv ≫
      (pullback R f).rightDerivedFunctorPlusUnit.app (singleCochain R A)

instance pullbackUnitOfSheaf_isIso {Y X : Scheme} (f : Y ⟶ X)
    [PullbackDerivedNormalization R f] (A : ModuleSheaf R X) :
    IsIso (pullbackUnitOfSheaf R f A) := by
  dsimp [pullbackUnitOfSheaf]
  infer_instance

/-- The derived map `A ⟶ Rf_* B` induced by a map of sheaves `A ⟶ f_* B`. -/
def pushforwardFromSheaf {Y X : Scheme} (f : Y ⟶ X)
    {A : ModuleSheaf R X} {B : ModuleSheaf R Y}
    (a : A ⟶ (pushforward R f).obj B) :
    single R A ⟶ (derivedPushforward R f).obj (single R B) :=
  singleMap R a ≫
    (DerivedCategory.Plus.Q.mapIso
      (singleCochainComparison R (pushforward R f) B)).inv ≫
        (pushforward R f).rightDerivedFunctorPlusUnit.app (singleCochain R B)

/-- Base change along `g` and then `f` is base change along `f ≫ g`. -/
def baseChangeComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseChange g ⋙ baseChange f ≅ baseChange (f ≫ g) :=
  Functor.fullyFaithfulCancelRight (ProEt.forget X)
    (Functor.isoWhiskerLeft (ProEt.forget Z) (Over.pullbackComp f g).symm)

/-- Direct images compose. -/
def pushforwardComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforward R f ⋙ pushforward R g ≅ pushforward R (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (baseChangeComp f g)
    (ModuleCat.{1} R) (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)

/-- Inverse images compose: the mate of the composition of direct images. -/
def pullbackComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback R g ⋙ pullback R f ≅ pullback R (f ≫ g) :=
  (((pullbackAdjunction R g).comp (pullbackAdjunction R f)).ofNatIsoRight
    (pushforwardComp R f g)).leftAdjointUniq (pullbackAdjunction R (f ≫ g))

/-- Composition of inverse images, applied degreewise to complexes. -/
def cochainPullbackComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : Cochains R Z) :
    (pullback R f).mapCochainComplexPlus.obj
        ((pullback R g).mapCochainComplexPlus.obj K) ≅
      (pullback R (f ≫ g)).mapCochainComplexPlus.obj K :=
  (CochainComplex.Plus.fullyFaithfulι (ModuleSheaf R X)).preimageIso
    ((Functor.mapHomologicalComplexCompIso (pullbackComp R f g) (.up ℤ)).app
      K.obj)

/-- The composite of the derived units of two inverse images on a complex. -/
def compositePullbackUnit {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : Cochains R Z) :
    DerivedCategory.Plus.Q.obj
        ((pullback R f).mapCochainComplexPlus.obj
          ((pullback R g).mapCochainComplexPlus.obj K)) ⟶
      (derivedPullback R f).obj
        ((derivedPullback R g).obj (DerivedCategory.Plus.Q.obj K)) :=
  (pullback R f).rightDerivedFunctorPlusUnit.app
      ((pullback R g).mapCochainComplexPlus.obj K) ≫
    (derivedPullback R f).map
      ((pullback R g).rightDerivedFunctorPlusUnit.app K)

/-- An isomorphism between the composite of derived inverse images along `g` and `f` and the
derived inverse image along `f ≫ g`, compatible on every complex with the composition of the
underived inverse images. It always exists (`derivedPullbackPasting`). -/
class DerivedPullbackPasting {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) where
  comparison : derivedPullback R g ⋙ derivedPullback R f ≅
    derivedPullback R (f ≫ g)
  normalized : ∀ K : Cochains R Z,
    compositePullbackUnit R f g K ≫
        comparison.hom.app (DerivedCategory.Plus.Q.obj K) =
      (DerivedCategory.Plus.Q.mapIso (cochainPullbackComp R f g K)).hom ≫
        (pullback R (f ≫ g)).rightDerivedFunctorPlusUnit.app K

/-- Composition of inverse images on bounded-below complexes, as a natural isomorphism. -/
def cochainPullbackCompIso {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullback R g).mapCochainComplexPlus ⋙ (pullback R f).mapCochainComplexPlus ≅
      (pullback R (f ≫ g)).mapCochainComplexPlus :=
  NatIso.ofComponents (cochainPullbackComp R f g) (fun {K L} φ => by
    apply ObjectProperty.hom_ext
    exact (Functor.mapHomologicalComplexCompIso (pullbackComp R f g) (.up ℤ)).hom.naturality
      φ.hom)

/-- Derived inverse images compose (Stacks, Tag 0D6D). Inverse images are exact, so their derived
units are isomorphisms and the comparison descends through the localization from the composition
of inverse images on complexes. -/
noncomputable instance derivedPullbackPasting {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    DerivedPullbackPasting R f g := by
  have : IsIso (pullback R f).rightDerivedFunctorPlusUnit := NatIso.isIso_of_isIso_app _
  have : IsIso (pullback R g).rightDerivedFunctorPlusUnit := NatIso.isIso_of_isIso_app _
  have : IsIso (pullback R (f ≫ g)).rightDerivedFunctorPlusUnit := NatIso.isIso_of_isIso_app _
  let uf := asIso (pullback R f).rightDerivedFunctorPlusUnit
  let ug := asIso (pullback R g).rightDerivedFunctorPlusUnit
  let ufg := asIso (pullback R (f ≫ g)).rightDerivedFunctorPlusUnit
  let e : DerivedCategory.Plus.Q ⋙ (derivedPullback R g ⋙ derivedPullback R f) ≅
      DerivedCategory.Plus.Q ⋙ derivedPullback R (f ≫ g) :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ug.symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ uf.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (cochainPullbackCompIso R f g) _ ≪≫ ufg
  let W := Localization.whiskeringLeftFunctor' DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf R Z)) (Derived R X)
  exact
    { comparison := W.preimageIso e
      normalized := fun K => by
        have h : (W.preimageIso e).hom.app (DerivedCategory.Plus.Q.obj K) = e.hom.app K :=
          NatTrans.congr_app (W.map_preimage e.hom) K
        rw [h]
        simp only [e, uf, ug, ufg, compositePullbackUnit, Iso.trans_hom, Iso.symm_hom,
          NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
          Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
          Functor.associator_inv_app, asIso_hom, asIso_inv, Category.id_comp, Category.assoc,
          Functor.mapIso_hom]
        rw [← Functor.map_comp_assoc]
        simp [cochainPullbackCompIso, derivedPullback] }

/-- The comparison of derived inverse images around a commutative square of schemes. -/
def pullbackSquare {X' X Y' Y : Scheme}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (comm : g' ≫ f = f' ≫ g)
    [DerivedPullbackPasting R f' g] [DerivedPullbackPasting R g' f] :
    derivedPullback R g ⋙ derivedPullback R f' ≅
      derivedPullback R f ⋙ derivedPullback R g' :=
  (DerivedPullbackPasting.comparison (R := R) (f := f') (g := g)) ≪≫
    eqToIso (congrArg (derivedPullback R) comm.symm) ≪≫
      (DerivedPullbackPasting.comparison (R := R) (f := g') (g := f)).symm

/-- The base-change map `g^* Rf_* ⟶ Rf'_* g'^*`: the mate of that comparison under the derived
adjunctions. -/
def baseChangeMap {X' X Y' Y : Scheme}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (comm : g' ≫ f = f' ≫ g)
    [DerivedAdjunction R f'] [DerivedAdjunction R f]
    [DerivedPullbackPasting R f' g] [DerivedPullbackPasting R g' f]
    (K : Derived R X) :
    (derivedPullback R g).obj ((derivedPushforward R f).obj K) ⟶
      (derivedPushforward R f').obj ((derivedPullback R g').obj K) :=
  (DerivedAdjunction.adjunction (R := R) (f := f')).unit.app _ ≫
    (derivedPushforward R f').map
      ((pullbackSquare R g' f' f g comm).hom.app
        ((derivedPushforward R f).obj K)) ≫
    (derivedPushforward R f').map
      ((derivedPullback R g').map
        ((DerivedAdjunction.adjunction (R := R) (f := f)).counit.app K))

/-- Global sections of `f_* F` are global sections of `F`. -/
def sectionsPushforward {Y X : Scheme} (f : Y ⟶ X) :
    pushforward R f ⋙ sections R X ≅ sections R Y := by
  let e : (baseChange f).obj (⊤_ X.ProEt) ≅ ⊤_ Y.ProEt :=
    (IsTerminal.isTerminalObj (baseChange f) _ terminalIsTerminal).uniqueUpToIso
      terminalIsTerminal
  exact NatIso.ofComponents (fun F ↦ (F.obj.mapIso e.op).symm)
    (by
      intro F G a
      change a.hom.app (op ((baseChange f).obj (⊤_ X.ProEt))) ≫
          G.obj.map e.inv.op =
        F.obj.map e.inv.op ≫ a.hom.app (op (⊤_ Y.ProEt))
      exact (a.hom.naturality e.inv.op).symm)

/-- That comparison, applied degreewise to complexes. -/
def cochainSectionsPushforward {Y X : Scheme} (f : Y ⟶ X)
    (K : Cochains R Y) :
    (sections R X).mapCochainComplexPlus.obj
        ((pushforward R f).mapCochainComplexPlus.obj K) ≅
      (sections R Y).mapCochainComplexPlus.obj K :=
  (CochainComplex.Plus.fullyFaithfulι (ModuleCat.{1} R)).preimageIso
    ((Functor.mapHomologicalComplexCompIso (sectionsPushforward R f) (.up
      ℤ)).app K.obj)

/-- An isomorphism between derived global sections of a derived direct image along `f` and derived
global sections, on the bounded-below derived categories of pro-étale sheaves of `R`-modules,
compatible on every bounded-below complex with the underived comparison `sectionsPushforward`. -/
class GlobalSectionsPushforward {Y X : Scheme} (f : Y ⟶ X) where
  comparison : derivedPushforward R f ⋙ derivedSections R X ≅
    derivedSections R Y
  normalized : ∀ K : Cochains R Y,
    (sections R X).rightDerivedFunctorPlusUnit.app
        ((pushforward R f).mapCochainComplexPlus.obj K) ≫
      (derivedSections R X).map
        ((pushforward R f).rightDerivedFunctorPlusUnit.app K) ≫
      comparison.hom.app (DerivedCategory.Plus.Q.obj K) =
    (DerivedCategory.Plus.Q.mapIso (cochainSectionsPushforward R f K)).hom ≫
      (sections R Y).rightDerivedFunctorPlusUnit.app K

/-- The map from derived global sections on `Y` to derived global sections of the nearby object
on `Z`, induced by the unit of the derived adjunction along `i`. -/
def nearbyGlobalComparison {A Y Z : Scheme} (j : Y ⟶ A) (i : Z ⟶ A)
    [DerivedAdjunction R i]
    [GlobalSectionsPushforward R j] [GlobalSectionsPushforward R i]
    (K : Derived R Y) :
    (derivedSections R Y).obj K ⟶
      (derivedSections R Z).obj
        ((derivedPullback R i).obj ((derivedPushforward R j).obj K)) :=
  (GlobalSectionsPushforward.comparison (R := R) (f := j)).inv.app K ≫
    (derivedSections R A).map
      ((DerivedAdjunction.adjunction (R := R) (f := i)).unit.app
        ((derivedPushforward R j).obj K)) ≫
    (GlobalSectionsPushforward.comparison (R := R) (f := i)).hom.app _

/-- Instances of `DerivedAdjunction` and `GlobalSectionsPushforward` for every morphism of schemes:
for each morphism, a normalized adjunction between derived inverse and direct image, and a
normalized comparison of derived global sections of a derived direct image with derived global
sections. -/
class DerivedFunctorTheory where
  [adjunctions : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X), DerivedAdjunction R f]
  [sectionsComparison : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X),
    GlobalSectionsPushforward R f]

attribute [instance_reducible] DerivedFunctorTheory.adjunctions
  DerivedFunctorTheory.sectionsComparison

attribute [instance] DerivedFunctorTheory.adjunctions DerivedFunctorTheory.sectionsComparison

variable (M : Type 1) [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-- The continuous coefficient sheaf `C(-, M)`, in degree zero. -/
def continuousComplex (X : Scheme) : Derived R X :=
  single R (continuousModuleSheaf R M X)

/-- The derived inverse image of the continuous coefficients is the continuous coefficients, when
the coefficient map `f⁻¹ C(-, M) ⟶ C(-, M)` is an isomorphism. -/
def continuousPullbackComparison {Y X : Scheme} (f : Y ⟶ X)
    [PullbackDerivedNormalization R f]
    [IsIso (coefficientPullback R M f)] :
    (derivedPullback R f).obj (continuousComplex R M X) ≅
      continuousComplex R M Y :=
  asIso (inv (pullbackUnitOfSheaf R f (continuousModuleSheaf R M X)) ≫
    singleMap R (coefficientPullback R M f))

/-- The nearby functor `i^* Rj_*`. -/
def nearbyFunctor {A Y Z : Scheme} (j : Y ⟶ A) (i : Z ⟶ A) :
    Derived R Y ⥤ Derived R Z :=
  derivedPushforward R j ⋙ derivedPullback R i

/-- The nearby object of the continuous coefficients. -/
def nearbyObject {A Y Z : Scheme} (j : Y ⟶ A) (i : Z ⟶ A) : Derived R Z :=
  (nearbyFunctor R j i).obj (continuousComplex R M Y)

/-- Specialization: the map from the coefficients on `Z` to the nearby object, induced by the
coefficient map `C(-, M) ⟶ j_* C(-, M)`. -/
def specialization {A Y Z : Scheme} (j : Y ⟶ A) (i : Z ⟶ A)
    [PullbackDerivedNormalization R i]
    [IsIso (coefficientPullback R M i)] :
    continuousComplex R M Z ⟶ nearbyObject R M j i :=
  (continuousPullbackComparison R M i).inv ≫
    (derivedPullback R i).map
      (pushforwardFromSheaf R j (coefficientPushforward R M j))

/-- The endomorphism of the nearby object induced, through the base-change map, by endomorphisms
`a` of `A` and `d` of `Y` compatible with `j` and fixing `Z` (`i ≫ a = i`), when the coefficient
map along `d` is an isomorphism. For automorphisms this is the action of one element; no action
law is proved here. The nearby object is `i^* Rj_*` for the given diagram. -/
def nearbyMonodromy {A Y Z : Scheme} (j : Y ⟶ A) (i : Z ⟶ A)
    (a : A ⟶ A) (d : Y ⟶ Y) (genericSquare : d ≫ j = j ≫ a)
    (specialSquare : i ≫ a = i)
    [DerivedAdjunction R j] [IsIso (coefficientPullback R M d)] :
    End (nearbyObject R M j i) :=
  End.of
    (((DerivedPullbackPasting.comparison (R := R) (f := i) (g := a)) ≪≫
        eqToIso (congrArg (derivedPullback R) specialSquare)).inv.app
        ((derivedPushforward R j).obj (continuousComplex R M Y)) ≫
      (derivedPullback R i).map
        (baseChangeMap R d j j a genericSquare
            (continuousComplex R M Y) ≫
          (derivedPushforward R j).map
            (continuousPullbackComparison R M d).hom))

/-- A map of bounded-below complexes representing specialization in the derived category. -/
structure VanishingCochainModel {A Y Z : Scheme} (j : Y ⟶ A) (i : Z ⟶ A)
    [PullbackDerivedNormalization R i]
    [IsIso (coefficientPullback R M i)] where
  source : Cochains R Z
  target : Cochains R Z
  sourceIso : DerivedCategory.Plus.Q.obj source ≅ continuousComplex R M Z
  targetIso : DerivedCategory.Plus.Q.obj target ≅ nearbyObject R M j i
  arrow : source ⟶ target
  normalized : DerivedCategory.Plus.Q.map arrow ≫ targetIso.hom =
    sourceIso.hom ≫ specialization R M j i

/-- The vanishing object: the mapping cone of the cochain model of specialization, a bounded-below
complex. -/
def vanishingObject {A Y Z : Scheme} {j : Y ⟶ A} {i : Z ⟶ A}
    [PullbackDerivedNormalization R i]
    [IsIso (coefficientPullback R M i)]
    (V : VanishingCochainModel R M j i) :
    Derived R Z :=
  DerivedCategory.Plus.Q.obj ⟨CochainComplex.mappingCone V.arrow.hom, by
    obtain ⟨n₁, _⟩ := V.source.property
    obtain ⟨n₂, _⟩ := V.target.property
    exact ⟨min (n₁ - 1) n₂,
      CochainComplex.isStrictlyGE_mappingCone V.arrow.hom n₁ n₂ _ (by omega) (by omega)⟩⟩

end MathlibExt.AlgebraicGeometry.AdicDerivedContracts
