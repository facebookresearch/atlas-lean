/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The base-change/ordinary composition comparisons are adapted from
AxiomMath/Stacks at c496df0d9beea9deaeabcea8492605f9a0a2313b:
StacksFrontier/AlgebraicGeometry/ProEtale/SiteFunctoriality/MorphismComposition.lean.
Licensed under Apache 2.0; that file has no individual author notice.
Modification notice: use the native small pro-etale sites and module
coefficients already fixed by the completed Atlas core.
-/

module

public import MathlibExt.AlgebraicGeometry.AdicLinearFunctoriality
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject

/-!
# Actual adic derived functors and normalized dependency contracts

All categories are the actual module sheaves on the small pro-etale site.
Inverse image is the existing exact sheaf inverse image. Its right derived
functor therefore computes the same exact inverse image on bounded-below
complexes. Direct image and global sections use Mathlib's actual right
derived functor and its actual unit.

`PullbackDerivedNormalization` and `DerivedAdjunction` record the precise
source-covered adapter input needed to identify these native functors.
They introduce no freely chosen cohomology group, functor or unit. Generic
exact-functor/right-derived adjunction producers are public toolbox; the
signatures below permit their completed adapters to be supplied separately.

Nearby cycles are the fixed composite i* Rj*. The constant-coefficient
specialization is made from the actual continuous-function coefficient
maps and derived units. A cochain vanishing model must represent that exact
arrow; its vanishing object is the actual mapping cone.

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

/-- The actual module-sheaf category, in the site universe. -/
abbrev ModuleSheaf (X : Scheme) := CoefficientSheaf X R

/-- The actual bounded-below cochain category. -/
abbrev Cochains (X : Scheme) := CochainComplex.Plus (ModuleSheaf R X)

/-- The actual bounded-below derived category. -/
abbrev Derived (X : Scheme) := DerivedCategory.Plus (ModuleSheaf R X)

/-- Actual global sections at the terminal small-site object. -/
def sections (X : Scheme) : ModuleSheaf R X ⥤ ModuleCat.{1} R where
  obj F := F.obj.obj (op (⊤_ X.ProEt))
  map a := a.hom.app (op (⊤_ X.ProEt))
  map_id _F := rfl
  map_comp _a _b := rfl

instance sections_additive (X : Scheme) : (sections R X).Additive where
  map_add := rfl

/-- The actual right derived global-section functor. -/
def derivedSections (X : Scheme) :
    Derived R X ⥤ DerivedCategory.Plus (ModuleCat.{1} R) :=
  (sections R X).rightDerivedFunctorPlus

/-- The actual derived inverse image of an exact inverse-image functor. -/
def derivedPullback {Y X : Scheme} (f : Y ⟶ X) :
    Derived R X ⥤ Derived R Y :=
  (pullback R f).rightDerivedFunctorPlus

/-- The actual right derived direct-image functor. -/
def derivedPushforward {Y X : Scheme} (f : Y ⟶ X) :
    Derived R Y ⥤ Derived R X :=
  (pushforward R f).rightDerivedFunctorPlus

/-- The actual single cochain complex, with its strict lower bound. -/
def singleCochain {X : Scheme} (F : ModuleSheaf R X) : Cochains R X :=
  ⟨(CochainComplex.singleFunctor (ModuleSheaf R X) 0).obj F,
    ⟨0, inferInstance⟩⟩

/-- The actual single derived object. -/
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

/-- A sheaf map gives its prescribed map of single complexes. -/
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

/-- The derived adjunction unit is prescribed on every cochain model. -/
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

/-- Source-covered exact-derived normalization for the fixed pullback.
The unit itself is Mathlib's fixed unit, not a chosen isomorphism. -/
class PullbackDerivedNormalization {Y X : Scheme} (f : Y ⟶ X) : Prop where
  unit_isIso (K : Cochains R X) :
    IsIso ((pullback R f).rightDerivedFunctorPlusUnit.app K)

attribute [instance] PullbackDerivedNormalization.unit_isIso

/-- A derived adjunction between the fixed functors, with its actual
ordinary/derived unit normalization on every cochain model. -/
class DerivedAdjunction {Y X : Scheme} (f : Y ⟶ X) where
  adjunction : derivedPullback R f ⊣ derivedPushforward R f
  unit_normalization : ∀ K : Cochains R X,
    adjunction.unit.app (DerivedCategory.Plus.Q.obj K) =
      normalizedDerivedUnit R f K

/-- The single-complex comparison is the native functorial comparison. -/
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

/-- An ordinary sheaf map into f* yields its prescribed derived map. -/
def pushforwardFromSheaf {Y X : Scheme} (f : Y ⟶ X)
    {A : ModuleSheaf R X} {B : ModuleSheaf R Y}
    (a : A ⟶ (pushforward R f).obj B) :
    single R A ⟶ (derivedPushforward R f).obj (single R B) :=
  singleMap R a ≫
    (DerivedCategory.Plus.Q.mapIso
      (singleCochainComparison R (pushforward R f) B)).inv ≫
        (pushforward R f).rightDerivedFunctorPlusUnit.app (singleCochain R B)

/-- The actual pullback-pasting comparison on small-site objects. -/
def baseChangeComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseChange g ⋙ baseChange f ≅ baseChange (f ≫ g) :=
  Functor.fullyFaithfulCancelRight (ProEt.forget X)
    (Functor.isoWhiskerLeft (ProEt.forget Z) (Over.pullbackComp f g).symm)

/-- Actual direct-image composition from that exact site comparison. -/
def pushforwardComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforward R f ⋙ pushforward R g ≅ pushforward R (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (baseChangeComp f g)
    (ModuleCat.{1} R) (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)

/-- The actual inverse-image composition mate of direct-image composition. -/
def pullbackComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback R g ⋙ pullback R f ≅ pullback R (f ≫ g) :=
  (((pullbackAdjunction R g).comp (pullbackAdjunction R f)).ofNatIsoRight
    (pushforwardComp R f g)).leftAdjointUniq (pullbackAdjunction R (f ≫ g))

/-- The prescribed ordinary composition on cochain models. -/
def cochainPullbackComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : Cochains R Z) :
    (pullback R f).mapCochainComplexPlus.obj
        ((pullback R g).mapCochainComplexPlus.obj K) ≅
      (pullback R (f ≫ g)).mapCochainComplexPlus.obj K :=
  (CochainComplex.Plus.fullyFaithfulι (ModuleSheaf R X)).preimageIso
    ((Functor.mapHomologicalComplexCompIso (pullbackComp R f g) (.up ℤ)).app
      K.obj)

/-- The actual composite derived unit on a cochain model. -/
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

/-- Derived pasting of the fixed pullbacks, normalized on every cochain.
This is a source-covered localization adapter, with no free comparison map. -/
class DerivedPullbackPasting {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) where
  comparison : derivedPullback R g ⋙ derivedPullback R f ≅
    derivedPullback R (f ≫ g)
  normalized : ∀ K : Cochains R Z,
    compositePullbackUnit R f g K ≫
        comparison.hom.app (DerivedCategory.Plus.Q.obj K) =
      (DerivedCategory.Plus.Q.mapIso (cochainPullbackComp R f g K)).hom ≫
        (pullback R (f ≫ g)).rightDerivedFunctorPlusUnit.app K

/-- The comparison of pullbacks around an actual commuting scheme square. -/
def pullbackSquare {X' X Y' Y : Scheme}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (comm : g' ≫ f = f' ≫ g)
    [DerivedPullbackPasting R f' g] [DerivedPullbackPasting R g' f] :
    derivedPullback R g ⋙ derivedPullback R f' ≅
      derivedPullback R f ⋙ derivedPullback R g' :=
  (DerivedPullbackPasting.comparison (R := R) (f := f') (g := g)) ≪≫
    eqToIso (congrArg (derivedPullback R) comm.symm) ≪≫
      (DerivedPullbackPasting.comparison (R := R) (f := g') (g := f)).symm

/-- The base-change map is the actual adjunction mate of that square. -/
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

/-- Ordinary global sections of f* are actual global sections of its source. -/
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

/-- The actual global-section/direct-image comparison on cochains. -/
def cochainSectionsPushforward {Y X : Scheme} (f : Y ⟶ X)
    (K : Cochains R Y) :
    (sections R X).mapCochainComplexPlus.obj
        ((pushforward R f).mapCochainComplexPlus.obj K) ≅
      (sections R Y).mapCochainComplexPlus.obj K :=
  (CochainComplex.Plus.fullyFaithfulι (ModuleCat.{1} R)).preimageIso
    ((Functor.mapHomologicalComplexCompIso (sectionsPushforward R f) (.up
      ℤ)).app K.obj)

/-- The fixed derived direct-image/global-section comparison, normalized
by the actual ordinary comparison and both native right-derived units. -/
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

/-- The canonical global nearby comparison uses the actual restriction
unit along i, with the actual global-section/direct-image comparisons. -/
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

/-- A reusable source-covered derived-functor adapter contract. Every
functor and unit in these fields is already the fixed native construction. -/
class DerivedFunctorTheory where
  [pullbackNormalization : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X),
    PullbackDerivedNormalization R f]
  [adjunctions : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X), DerivedAdjunction R f]
  [pasting : ∀ {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z),
    DerivedPullbackPasting R f g]
  [sectionsComparison : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X),
    GlobalSectionsPushforward R f]

attribute [instance_reducible] DerivedFunctorTheory.adjunctions
  DerivedFunctorTheory.pasting DerivedFunctorTheory.sectionsComparison

attribute [instance] DerivedFunctorTheory.pullbackNormalization
  DerivedFunctorTheory.adjunctions DerivedFunctorTheory.pasting
  DerivedFunctorTheory.sectionsComparison

variable (M : Type 1) [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-- The actual continuous coefficient sheaf, placed in degree zero. -/
def continuousComplex (X : Scheme) : Derived R X :=
  single R (continuousModuleSheaf R M X)

/-- The coefficient pullback comparison, fixed by the actual coefficient map. -/
def continuousPullbackComparison {Y X : Scheme} (f : Y ⟶ X)
    [PullbackDerivedNormalization R f]
    [IsIso (coefficientPullback R M f)] :
    (derivedPullback R f).obj (continuousComplex R M X) ≅
      continuousComplex R M Y :=
  asIso (inv (pullbackUnitOfSheaf R f (continuousModuleSheaf R M X)) ≫
    singleMap R (coefficientPullback R M f))

/-- The actual global nearby functor for a prescribed geometric diagram. -/
def nearbyFunctor {A Y Z : Scheme} (j : Y ⟶ A) (i : Z ⟶ A) :
    Derived R Y ⥤ Derived R Z :=
  derivedPushforward R j ⋙ derivedPullback R i

/-- The actual nearby object with continuous coefficients. -/
def nearbyObject {A Y Z : Scheme} (j : Y ⟶ A) (i : Z ⟶ A) : Derived R Z :=
  (nearbyFunctor R j i).obj (continuousComplex R M Y)

/-- Specialization is the actual coefficient-unit/right-derived-unit map. -/
def specialization {A Y Z : Scheme} (j : Y ⟶ A) (i : Z ⟶ A)
    [PullbackDerivedNormalization R i]
    [IsIso (coefficientPullback R M i)] :
    continuousComplex R M Z ⟶ nearbyObject R M j i :=
  (continuousPullbackComparison R M i).inv ≫
    (derivedPullback R i).map
      (pushforwardFromSheaf R j (coefficientPushforward R M j))

/-- The reusable realization proof for the actual coefficient pullback
map, not a choice of another coefficient object or comparison. -/
class CoefficientTheory : Prop where
  [pullback_isIso : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X),
    IsIso (coefficientPullback R M f)]

attribute [instance] CoefficientTheory.pullback_isIso

/-- The canonical nearby monodromy mate of a prescribed geometric deck
square. The two maps a and d must be the actual geometric scheme actions. -/
def nearbyMonodromy {A Y Z : Scheme} (j : Y ⟶ A) (i : Z ⟶ A)
    (a : A ⟶ A) (d : Y ⟶ Y) (genericSquare : d ≫ j = j ≫ a)
    (specialSquare : i ≫ a = i)
    [DerivedFunctorTheory R] [CoefficientTheory R M] :
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

/-- A cochain model represents the exact specialization arrow. Such an
enhancement is generic source-covered adapter data, not a free vanishing map. -/
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
