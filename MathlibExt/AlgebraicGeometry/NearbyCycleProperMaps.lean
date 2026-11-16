/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import MathlibExt.AlgebraicGeometry.NearbyCycleMonodromy

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Canonical derived comparison maps for nearby cycles

Direct image is Mathlib's actual total right derived functor. Its
adjunction data is normalized by the ordinary sheaf unit and the actual
right-derived unit on every cochain complex. Base change is their
adjunction mate; no independently chosen proper comparison map occurs.

Generic derived existence and K-injective computation are explicit
toolbox inputs, already covered by the Axiom Stacks Spaltenstein theory.
The matching Wanted module requests geometric isomorphism theorems.
-/

namespace MathlibExt.AlgebraicGeometry.NearbyCycleProperMaps

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits CategoryTheory.Localization
open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.ComplexAnalytification
open _root_.MathlibExt.AlgebraicGeometry.PerverseSheaves
open _root_.MathlibExt.AlgebraicGeometry.ConstructibleComplexes
open _root_.MathlibExt.AlgebraicGeometry.NearbyCycleGeometry
open _root_.MathlibExt.AlgebraicGeometry.NearbyCycleComplexes
open _root_.MathlibExt.AlgebraicGeometry.NearbyCycleMonodromy

attribute [local instance] HasDerivedCategory.standard

/-- The fixed cochain functor whose actual right derived functor is Rf*. -/
abbrev pushforwardSource {V W : TopCat.{0}} (f : V ⟶ W) :
    QCochain V ⥤ QDerived W :=
  cochainPushforward f ⋙ DerivedCategory.Q

/-- Generic existence of the actual right Kan-derived functor at this
particular continuous map. No global provider is asserted. -/
class HasDerivedPushforward {V W : TopCat.{0}} (f : V ⟶ W) : Prop where
  [hasDerived : (pushforwardSource f).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (QSheaf V) (.up ℤ))]

attribute [instance] HasDerivedPushforward.hasDerived

/-- The actual Rf*, fixed by Mathlib's right-derived construction. -/
def derivedPushforward {V W : TopCat.{0}} (f : V ⟶ W) [HasDerivedPushforward f] :
    QDerived V ⥤ QDerived W :=
  (pushforwardSource f).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (QSheaf V) (.up ℤ))

/-- The actual right-derived unit, before localization of the source. -/
def derivedPushforwardUnit {V W : TopCat.{0}} (f : V ⟶ W) [HasDerivedPushforward f] :
    pushforwardSource f ⟶ DerivedCategory.Q ⋙ derivedPushforward f :=
  (pushforwardSource f).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso (QSheaf V) (.up ℤ))

/-- The required derived-adjunction unit on an actual Q(cochain), obtained
from the ordinary unit and the right-derived unit. -/
def normalizedUnitOnCochain {V W : TopCat.{0}} (f : V ⟶ W)
    [HasDerivedPushforward f] (K : QCochain W) :
    DerivedCategory.Q.obj K ⟶
      (derivedPushforward f).obj ((derivedPullback ℚ f).obj (DerivedCategory.Q.obj K)) :=
  DerivedCategory.Q.map ((cochainUnit f).app K) ≫
    (derivedPushforwardUnit f).app ((cochainPullback f).obj K) ≫
      (derivedPushforward f).map ((pullback ℚ f).mapDerivedCategoryFactors.inv.app K)

/-- Actual adjunction for the fixed inverse image and Rf*, including
normalization on every cochain. This input has no free trace or unit. -/
class NormalizedDerivedAdjunction {V W : TopCat.{0}} (f : V ⟶ W)
    [HasDerivedPushforward f] where
  adjunction : derivedPullback ℚ f ⊣ derivedPushforward f
  unit_eq : ∀ K : QCochain W,
    adjunction.unit.app (DerivedCategory.Q.obj K) = normalizedUnitOnCochain f K

/-- Exact-functor localization carries a fixed sheaf natural
isomorphism to a fixed derived natural isomorphism. -/
def exactDerivedIso {V W : TopCat.{0}} {F G : QSheaf V ⥤ QSheaf W}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (QSheaf V) (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q)

/-- Canonical composition for actual exact derived inverse images. -/
def derivedPullbackComp {V W Z : TopCat.{0}} (f : V ⟶ W) (g : W ⟶ Z) :
    derivedPullback ℚ g ⋙ derivedPullback ℚ f ≅ derivedPullback ℚ (f ≫ g) :=
  (pullback ℚ g).mapDerivedCategoryCompIso (pullback ℚ f) ≪≫
    exactDerivedIso (sheafPullbackComp f g)

/-- Direct-image equality comparison at an actual equality of maps. -/
def derivedPushforwardCongr {V W : TopCat.{0}} {f g : V ⟶ W}
    (h : f = g) [HasDerivedPushforward f] [HasDerivedPushforward g] :
    derivedPushforward f ≅ derivedPushforward g :=
  eqToIso (by subst h; rfl)

/-- Composition of the fixed Rf* functors, as right-adjoint uniqueness
for the same canonical inverse-image composition. -/
def derivedPushforwardComp {V W Z : TopCat.{0}} (f : V ⟶ W) (g : W ⟶ Z)
    [HasDerivedPushforward f] [HasDerivedPushforward g]
    [HasDerivedPushforward (f ≫ g)]
    [NormalizedDerivedAdjunction f] [NormalizedDerivedAdjunction g]
    [NormalizedDerivedAdjunction (f ≫ g)] :
    derivedPushforward f ⋙ derivedPushforward g ≅ derivedPushforward (f ≫ g) :=
  ((NormalizedDerivedAdjunction.adjunction (f := g)).comp
    (NormalizedDerivedAdjunction.adjunction (f := f))).rightAdjointUniq
      ((NormalizedDerivedAdjunction.adjunction (f := f ≫ g)).ofNatIsoLeft
        (derivedPullbackComp f g).symm)

/-- The canonical inverse-image comparison for a commutative square. -/
def squarePullbackIso {V V' W W' : TopCat.{0}}
    (a : V' ⟶ V) (b : W' ⟶ W) (g : V ⟶ W) (g' : V' ⟶ W')
    (h : a ≫ g = g' ≫ b) :
    derivedPullback ℚ b ⋙ derivedPullback ℚ g' ≅
      derivedPullback ℚ g ⋙ derivedPullback ℚ a :=
  derivedPullbackComp g' b ≪≫
    eqToIso (congrArg (fun f : V' ⟶ W ↦ derivedPullback ℚ f) h.symm) ≪≫
      (derivedPullbackComp a g).symm

/-- The actual base-change map b* Rg* → Rg'* a*, obtained from the
normalized adjunction unit, the fixed square comparison and the counit. -/
def baseChange {V V' W W' : TopCat.{0}}
    (a : V' ⟶ V) (b : W' ⟶ W) (g : V ⟶ W) (g' : V' ⟶ W')
    (h : a ≫ g = g' ≫ b)
    [HasDerivedPushforward g] [HasDerivedPushforward g']
    [NormalizedDerivedAdjunction g] [NormalizedDerivedAdjunction g'] :
    derivedPushforward g ⋙ derivedPullback ℚ b ⟶
      derivedPullback ℚ a ⋙ derivedPushforward g' :=
  CategoryTheory.mateEquiv
    (NormalizedDerivedAdjunction.adjunction (f := g))
    (NormalizedDerivedAdjunction.adjunction (f := g'))
    (squarePullbackIso a b g g' h).hom

/-- The classical unshifted i* Rq* q* formula, on the actual cover. -/
def formulaNearby {X : ComplexScheme} {s : Γ(X.left, ⊤)} (A : ZeroFiber X s)
    [HasDerivedPushforward (coverProjection X s)] :
    QDerived (space X) ⥤ QDerived (space A.Z) :=
  derivedPullback ℚ (coverProjection X s) ⋙
    derivedPushforward (coverProjection X s) ⋙ derivedPullback ℚ (spaceMap A.i)



/-- Generic K-injective computation for the actual right-derived unit.
This is a property of the fixed Rf*, with no selected comparison map. -/
class RightDerivedInjectiveCalculation {V W : TopCat.{0}} (f : V ⟶ W)
    [HasDerivedPushforward f] : Prop where
  unitIso : ∀ (K : QCochain V), K.IsKInjective →
    IsIso ((derivedPushforwardUnit f).app K)

instance resolvedRightDerivedUnitIso {V W : TopCat.{0}} (f : V ⟶ W)
    [HasDerivedPushforward f] [RightDerivedInjectiveCalculation f]
    (R : FunctorialResolution V) (K : QCochain V) :
    IsIso ((whiskerLeft R.functor (derivedPushforwardUnit f)).app K) :=
  RightDerivedInjectiveCalculation.unitIso _ (R.isKInjective K)

/-- The actual Q of the resolution inclusion is an isomorphism. -/
def resolutionLocalizationIso {V : TopCat.{0}} (R : FunctorialResolution V) :
    (DerivedCategory.Q : QCochain V ⥤ QDerived V) ≅ R.functor ⋙ DerivedCategory.Q := by
  have hi : IsIso (whiskerRight R.inclusion DerivedCategory.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    change IsIso (DerivedCategory.Q.map (R.inclusion.app K))
    have : QuasiIso (R.inclusion.app K) := R.quasiIso K
    infer_instance
  exact (Functor.leftUnitor DerivedCategory.Q).symm ≪≫
    asIso (whiskerRight R.inclusion DerivedCategory.Q)

/-- Canonical K-injective calculation, using the same right-derived unit
and actual natural quasi-isomorphism of the resolution. -/
def cochainPushforwardCalculation {V W : TopCat.{0}} (f : V ⟶ W)
    [HasDerivedPushforward f] [RightDerivedInjectiveCalculation f]
    (R : FunctorialResolution V) :
    DerivedCategory.Q ⋙ derivedPushforward f ≅
      R.functor ⋙ cochainPushforward f ⋙ DerivedCategory.Q := by
  have hi : IsIso (whiskerLeft R.functor (derivedPushforwardUnit f)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact RightDerivedInjectiveCalculation.unitIso _ (R.isKInjective K)
  exact isoWhiskerRight (resolutionLocalizationIso R) (derivedPushforward f) ≪≫
    Functor.associator _ _ _ ≪≫
      (asIso (whiskerLeft R.functor (derivedPushforwardUnit f))).symm

/-- The cochain calculation identifies the classical formula with the
actual localized nearby functor. All three comparison maps are canonical. -/
def formulaCochainComparison {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s))
    [HasDerivedPushforward (coverProjection X s)]
    [RightDerivedInjectiveCalculation (coverProjection X s)] :
    DerivedCategory.Q ⋙ formulaNearby A ≅ nearbyCochain A R ⋙ DerivedCategory.Q := by
  let P := cochainPullback (coverProjection X s)
  let B := cochainPushforward (coverProjection X s)
  let I := cochainPullback (spaceMap A.i)
  let D := derivedPushforward (coverProjection X s)
  let J := derivedPullback ℚ (spaceMap A.i)
  let a := (pullback ℚ (coverProjection X s)).mapDerivedCategoryFactors
  let b := cochainPushforwardCalculation (coverProjection X s) R
  let c := (pullback ℚ (spaceMap A.i)).mapDerivedCategoryFactors
  exact (Functor.associator _ _ (D ⋙ J)).symm ≪≫
    isoWhiskerRight a (D ⋙ J) ≪≫ Functor.associator P _ _ ≪≫
    isoWhiskerLeft P
      ((Functor.associator _ D J).symm ≪≫ isoWhiskerRight b J ≪≫
        isoWhiskerRight (Functor.associator R.functor B DerivedCategory.Q).symm J ≪≫
        Functor.associator (R.functor ⋙ B) DerivedCategory.Q J ≪≫
        isoWhiskerLeft (R.functor ⋙ B) c ≪≫
        Functor.associator R.functor B (I ⋙ DerivedCategory.Q) ≪≫
        isoWhiskerLeft R.functor (Functor.associator B I DerivedCategory.Q).symm ≪≫
        (Functor.associator R.functor (B ⋙ I) DerivedCategory.Q).symm) ≪≫
    (Functor.associator P (R.functor ⋙ B ⋙ I) DerivedCategory.Q).symm

/-- The actual global nearby functor agrees with i* Rq* q* through this
fixed, resolution-normalized comparison. -/
def nearbyFormulaIso {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s))
    [HasDerivedPushforward (coverProjection X s)]
    [RightDerivedInjectiveCalculation (coverProjection X s)] :
    nearbyFunctor A R ≅ formulaNearby A :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (QSheaf (space X)) (.up ℤ))
    (nearbyCochain A R ⋙ DerivedCategory.Q) (DerivedCategory.Q ⋙ formulaNearby A)
    _ _ (formulaCochainComparison A R).symm

instance derivedPushforwardCommShift {V W : TopCat.{0}} (f : V ⟶ W)
    [HasDerivedPushforward f] : (derivedPushforward f).CommShift ℤ := by
  dsimp [derivedPushforward]
  infer_instance


/-- The particular right-derived and normalized-adjoint inputs used by
the actual cover and zero-fiber squares of this diagram. -/
class DiagramDerivedData {X Y : ComplexScheme}
    {s : Γ(X.left, ⊤)} {t : Γ(Y.left, ⊤)}
    {A : ZeroFiber X s} {B : ZeroFiber Y t} (G : FunctionMorphism A B) where
  [pushG : HasDerivedPushforward (spaceMap G.g)]
  [pushZero : HasDerivedPushforward (spaceMap G.g₀)]
  [pushCoverX : HasDerivedPushforward (coverProjection X s)]
  [pushCoverY : HasDerivedPushforward (coverProjection Y t)]
  [pushCoverMap : HasDerivedPushforward (coverMap G)]
  [pushCompositeX : HasDerivedPushforward (coverProjection X s ≫ spaceMap G.g)]
  [pushCompositeY : HasDerivedPushforward (coverMap G ≫ coverProjection Y t)]
  [computeCoverX : RightDerivedInjectiveCalculation (coverProjection X s)]
  [computeCoverY : RightDerivedInjectiveCalculation (coverProjection Y t)]
  [adjG : NormalizedDerivedAdjunction (spaceMap G.g)]
  [adjZero : NormalizedDerivedAdjunction (spaceMap G.g₀)]
  [adjCoverX : NormalizedDerivedAdjunction (coverProjection X s)]
  [adjCoverY : NormalizedDerivedAdjunction (coverProjection Y t)]
  [adjCoverMap : NormalizedDerivedAdjunction (coverMap G)]
  [adjCompositeX : NormalizedDerivedAdjunction (coverProjection X s ≫ spaceMap G.g)]
  [adjCompositeY : NormalizedDerivedAdjunction (coverMap G ≫ coverProjection Y t)]

attribute [instance_reducible] DiagramDerivedData.adjG DiagramDerivedData.adjZero
  DiagramDerivedData.adjCoverX DiagramDerivedData.adjCoverY DiagramDerivedData.adjCoverMap
  DiagramDerivedData.adjCompositeX DiagramDerivedData.adjCompositeY

attribute [instance] DiagramDerivedData.pushG DiagramDerivedData.pushZero
  DiagramDerivedData.pushCoverX DiagramDerivedData.pushCoverY DiagramDerivedData.pushCoverMap
  DiagramDerivedData.pushCompositeX DiagramDerivedData.pushCompositeY
  DiagramDerivedData.computeCoverX DiagramDerivedData.computeCoverY
  DiagramDerivedData.adjG DiagramDerivedData.adjZero DiagramDerivedData.adjCoverX
  DiagramDerivedData.adjCoverY DiagramDerivedData.adjCoverMap
  DiagramDerivedData.adjCompositeX DiagramDerivedData.adjCompositeY

/-- The actual zero-fiber square on complex points. -/
lemma zeroSpaceSquare {X Y : ComplexScheme}
    {s : Γ(X.left, ⊤)} {t : Γ(Y.left, ⊤)}
    {A : ZeroFiber X s} {B : ZeroFiber Y t} (G : FunctionMorphism A B) :
    spaceMap A.i ≫ spaceMap G.g = spaceMap G.g₀ ≫ spaceMap B.i := by
  change ComplexAnalytification.functor.map A.i ≫ ComplexAnalytification.functor.map G.g =
    ComplexAnalytification.functor.map G.g₀ ≫ ComplexAnalytification.functor.map B.i
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg ComplexAnalytification.functor.map G.zero_square

/-- The canonical derived direct-image interchange in the cover square. -/
def coverPushInterchange {X Y : ComplexScheme}
    {s : Γ(X.left, ⊤)} {t : Γ(Y.left, ⊤)}
    {A : ZeroFiber X s} {B : ZeroFiber Y t} (G : FunctionMorphism A B)
    [DiagramDerivedData G] :
    derivedPushforward (coverMap G) ⋙ derivedPushforward (coverProjection Y t) ≅
      derivedPushforward (coverProjection X s) ⋙ derivedPushforward (spaceMap G.g) :=
  derivedPushforwardComp (coverMap G) (coverProjection Y t) ≪≫
    derivedPushforwardCongr (coverMap_square G) ≪≫
      (derivedPushforwardComp (coverProjection X s) (spaceMap G.g)).symm

/-- The actual proper-nearby comparison: first the cover base-change
mate, then direct-image composition, then the zero-fiber base-change mate.
Its geometric invertibility is requested separately. -/
def properNearbyComparison {X Y : ComplexScheme}
    {s : Γ(X.left, ⊤)} {t : Γ(Y.left, ⊤)}
    {A : ZeroFiber X s} {B : ZeroFiber Y t} (G : FunctionMorphism A B)
    [DiagramDerivedData G] :
    derivedPushforward (spaceMap G.g) ⋙ formulaNearby B ⟶
      formulaNearby A ⋙ derivedPushforward (spaceMap G.g₀) := by
  let P₁ := derivedPullback ℚ (coverProjection X s)
  let P₂ := derivedPullback ℚ (coverProjection Y t)
  let R₁ := derivedPushforward (coverProjection X s)
  let R₂ := derivedPushforward (coverProjection Y t)
  let J₁ := derivedPullback ℚ (spaceMap A.i)
  let J₂ := derivedPullback ℚ (spaceMap B.i)
  let S := derivedPushforward (spaceMap G.g)
  let S₀ := derivedPushforward (spaceMap G.g₀)
  let S' := derivedPushforward (coverMap G)
  let b := baseChange (coverProjection X s) (coverProjection Y t)
    (spaceMap G.g) (coverMap G) (coverMap_square G).symm
  let c := coverPushInterchange G
  let z := baseChange (spaceMap A.i) (spaceMap B.i) (spaceMap G.g) (spaceMap G.g₀)
    (zeroSpaceSquare G)
  exact (Functor.associator S P₂ (R₂ ⋙ J₂)).inv ≫
    whiskerRight b (R₂ ⋙ J₂) ≫ (Functor.associator P₁ S' (R₂ ⋙ J₂)).hom ≫
    whiskerLeft P₁
      ((Functor.associator S' R₂ J₂).inv ≫ whiskerRight c.hom J₂ ≫
        (Functor.associator R₁ S J₂).hom) ≫
    whiskerLeft P₁ (whiskerLeft R₁ z) ≫
    whiskerLeft P₁ (Functor.associator R₁ J₁ S₀).inv ≫
    (Functor.associator P₁ (R₁ ⋙ J₁) S₀).inv

/-- Proper comparison of the actual cycle triangles on bounded
constructible source complexes. The first two components are fixed by
the actual base-change maps; monodromy is the actual deck map. -/
structure CanonicalProperCycleComparison {X Y : ComplexScheme}
    {s : Γ(X.left, ⊤)} {t : Γ(Y.left, ⊤)}
    {A : ZeroFiber X s} {B : ZeroFiber Y t} (G : FunctionMorphism A B)
    [DiagramDerivedData G]
    (R₁ : FunctorialResolution (exponentialCover X s))
    (R₂ : FunctorialResolution (exponentialCover Y t))
    (E₁ : DeckResolutionComparison R₁ (deckIso X s 1))
    (E₂ : DeckResolutionComparison R₂ (deckIso Y t 1))
    (hc₁ : specializationCochain A R₁ ≫ (nearbyCochainMonodromy A R₁ E₁).hom =
      specializationCochain A R₁)
    (hc₂ : specializationCochain B R₂ ≫ (nearbyCochainMonodromy B R₂ E₂).hom =
      specializationCochain B R₂) where
  comparison :
    (PerverseSheaves.boundedConstructible X).ι ⋙
      derivedPushforward (spaceMap G.g) ⋙ cycleTriangles B R₂ ≅
    (PerverseSheaves.boundedConstructible X).ι ⋙
      cycleTriangles A R₁ ⋙ (derivedPushforward (spaceMap G.g₀)).mapTriangle
  first : ∀ K : (PerverseSheaves.boundedConstructible X).FullSubcategory,
    (comparison.hom.app K).hom₁ =
      (cycleFirstIso B R₂).hom.app ((derivedPushforward (spaceMap G.g)).obj K.obj) ≫
        (baseChange (spaceMap A.i) (spaceMap B.i) (spaceMap G.g) (spaceMap G.g₀)
          (zeroSpaceSquare G)).app K.obj ≫
            (derivedPushforward (spaceMap G.g₀)).map ((cycleFirstIso A R₁).inv.app K.obj)
  second : ∀ K : (PerverseSheaves.boundedConstructible X).FullSubcategory,
    (comparison.hom.app K).hom₂ =
      (nearbyFormulaIso B R₂).hom.app ((derivedPushforward (spaceMap G.g)).obj K.obj) ≫
        (properNearbyComparison G).app K.obj ≫
          (derivedPushforward (spaceMap G.g₀)).map ((nearbyFormulaIso A R₁).inv.app K.obj)
  nearbyMonodromy_eq : ∀ K : (PerverseSheaves.boundedConstructible X).FullSubcategory,
    (nearbyMonodromy B R₂ E₂).hom.app ((derivedPushforward (spaceMap G.g)).obj K.obj) ≫
      (comparison.hom.app K).hom₂ =
        (comparison.hom.app K).hom₂ ≫
          (derivedPushforward (spaceMap G.g₀)).map ((nearbyMonodromy A R₁ E₁).hom.app K.obj)
  vanishingMonodromy_eq : ∀ K : (PerverseSheaves.boundedConstructible X).FullSubcategory,
    (vanishingMonodromy B R₂ E₂ hc₂).hom.app
        ((derivedPushforward (spaceMap G.g)).obj K.obj) ≫ (comparison.hom.app K).hom₃ =
      (comparison.hom.app K).hom₃ ≫
        (derivedPushforward (spaceMap G.g₀)).map
          ((vanishingMonodromy A R₁ E₁ hc₁).hom.app K.obj)


end MathlibExt.AlgebraicGeometry.NearbyCycleProperMaps

