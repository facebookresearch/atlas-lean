/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BerkovichAnalytification
public import MathlibExt.AlgebraicGeometry.BerkovichStructureSheaf
public import MathlibExt.AlgebraicGeometry.BoundedAffinoidMorphisms
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# General nonarchimedean analytic realization contracts

Local models retain the actual polynomial kernel in the Tate quotient,
including nilpotents. Their structure sheaf is the fixed rational-limit
presheaf. Its map to an affine scheme is constructed by the existing
locally-ringed-space Γ–Spec adjunction. Only its real-valued point comparison
and the global geometric realization are additional provider data.

An atlas uses open subsets of affinoid spectra, with open ringed chart maps
and isomorphisms on all stalks. It covers each valued point and commutes with
the actual affine polynomial presentation. Thus the interface includes
singular and nonreduced locally finite-type schemes; no smoothness or
manifold replacement is built into it. Affinoid domains themselves may have
boundary, so a whole affinoid chart is not required to be an ambient open.

Coherent modules, pullback, its adjunction and the derived cohomology
comparison are actual Mathlib constructions on this normalized ringed map.
The geometric existence, coherence, GAGA and comparison proofs are separate
Wanted dependencies. These definitions do not assert those providers.

References: Berkovich, *Spectral theory and analytic geometry over
non-Archimedean fields*, §§3.4–3.5; Zomervrucht, *Berkovich analytification*,
Theorem 2.1, formula (2.3), Theorems 2.8–2.9, pp. 2–3.
https://www.mi.fu-berlin.de/math/groups/arithmetic_geometry/research_seminar/documents/berkovich03.pdf
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticSpaces
open MathlibExt.AlgebraicGeometry.BerkovichStructureSheaf
open MathlibExt.AlgebraicGeometry.BerkovichAnalytification
open MathlibExt.AlgebraicGeometry.BoundedAffinoidMorphisms

variable (K : Type) [NormedField K] [IsUltrametricDist K]

/-- Named local dependencies, so global paper interfaces can be bound before
the rational-spectrum and sheaf-geometry providers have been proved. -/
structure LocalAffinoidTheory where
  rational : ∀ A : AffinoidAlgebra K, RationalRestrictionTheory A
  spectrum : ∀ A : AffinoidAlgebra K, RationalSpectrumGeometry (rational A)
  sheaf : ∀ A : AffinoidAlgebra K,
    AffinoidSheafGeometry (rational A) (spectrum A)
  morphism : ∀ (A B : AffinoidAlgebra K) (f : B ⟶ A),
    AffinoidMorphism (sheaf A) (sheaf B) f

/-- Actual ground-field regular constants. -/
def globalScalarMap (X : AlgebraicScheme K) : K →+* Γ(X.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ X.hom.appTop).hom

/-- A finite affinoid presentation of an actual affine coordinate ring.
The Tate kernel is precisely the extension of the polynomial kernel. -/
structure AffineTateChart (X : AlgebraicScheme K) where
  isAffine : IsAffine X.left
  algebra : AffinoidAlgebra K
  polynomialMap : MvPolynomial (Fin algebra.presentation.variableCount) K →+*
    Γ(X.left, ⊤)
  polynomial_surjective : Function.Surjective polynomialMap
  polynomial_scalar : ∀ a : K,
    polynomialMap (MvPolynomial.C a) = globalScalarMap K X a
  coefficientMap : Γ(X.left, ⊤) →+* algebra
  polynomial_normalization : ∀ f,
    coefficientMap (polynomialMap f) =
      algebra.presentation.quotientMap
        (MvPolynomial.toRestricted algebra.presentation.radius f)
  kernel_normalization :
    RingHom.ker algebra.presentation.quotientMap.toRingHom =
    Ideal.span ((MvPolynomial.toRestricted algebra.presentation.radius) ''
      (RingHom.ker polynomialMap : Set _))

namespace AffineTateChart

variable {K} {X : AlgebraicScheme K} (T : AffineTateChart K X)
  {R : RationalRestrictionTheory T.algebra}
  {G : RationalSpectrumGeometry R} (S : AffinoidSheafGeometry R G)

/-- The actual normalized affine ringed map, constructed by Γ–Spec. -/
def algebraicMap : S.locallyRingedSpace ⟶ X.left.toLocallyRingedSpace :=
  letI := T.isAffine
  (ΓSpec.locallyRingedSpaceAdjunction.homEquiv S.locallyRingedSpace
    (op Γ(X.left, ⊤)))
      (CommRingCat.ofHom ((constantSection R ⊤).comp T.coefficientMap)).op ≫
    X.left.isoSpec.inv.toLRSHom

/-- The coefficient map includes the actual ground-field constants. -/
theorem coefficientMap_scalar (a : K) :
    T.coefficientMap (globalScalarMap K X a) = algebraMap K T.algebra a := by
  rw [← T.polynomial_scalar, T.polynomial_normalization,
    MvPolynomial.toRestricted_C, ← MvPowerSeries.Restricted.algebraMap_apply]
  exact T.algebra.presentation.quotientMap.commutes a

/-- The affine point comparison has its scheme point and every coordinate
seminorm fixed by the constructed ringed map and polynomial presentation. -/
structure PointComparison where
  map : spectrum T.algebra ⟶ space K X
  schemePoint_normalized : ∀ p : spectrum T.algebra,
    (map p).schemePoint = (T.algebraicMap S).base p
  evaluation_normalized : ∀ (p : spectrum T.algebra) (s : Γ(X.left, ⊤)),
    (map p).eval s (by trivial) = p.seminorm (T.coefficientMap s)

end AffineTateChart

variable {K}

/-- An actual sheaf on the prescribed valued-point topology. -/
def sheafRingedSpace (X : AlgebraicScheme K)
    (O : TopCat.Sheaf CommRingCat (space K X)) : RingedSpace where
  carrier := space K X
  presheaf := O.obj
  IsSheaf := O.property

/-- The regular-function comorphism uses the fixed actual point projection. -/
def ringedMapOf (X : AlgebraicScheme K)
    (O : TopCat.Sheaf CommRingCat (space K X))
    (r : X.left.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat (projection K X)).obj O.obj) :
    sheafRingedSpace X O ⟶ X.left.toRingedSpace :=
  InducedCategory.homMk { base := projection K X, c := r }

/-- An algebraic chart includes the entire Tate presentation and its
normalized affine map, in addition to the actual analytic chart. -/
structure AlgebraicAffinoidChart (X : AlgebraicScheme K)
    (O : TopCat.Sheaf CommRingCat (space K X))
    (r : X.left.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat (projection K X)).obj
        O.obj) where
  affine : AlgebraicScheme K
  presentation : AffineTateChart K affine
  rational : RationalRestrictionTheory presentation.algebra
  spectrum : RationalSpectrumGeometry rational
  geometry : AffinoidSheafGeometry rational spectrum
  point : presentation.PointComparison geometry
  immersion : affine ⟶ X
  isOpenImmersion : IsOpenImmersion immersion.left
  source : Opens (NonarchimedeanAnalyticSpaces.spectrum presentation.algebra)
  map : (geometry.locallyRingedSpace.restrict
    (Opens.isOpenEmbedding source)).toRingedSpace ⟶ sheafRingedSpace X O
  isOpen : IsOpenEmbedding map.hom.base
  stalkIso : ∀ q, IsIso (map.hom.stalkMap q)
  point_normalization : ∀ q, map.hom.base q = mapPoint immersion (point.map q.1)
  square : map ≫ ringedMapOf X O r =
    (geometry.locallyRingedSpace.ofRestrict
      (Opens.isOpenEmbedding source)).toShHom ≫
        (presentation.algebraicMap geometry).toShHom ≫
          immersion.left.toLRSHom.toShHom

def AlgebraicAffinoidChart.toChart {X : AlgebraicScheme K}
    {O : TopCat.Sheaf CommRingCat (space K X)} {r}
    (C : AlgebraicAffinoidChart X O r) :
    AffinoidChart (K := K) (sheafRingedSpace X O) where
  algebra := C.presentation.algebra
  rational := C.rational
  spectrum := C.spectrum
  geometry := C.geometry
  source := C.source
  map := C.map
  isOpen := C.isOpen
  stalkIso := C.stalkIso

/-- A covering algebraic atlas has actual bounded common refinements on
each overlap, as required by the analytic-space definition. -/
structure AlgebraicAffinoidAtlas (X : AlgebraicScheme K)
    (O : TopCat.Sheaf CommRingCat (space K X))
    (r : X.left.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat (projection K X)).obj
        O.obj) where
  Index : Type
  chart : Index → AlgebraicAffinoidChart X O r
  covers : ∀ p : space K X, ∃ i, p ∈ Set.range (chart i).map.hom.base
  overlaps : ∀ (i j : Index) (p : space K X),
    p ∈ Set.range (chart i).map.hom.base →
    p ∈ Set.range (chart j).map.hom.base →
    Nonempty (BoundedDiagram (chart i).toChart (chart j).toChart (𝟙 _) p)

/-- A faithful good Berkovich realization of an actual algebraic scheme.
Every chart uses the polynomial-kernel Tate model and canonical sheaf. -/
structure AnalyticSpace (X : AlgebraicScheme K) where
  structureSheaf : TopCat.Sheaf CommRingCat (space K X)
  regularMap : X.left.presheaf ⟶
    (TopCat.Presheaf.pushforward CommRingCat (projection K X)).obj
      structureSheaf.obj
  localRing : ∀ p : space K X,
    IsLocalRing (TopCat.Presheaf.stalk (C := CommRingCat) structureSheaf.obj p)
  stalk_local : ∀ p : space K X,
    letI := localRing p
    IsLocalHom ((ringedMapOf X structureSheaf regularMap).hom.stalkMap p).hom
  atlas : AlgebraicAffinoidAtlas X structureSheaf regularMap

namespace AnalyticSpace

variable {X Y : AlgebraicScheme K}

abbrev ringed (A : AnalyticSpace X) : RingedSpace :=
  sheafRingedSpace X A.structureSheaf

def algebraic (A : AnalyticSpace X) : A.ringed ⟶ X.left.toRingedSpace :=
  ringedMapOf X A.structureSheaf A.regularMap

def locallyRinged (A : AnalyticSpace X) : LocallyRingedSpace where
  toSheafedSpace := A.ringed
  isLocalRing := A.localRing

def locallyRingedMap (A : AnalyticSpace X) :
    A.locallyRinged ⟶ X.left.toLocallyRingedSpace :=
  ⟨A.algebraic.hom, A.stalk_local⟩

abbrev ringSheaf (A : AnalyticSpace X) : TopCat.Sheaf RingCat (space K X) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat)).obj A.structureSheaf

abbrev Modules (A : AnalyticSpace X) := SheafOfModules.{0} A.ringSheaf

def ringMap (A : AnalyticSpace X) : X.left.ringCatSheaf ⟶
    ((Opens.map (projection K X)).sheafPushforwardContinuous _ _ _).obj
      A.ringSheaf where
  hom := Functor.whiskerRight A.regularMap (forget₂ CommRingCat RingCat)

instance presheafRightAdjoint (A : AnalyticSpace X) :
    (PresheafOfModules.pushforward.{0} (F := Opens.map (projection K X))
      A.ringMap.hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top A.ringMap.hom)

instance sheafRightAdjoint (A : AnalyticSpace X) :
    (SheafOfModules.pushforward.{0} (F := Opens.map (projection K X))
      A.ringMap).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{0} A.ringMap).isRightAdjoint

def pullback (A : AnalyticSpace X) : X.left.Modules ⥤ A.Modules :=
  SheafOfModules.pullback.{0} (F := Opens.map (projection K X)) A.ringMap

def pushforward (A : AnalyticSpace X) : A.Modules ⥤ X.left.Modules :=
  SheafOfModules.pushforward.{0} (F := Opens.map (projection K X)) A.ringMap

def adjunction (A : AnalyticSpace X) : A.pullback ⊣ A.pushforward :=
  SheafOfModules.pullbackPushforwardAdjunction.{0} A.ringMap

instance pullbackIsLeftAdjoint (A : AnalyticSpace X) :
    A.pullback.IsLeftAdjoint :=
  A.adjunction.isLeftAdjoint

/-- Local boundedness is expressed by actual normalized bounded algebra maps
on actual chart refinements, not merely an abstract locally ringed map. -/
def IsLocallyBounded (A : AnalyticSpace X) (B : AnalyticSpace Y)
    (m : A.ringed ⟶ B.ringed) : Prop :=
  ∀ p : space K X, ∃ (i : A.atlas.Index) (j : B.atlas.Index),
    Nonempty (BoundedDiagram (A.atlas.chart i).toChart
      (B.atlas.chart j).toChart m p)

/-- Analytic morphisms have fixed points, the regular-function square, and
the source-correct local bounded-domain condition. -/
structure Morphism (A : AnalyticSpace X) (B : AnalyticSpace Y) (f : X ⟶ Y) where
  map : A.locallyRinged ⟶ B.locallyRinged
  point_map : map.base = BerkovichAnalytification.map f
  square : map.toShHom ≫ B.algebraic = A.algebraic ≫ f.left.toLRSHom.toShHom
  bounded : A.IsLocallyBounded B map.toShHom

abbrev AlgebraicCoherent (X : AlgebraicScheme K) :=
  (SheafOfModules.isFinitePresentation X.left.ringCatSheaf).FullSubcategory

abbrev Coherent (A : AnalyticSpace X) :=
  (SheafOfModules.isFinitePresentation A.ringSheaf).FullSubcategory

/-- Coherence and exactness are dependencies on this actual pullback. -/
structure CoherentPullback (A : AnalyticSpace X) : Prop where
  preserves : ∀ F : X.left.Modules, F.IsFinitePresentation →
    (A.pullback.obj F).IsFinitePresentation
  exact : PreservesFiniteLimits A.pullback

/-- GAGA concerns actual coherent objects and actual pulled module maps. -/
structure GAGA (A : AnalyticSpace X) : Prop where
  coherent : A.CoherentPullback
  fullyFaithful : ∀ F G : X.left.Modules, F.IsFinitePresentation →
    G.IsFinitePresentation →
      Function.Bijective (A.pullback.map (X := F) (Y := G))
  essential : ∀ G : A.Modules, G.IsFinitePresentation →
    ∃ F : X.left.Modules, F.IsFinitePresentation ∧
      Nonempty (A.pullback.obj F ≅ G)

attribute [local instance] HasDerivedCategory.standard

def pullbackUnitIso (A : AnalyticSpace X) :
    A.pullback.obj (SheafOfModules.unit X.left.ringCatSheaf) ≅
      SheafOfModules.unit A.ringSheaf :=
  letI : (Opens.map (projection K X)).Final := inferInstance
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{0, 0, 0, 0, 0}
    (F := Opens.map (projection K X)) A.ringMap)
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal A.ringMap)

variable (A : AnalyticSpace X) [PreservesFiniteLimits A.pullback]

instance pullbackAdditive : A.pullback.Additive :=
  Functor.additive_of_preserves_binary_products _

instance pullbackFiniteColimits : PreservesFiniteColimits A.pullback :=
  by infer_instance

abbrev derivedPullback := A.pullback.mapDerivedCategory

abbrev algebraicUnit :=
  (DerivedCategory.singleFunctor X.left.Modules 0).obj
    (SheafOfModules.unit X.left.ringCatSheaf)

abbrev analyticUnit :=
  (DerivedCategory.singleFunctor A.Modules 0).obj
    (SheafOfModules.unit A.ringSheaf)

def derivedUnitIso :
    A.derivedPullback.obj (algebraicUnit (X := X)) ≅ A.analyticUnit :=
  (A.pullback.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor A.Modules 0).mapIso A.pullbackUnitIso

/-- Coherent cohomology on actual derived module categories. -/
abbrev AlgebraicCohomology (F : X.left.Modules) (n : ℤ) :=
  algebraicUnit (X := X) ⟶
    ((DerivedCategory.singleFunctor X.left.Modules 0).obj F)⟦n⟧

abbrev AnalyticCohomology (F : X.left.Modules) (n : ℤ) :=
  A.analyticUnit ⟶
    (A.derivedPullback.obj
      ((DerivedCategory.singleFunctor X.left.Modules 0).obj F))⟦n⟧

/-- The comparison is the fixed exact pullback's map with its unit and shift. -/
def cohomologyComparison (F : X.left.Modules) (n : ℤ)
    (a : AlgebraicCohomology F n) : A.AnalyticCohomology F n :=
  A.derivedUnitIso.inv ≫ A.derivedPullback.map a ≫
    (A.derivedPullback.commShiftIso n).hom.app
      ((DerivedCategory.singleFunctor X.left.Modules 0).obj F)

end AnalyticSpace

end MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticGeometry
