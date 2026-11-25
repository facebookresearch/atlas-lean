/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicGeometricClassifyingSpaces
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Canonical finite-group power source and its native cohomology action

The source is the original affine finite-cycle sheaf, smashed with the
actual free quotient. Its normalization is tested on every original
ring-coefficient cycle by external power, unique free quotient descent,
the actual diagonal, the pulled associated bundle and Construction 5.1.
The expected class is the computed inverse of the native Thom action.

The Tate operation conjugates this source map by the independently
normalized affine/Tate comparison. Cohomology representatives are chosen
through the fixed reduced-free/Dold--Kan representability map; smash on
the localization is the native localization lift of the literal smash
functor. There is no independent function chosen as the total power.

Pointed powers require a positive number of factors. The zero-fold
cycle identity does not supply a pointed power operation.

Source: Voevodsky, arXiv:math/0107109v1, Constructions 5.1/5.3,
Equation 5.2, Lemmas 5.4/5.5 and Section 6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicCanonicalPowerModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes EffectiveMotivicComplexModels PointedMotivicModels
open PointedMotivicQuotients PointedMotivicQuotientMaps ReducedMotivicCohomologyModels
open MotivicRealizationComparisons MotivicEilenbergMacLaneModels
open MotivicFinitePermutationModels MotivicPermutationBundleModels MotivicFinitePowerCycles
open MotivicPowerQuotientModels MotivicPowerDescentModels MotivicPowerThomModels
open MotivicAffineQuotientModels MotivicAffineTateComparisons
open MotivicCycleProducts MotivicTensorOperations MotivicCohomologyProducts
open MotivicPointedProducts MotivicBundleModels GeneralMotivicBundleThom
open FiniteBundleCycleRealization FiniteBundleThomComparisons MotivicGeometricClassifyingSpaces

variable {k : Type} [Field k]

/-- The original smash maps form the actual source functor. -/
def smashRightFunctor (W : PointedSpaces (k := k)) :
    PointedSpaces (k := k) ⥤ PointedSpaces (k := k) where
  obj X := smash X W
  map f := smashMap f (𝟙 W)
  map_id X := by
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext <;> simp [smashMap, pushout.map]
    all_goals exact (Category.comp_id _).symm
  map_comp f g := by
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext <;> simp [smashMap, pushout.map]

variable {P : SmoothProductSystem k} (A : StandardSchemes P)

/-- The only descent input is inversion of the original motivic weak maps. -/
abbrev SmashLocalizationSource (W : PointedSpaces (k := k)) : Prop :=
  (motivicWeakMaps A).IsInvertedBy (smashRightFunctor W ⋙ motivicQ A)

/-- Smash in the motivic localization is its native universal lift. -/
def localizedSmashRight (W : PointedSpaces (k := k)) (h : SmashLocalizationSource A W) :
    MotivicHomotopyCategory A ⥤ MotivicHomotopyCategory A :=
  Localization.Construction.lift (smashRightFunctor W ⋙ motivicQ A) h

variable
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D₀ : CompositionSystem k} {G₀ : GraphSystem k}
  [CorrespondenceLaws D₀ G₀] [CorrespondenceAdditivity D₀ G₀]
  {E : ExternalSystem P} {C : CorrespondenceProductModel D₀ G₀ P E}
  {R₀ : RepresentableSystem D₀ G₀} {S₀ : TransferSheafificationModel D₀ G₀}
  {T : CycleComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R₀)}
  (N : NisTensorSystem k) [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  (B : CoefficientComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R₀) (S := S₀) T N)
  (I : KInjectiveResolutionSystem k) (Q : PointedSimplicialModuleFunctor k)
  (F : ReducedFreeNisSystem k) (J : ReducedFreeAdjunction F Q)
  (Msec : ModuleSectionSystem Q)
  (V₀ : AffineTateMapSystem (N := N) (B := B) (I := I) (Q := Q))
  (Rep : RepresentabilityMap (A := A) B I Q F J)

/-- The actual affine sheaf power morphism, in the native motivic category. -/
abbrev PowerRealizationMorphism (W : PointedSpaces (k := k)) (i n : ℕ)
    (R : Type 1) [CommRing R] :=
  (motivicQ A).obj (smash
    (affineK (D := D₀) (G := G₀) (P := P) (A := A) (R := R₀) N Q i
      (ModuleCat.of ℤ R)) W) ⟶
    (motivicQ A).obj (K B I Q (2 * ((n * i : ℕ) : ℤ)) ((n * i : ℕ) : ℤ)
      (ModuleCat.of ℤ R))

/-- The comparison inverse is the inverse of the original native weak map. -/
def tatePowerMorphism (W : PointedSpaces (k := k)) (i n : ℕ) (R : Type 1) [CommRing R]
    (hSmash : SmashLocalizationSource A W)
    (hV : MotivicWeakEquivalence A (V₀.map i (ModuleCat.of ℤ R)))
    (f : PowerRealizationMorphism A N B I Q W i n R) :
    (motivicQ A).obj (smash (K B I Q (2 * (i : ℤ)) (i : ℤ) (ModuleCat.of ℤ R)) W) ⟶
      (motivicQ A).obj (K B I Q (2 * ((n * i : ℕ) : ℤ)) ((n * i : ℕ) : ℤ)
        (ModuleCat.of ℤ R)) := by
  let a := V₀.map i (ModuleCat.of ℤ R)
  haveI : IsIso ((motivicQ A).map (smashMap a (𝟙 W))) := hSmash a hV
  exact inv ((motivicQ A).map (smashMap a (𝟙 W))) ≫ f

/-- The total power on actual motivic hypercohomology is derived from this source map. -/
def totalPower (W : PointedSpaces (k := k)) (i n : ℕ) (R : Type 1) [CommRing R]
    (_hn : 0 < n) (hSmash : SmashLocalizationSource A W)
    (hV : MotivicWeakEquivalence A (V₀.map i (ModuleCat.of ℤ R)))
    (f : PowerRealizationMorphism A N B I Q W i n R)
    (X : PointedSpaces (k := k))
    (hRep : Function.Bijective (Rep.map X (2 * (i : ℤ)) (i : ℤ) (ModuleCat.of ℤ R)))
    (u : ReducedCohomology B F X (2 * (i : ℤ)) (i : ℤ) (ModuleCat.of ℤ R)) :
    ReducedCohomology B F (smash X W) (2 * ((n * i : ℕ) : ℤ)) ((n * i : ℕ) : ℤ)
      (ModuleCat.of ℤ R) :=
  Rep.map (smash X W) (2 * ((n * i : ℕ) : ℤ)) ((n * i : ℕ) : ℤ) (ModuleCat.of ℤ R)
    ((localizedSmashRight A W hSmash).map
      ((Equiv.ofBijective (Rep.map X (2 * (i : ℤ)) (i : ℤ) (ModuleCat.of ℤ R)) hRep).symm u) ≫
        tatePowerMorphism A N B I Q V₀ W i n R hSmash hV f)

variable {J₀ : TorusConcatenation A}
  {M₀ : SingularCycleProduct (S := S₀) N T J₀} {Z₀ : EilenbergZilberModel N}
  {V₁ : NegativeTensorComparison N}
  (K₀ : CoefficientMultiplicationSystem N T B M₀ Z₀ V₁)
  (F₀ : KFlatResolutionSystem N) (D : DerivedTensorSource N F₀)
  (S : DerivedTensorShifts N F₀ D) (M₁ : ReducedSmashComultiplication N F)
  (hF : IsFreeTensorComparison N F₀ D F) (U₀ : IntegerCoefficientUnits)
  (T₀ : AffineThomCycleSections (D₀ := D₀) (G := G₀) (P := P)
    (A := A) (R := R₀) (N := N) (Q := Q) (M := Msec))
  {H : Type} [Group H] [Fintype H]
  [Gconst : ConstantGroupGeometry (k := k) (H := H)]
  (U : FreeQuotient (k := k) (H := H)) {n : ℕ}
  (r : H →* Equiv.Perm (Fin n)) (i : ℕ) (R : Type 1) [CommRing R]

/-- A test retains the entire original cycle, quotient, diagonal and Thom source.
Affine X permits a scheme quotient. A larger X can use the same predicate
with a supplied source quotient in a separate comparison construction. -/
structure FinitePowerThomTest where
  X : SmoothScheme k
  [affine : IsAffine X.scheme.left]
  sourceQuotient : PowerQuotient P U r X
  vector : VectorQuotient P U r A i
  vectorNormalized : vector.IsNormalized P U r
  input : CoefficientCycles X (A.affine i) R
  descent : CycleDescent P U r sourceQuotient D₀ G₀ R A i vector input E
  diagonal : DiagonalDescent P U r sourceQuotient
  pullback : PullbackPowerBundle P U r A i vector (X := X)
  cycle : RelativePowerCycle P U r sourceQuotient D₀ G₀ R A i vector input descent diagonal pullback
  complement : PowerComplement (P := P) U r i vector pullback
  geometry : ∀ z : pullback.bundle.RelativeGenerator,
    CycleGeometry A pullback.bundle complement.bundle complement.sum complement.frame z
  null : ComplementNull (D₀ := D₀) (G₀ := G₀) (R := R₀) A pullback.bundle
    complement.bundle complement.sum complement.frame N Q Msec geometry (ModuleCat.of ℤ R) cycle.value
  thomDiagonal : BundleThomDiagonals complement.bundle
  thom : ThomClass N B I Q F J V₀ T₀ complement.bundle
  thomBijective : Function.Bijective (baseThomAction N B I Q F J V₀ T₀ K₀ F₀ D S M₁ hF U₀
    complement.bundle thomDiagonal thom (2 * ((n * i : ℕ) : ℤ)) ((n * i : ℕ) : ℤ)
      (ModuleCat.of ℤ R))

attribute [instance] FinitePowerThomTest.affine

/-- The expected power is the computed native inverse Thom class of this exact cycle. -/
def FinitePowerThomTest.expected
    (t : FinitePowerThomTest A N B I Q F J Msec V₀ K₀ F₀ D S M₁ hF U₀ T₀ U r i R) :
    ReducedCohomology B F (representedPointed (P.obj t.X U.base))
      (2 * ((n * i : ℕ) : ℤ)) ((n * i : ℕ) : ℤ) (ModuleCat.of ℤ R) :=
  powerBundleClass N B I Q F J Msec V₀ U r i t.vector t.pullback t.complement t.geometry R
    t.cycle.value t.null K₀ F₀ D S M₁ hF U₀ T₀ t.thomDiagonal t.thom t.thomBijective

/-- Source normalization uses every original coefficient cycle and the actual Thom equation. -/
def IsFinitePowerNormalization (hn : 0 < n)
    (hSmash : SmashLocalizationSource A (representedPointed U.base))
    (hV : MotivicWeakEquivalence A (V₀.map i (ModuleCat.of ℤ R)))
    (hRep : ∀ X : PointedSpaces (k := k),
      Function.Bijective (Rep.map X (2 * (i : ℤ)) (i : ℤ) (ModuleCat.of ℤ R)))
    (f : PowerRealizationMorphism A N B I Q (representedPointed U.base) i n R) : Prop :=
  ∀ t : FinitePowerThomTest A N B I Q F J Msec V₀ K₀ F₀ D S M₁ hF U₀ T₀ U r i R,
    ReducedMotivicCohomologyModels.pullback B F (productPointedMap (P := P) t.X U.base)
      (2 * ((n * i : ℕ) : ℤ)) ((n * i : ℕ) : ℤ) (ModuleCat.of ℤ R)
      (totalPower A N B I Q F J V₀ Rep (representedPointed U.base) i n R hn hSmash hV f
        (representedPointed t.X) (hRep _) (affineInputClass N B I Q F J Msec V₀ i R t.X t.input)) =
          t.expected A N B I Q F J Msec V₀ K₀ F₀ D S M₁ hF U₀ T₀ U r i R

/-- Restriction of the global affine sheaf power through the actual finite-stage cocone. -/
def geometricStagePower (G : GeometricApproximation (k := k) (H := H))
    (f : PowerRealizationMorphism A N B I Q (geometricClassifyingSpace G) i n R) (m : ℕ) :
    PowerRealizationMorphism A N B I Q (representedPointed (G.step m).quotient.base) i n R :=
  (motivicQ A).map (smashMap (𝟙 _) (stageMap G m)) ≫ f

/-- An affine replacement is an actual equivariant free-torsor map, with its native motivic comparison. -/
structure AffineFreeReplacement where
  source : FreeQuotient (k := k) (H := H)
  [affine : IsAffine source.base.scheme.left]
  arrow : FreeQuotientArrow source U
  weak : MotivicWeakEquivalence A (representedMap arrow.base)

attribute [instance] AffineFreeReplacement.affine

/-- Base change is the actual source quotient map, rather than an independent operation. -/
def baseChangePower {U' : FreeQuotient (k := k) (H := H)} (a : FreeQuotientArrow U' U)
    (f : PowerRealizationMorphism A N B I Q (representedPointed U.base) i n R) :
    PowerRealizationMorphism A N B I Q (representedPointed U'.base) i n R :=
  (motivicQ A).map (smashMap (𝟙 _) (representedMap a.base)) ≫ f

/-- Whole affine source comparisons keep the finite-power normalization nonvacuous on local replacements. -/
def IsAffineCoverPowerNormalization (hn : 0 < n)
    (hSmash : ∀ W : PointedSpaces (k := k), SmashLocalizationSource A W)
    (hV : MotivicWeakEquivalence A (V₀.map i (ModuleCat.of ℤ R)))
    (hRep : ∀ X : PointedSpaces (k := k),
      Function.Bijective (Rep.map X (2 * (i : ℤ)) (i : ℤ) (ModuleCat.of ℤ R)))
    (f : PowerRealizationMorphism A N B I Q (representedPointed U.base) i n R) : Prop :=
  ∀ (U' : FreeQuotient (k := k) (H := H)) (_ : IsAffine U'.base.scheme.left)
    (a : FreeQuotientArrow U' U),
    IsFinitePowerNormalization A N B I Q F J Msec V₀ Rep K₀ F₀ D S M₁ hF U₀ T₀ U' r i R
      hn (hSmash _) hV hRep (baseChangePower A N B I Q U (i := i) (n := n) R a f)

/-- The global map retains Construction 5.3 on every original geometric free quotient. -/
def IsGeometricPowerNormalization (G : GeometricApproximation (k := k) (H := H))
    (hn : 0 < n)
    (hSmash : ∀ W : PointedSpaces (k := k), SmashLocalizationSource A W)
    (hV : MotivicWeakEquivalence A (V₀.map i (ModuleCat.of ℤ R)))
    (hRep : ∀ X : PointedSpaces (k := k),
      Function.Bijective (Rep.map X (2 * (i : ℤ)) (i : ℤ) (ModuleCat.of ℤ R)))
    (f : PowerRealizationMorphism A N B I Q (geometricClassifyingSpace G) i n R) : Prop :=
  ∀ m : ℕ,
    IsFinitePowerNormalization A N B I Q F J Msec V₀ Rep K₀ F₀ D S M₁ hF U₀ T₀
      (G.step m).quotient r i R hn (hSmash _) hV hRep
        (geometricStagePower A N B I Q (i := i) (n := n) R G f m) ∧
    IsAffineCoverPowerNormalization A N B I Q F J Msec V₀ Rep K₀ F₀ D S M₁ hF U₀ T₀
      (G.step m).quotient r i R hn hSmash hV hRep
        (geometricStagePower A N B I Q (i := i) (n := n) R G f m)

end MathlibExt.AlgebraicGeometry.MotivicCanonicalPowerModels
