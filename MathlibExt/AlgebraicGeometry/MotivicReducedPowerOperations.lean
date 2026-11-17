/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicPowerSuspensions

/-!
# Reduced power operations from the canonical native source coefficients

The source packet consists of the actual geometrically normalized
affine sheaf power maps and the actual completed c/d decompositions.
The independent canonical affine/Tate source is retained as a parameter;
a zero or sign-changed comparison does not define this packet.

For every diagonal class the total power is first computed on actual
motivic hypercohomology, and its independent D/C coefficients define P/B.
For all integer p,q the operations are the native circle/Tate suspension
extension of these same diagonal coefficients.

P^0, negative-operation vanishing, beta P = B, Cartan and suspension
independence are theorem targets in the companion, not source fields.
The packet does not assert generation of all bistable operations.

Source: Voevodsky, arXiv:math/0107109v1, Constructions 5.1/5.3,
Theorems 6.14/6.16, Equation 9.1 and Proposition 2.6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicReducedPowerOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes EffectiveMotivicComplexModels PointedMotivicModels
open PointedMotivicQuotients ReducedMotivicCohomologyModels MotivicRealizationComparisons
open MotivicAffineQuotientModels MotivicAffineTateComparisons
open MotivicCycleProducts MotivicTensorOperations MotivicCohomologyProducts MotivicPointedProducts
open GeneralMotivicBundleThom MotivicFinitePermutationModels
open MotivicGeometricClassifyingSpaces MotivicPrimeClassGeometry MotivicPrimeClasses
open MotivicBocksteinModels MotivicTorusClassModels
open MotivicCanonicalPowerModels MotivicPowerCoefficients MotivicPowerSuspensions

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D₀ : CompositionSystem k} {G₀ : GraphSystem k}
  [CorrespondenceLaws D₀ G₀] [CorrespondenceAdditivity D₀ G₀]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D₀ G₀ P E} {A : StandardSchemes P}
  {R₀ : RepresentableSystem D₀ G₀} {S₀ : TransferSheafificationModel D₀ G₀}
  {T : CycleComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R₀)}
  {N : NisTensorSystem k} [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  {B : CoefficientComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R₀) (S := S₀) T N}
  {I : KInjectiveResolutionSystem k} {Q : PointedSimplicialModuleFunctor k}
  {F : ReducedFreeNisSystem k} {J : ReducedFreeAdjunction F Q}
  {Msec : ModuleSectionSystem Q}
  {V : AffineTateMapSystem (N := N) (B := B) (I := I) (Q := Q)}
  {T₀ : AffineThomCycleSections (D₀ := D₀) (G := G₀) (P := P)
    (A := A) (R := R₀) (N := N) (Q := Q) (M := Msec)}
  {J₀ : TorusConcatenation A}
  {M₀ : SingularCycleProduct (S := S₀) N T J₀} {EZ : EilenbergZilberModel N}
  {V₀ : NegativeTensorComparison N}
  {K₀ : CoefficientMultiplicationSystem N T B M₀ EZ V₀}
  {F₀ : KFlatResolutionSystem N} {D : DerivedTensorSource N F₀}
  {S : DerivedTensorShifts N F₀ D} {M₁ : ReducedSmashComultiplication N F}
  {hF : IsFreeTensorComparison N F₀ D F} {U₀ : IntegerCoefficientUnits}
  {Kt : PointedTateProducts N B I Q F J K₀ F₀ D S M₁ hF}
  {Et : AffineCycleProduct (D := D₀) (G := G₀) (P := P) (A := A) (R := R₀) N Q E Msec}
  {O : MotivicTateThomModels.TorusOpenAffine (P := P) (A := A)}
  {Raff : MotivicTateThomModels.RelativeA1CofiberSource O}
  {Caff : MotivicCofiberComparisons.CofiberChainSource F
    (MotivicTateThomModels.relativeTorusMap O)}
  {Lt : TorusCycleLinearization (S := S₀) T F}
  {Zi : IntegerCoefficientInclusions (N := N) (T := T) (B := B)}
  {canonical : CanonicalAffineSource N B I Q F J V T₀ K₀ F₀ D S M₁ hF
    Kt Et O Raff Caff Lt Zi}
  {Rep : RepresentabilityMap (A := A) B I Q F J}
  {hRep : ∀ (X : PointedSpaces (k := k)) (p q : ℤ) (V₁ : ModuleCat.{1} ℤ),
    Function.Bijective (Rep.map X p q V₁)}
  {hSmash : ∀ W : PointedSpaces (k := k), SmashLocalizationSource A W}
  {ell : ℕ} [Fact ell.Prime]
  [Gprime : ConstantGroupGeometry (k := k) (H := Equiv.Perm (Fin ell))]
  {G : GeometricApproximation (k := k) (H := Equiv.Perm (Fin ell))}
  {Eprime : PrimeThomDiagram G} {point : BasedApproximation P G}
  {t : GlobalPrimeThomClass N B I Q F J V T₀ Eprime}
  {delta : CoefficientConeSource B (integralSequence ell) (primeWeight ell)}
  {c : BasedIntegralLift N B I Q F J V T₀ Eprime point t delta}

/-- A canonical source has native cycle normalization and completed coefficient reconstruction, without operation-law fields. -/
structure CanonicalPowerCoefficientSource [PerfectField k] (hchar : (ell : k) ≠ 0) where
  power : ∀ d : ℕ, PowerRealizationMorphism A N B I Q (geometricClassifyingSpace G) d ell
    (ULift.{1} (ZMod ell))
  normalization : ∀ d : ℕ,
    IsGeometricPowerNormalization A N B I Q F J Msec V Rep K₀ F₀ D S M₁ hF U₀ T₀
      (standardPermutation (ell := ell)) d (ULift.{1} (ZMod ell)) G
      (Fact.out : ell.Prime).pos hSmash (canonical.weak d _) (fun X => hRep X _ _ _) (power d)
  decomposition : ∀ (X : PointedSpaces (k := k)) (p q : ℤ),
    CompletedBSDecomposition N B I Q F J V T₀ K₀ F₀ D S M₁ hF Eprime point t delta c X p q

variable [PerfectField k] {hchar : (ell : k) ≠ 0}
  (source : CanonicalPowerCoefficientSource (canonical := canonical) (Rep := Rep)
    (hRep := hRep) (hSmash := hSmash) (U₀ := U₀) (Eprime := Eprime) (point := point)
    (t := t) (delta := delta) (c := c) hchar)

/-- The actual canonical total power of a diagonal class, before extracting individual coefficients. -/
def canonicalTotalPower (X : PointedSpaces (k := k)) (d : ℕ)
    (w : ReducedCohomology B F X (2 * (d : ℤ)) (d : ℤ) (ModCoefficients ell)) :
    ReducedCohomology B F (smash X (geometricClassifyingSpace G))
      (2 * ((ell * d : ℕ) : ℤ)) ((ell * d : ℕ) : ℤ) (ModCoefficients ell) :=
  totalPower A N B I Q F J V Rep (geometricClassifyingSpace G) d ell (ULift.{1} (ZMod ell))
    (Fact.out : ell.Prime).pos (hSmash _) (canonical.weak d _) (source.power d) X
      (hRep X _ _ _) w

/-- Equation 9.1 defines the complete independent D/C coefficient series. -/
def coefficients (X : PointedSpaces (k := k)) (d : ℕ)
    (w : ReducedCohomology B F X (2 * (d : ℤ)) (d : ℤ) (ModCoefficients ell)) :
    CompletedCoefficients (ell := ell) N B F X (2 * ((ell * d : ℕ) : ℤ)) ((ell * d : ℕ) : ℤ) :=
  (source.decomposition X _ _).expand (canonicalTotalPower source X d w)

/-- The diagonal P operation is the source D coefficient indexed by d-j. -/
def diagonalP (j : ℤ) (d : ℕ) (X : PointedSpaces (k := k))
    (w : ReducedCohomology B F X (2 * (d : ℤ)) (d : ℤ) (ModCoefficients ell)) :
    ReducedCohomology B F X (2 * (d : ℤ) + pShift ell j) ((d : ℤ) + qShift ell j)
      (ModCoefficients ell) :=
  PDiagonal N B F X d j (coefficients source X d w)

/-- The diagonal B operation is the independent source C coefficient indexed by d-j. -/
def diagonalB (j : ℤ) (d : ℕ) (X : PointedSpaces (k := k))
    (w : ReducedCohomology B F X (2 * (d : ℤ)) (d : ℤ) (ModCoefficients ell)) :
    ReducedCohomology B F X (2 * (d : ℤ) + pShift ell j + 1) ((d : ℤ) + qShift ell j)
      (ModCoefficients ell) :=
  BDiagonal N B F X d j (coefficients source X d w)

variable {Ls : CircleCycleOrientation (S₀ := S₀) T F}
  (σ : SuspensionEquivalences T F N B Zi K₀ F₀ D S M₁ hF U₀ Ls Lt ell)

/-- P^j on every integer bidegree is the actual circle/Tate extension of its D coefficient. -/
def reducedPower (j : ℤ) (X : PointedSpaces (k := k)) (p q : ℤ)
    (w : ReducedCohomology B F X p q (ModCoefficients ell)) :
    ReducedCohomology B F X (p + pShift ell j) (q + qShift ell j) (ModCoefficients ell) :=
  extendDiagonalOperation σ (pShift ell j) (qShift ell j) (diagonalP source j) X p q w

/-- B^j on every integer bidegree is the same source suspension extension of the independent C coefficient. -/
def bocksteinPower (j : ℤ) (X : PointedSpaces (k := k)) (p q : ℤ)
    (w : ReducedCohomology B F X p q (ModCoefficients ell)) :
    ReducedCohomology B F X (p + pShift ell j + 1) (q + qShift ell j) (ModCoefficients ell) :=
  regrade N (B := B) (R₁ := F) X (ModCoefficients ell) (by omega) rfl
    (extendDiagonalOperation σ (pShift ell j + 1) (qShift ell j)
      (fun d X w => regrade N (B := B) (R₁ := F) X (ModCoefficients ell) (by omega) rfl
        (diagonalB source j d X w)) X p q w)

end MathlibExt.AlgebraicGeometry.MotivicReducedPowerOperations
