/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MotivicPowerOperationLaws

/-!
# Canonical reduced powers and the remaining theorem requests

`canonicalPowerOperations` requests the canonical source-normalized geometric power maps and
completed coefficient decomposition together with Voevodsky's operation laws for them
(`MotivicPowerOperationLaws.PowerOperationLaws`): the normalization on cycle classes of smooth
affine schemes does not determine the power maps on arbitrary pointed simplicial spaces, so the
laws are not requested for every source with that normalization. B is an independent c
coefficient, with beta P = B among the laws.

Cartan is recorded through the actual native classifying-space product diagonal. Its completed
expansion retains tau and rho at ell=2. No bidegree-inconsistent printed odd-square formula is
introduced. The Bockstein laws not involving the powers remain separate theorem requests.

Full uniqueness/generation of all bistable operations and optional Adem-provider reconstruction
remain outside the selected source packet.

Source: Voevodsky, arXiv:math/0107109v1, Equation 8.1,
Equation 9.1, Theorems 9.3/9.4, Lemmas 5.7/9.2/9.5 and Proposition 2.6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MotivicReducedPowerWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes EffectiveMotivicComplexModels PointedMotivicModels
open PointedMotivicQuotients ReducedMotivicCohomologyModels MotivicRealizationComparisons
open MotivicAffineQuotientModels MotivicAffineTateComparisons
open MotivicCycleProducts MotivicTensorOperations MotivicCohomologyProducts MotivicPointedProducts
open GeneralMotivicBundleThom MotivicFinitePermutationModels
open MotivicGeometricClassifyingSpaces MotivicPrimeClassGeometry MotivicPrimeClasses
open MotivicBocksteinModels MotivicTorusClassModels
open MotivicCanonicalPowerModels MotivicPowerCoefficients MotivicPowerSuspensions
open MotivicReducedPowerOperations MotivicPowerCartanModels

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

/-- Construct the canonical reduced powers: the source family with native cycle normalization and
the completed expansion, together with Voevodsky's operation laws for it (`PowerOperationLaws`).
The laws are requested for this constructed source, not for every source with the same
normalization on schemes, which does not determine the power maps. -/
def_wanted canonicalPowerOperations [PerfectField k] (hchar : (ell : k) ≠ 0)
    {Ls : CircleCycleOrientation (S₀ := S₀) T F}
    (σ : SuspensionEquivalences T F N B Zi K₀ F₀ D S M₁ hF U₀ Ls Lt ell) :
    {source : CanonicalPowerCoefficientSource (canonical := canonical) (Rep := Rep) (U₀ := U₀)
      (hRep := hRep) (hSmash := hSmash) (Eprime := Eprime) (point := point)
      (t := t) (delta := delta) (c := c) hchar //
      MotivicPowerOperationLaws.PowerOperationLaws source σ}

/-- The product diagonal is fixed on every original simplex and classifying-space coordinate. -/
def_wanted classifyingPowerDiagonal (X Y : PointedSpaces (k := k)) :
    ClassifyingPowerDiagonal (geometricClassifyingSpace G) X Y

/-- The square-zero statement concerns the original coefficient cone boundary. -/
theorem_wanted beta_squared (X : PointedSpaces (k := k)) (p q : ℤ)
    (betaSource : CoefficientConeSource B (modSequence ell) q)
    (u : ReducedCohomology B F X p q (ModCoefficients ell)) :
    bockstein B ell F X (p + 1) q betaSource (bockstein B ell F X p q betaSource u) = 0

/-- Equation 8.1 retains the sign (-1)^p of the first input cohomological degree. -/
theorem_wanted beta_Cartan (X Y : PointedSpaces (k := k)) (p q r s : ℤ)
    (betaQ : CoefficientConeSource B (modSequence ell) q)
    (betaS : CoefficientConeSource B (modSequence ell) s)
    (betaQS : CoefficientConeSource B (modSequence ell) (q + s))
    (u : ReducedCohomology B F X p q (ModCoefficients ell))
    (v : ReducedCohomology B F Y r s (ModCoefficients ell)) :
    bockstein B ell F (smash X Y) (p + r) (q + s) betaQS
      (externalCup N B K₀ F₀ D S F M₁ hF X Y p q r s _ _ _
        (ringCoefficientMultiplication (ULift.{1} (ZMod ell))) u v) =
      regrade N (B := B) (R₁ := F) (smash X Y) (ModCoefficients ell) (by omega) rfl
        (externalCup N B K₀ F₀ D S F M₁ hF X Y (p + 1) q r s _ _ _
          (ringCoefficientMultiplication (ULift.{1} (ZMod ell)))
          (bockstein B ell F X p q betaQ u) v) +
      p.negOnePow •
        regrade N (B := B) (R₁ := F) (smash X Y) (ModCoefficients ell) (by omega) rfl
          (externalCup N B K₀ F₀ D S F M₁ hF X Y p q (r + 1) s _ _ _
            (ringCoefficientMultiplication (ULift.{1} (ZMod ell))) u
            (bockstein B ell F Y r s betaS v))

end WantedExt.AlgebraicGeometry.MotivicReducedPowerWanted
