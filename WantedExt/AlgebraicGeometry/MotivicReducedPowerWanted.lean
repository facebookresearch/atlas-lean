/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MotivicPowerCartanModels

/-!
# Canonical reduced-power source assembly and independent theorem requests

The constructor requests only the original source-normalized geometric
power maps and completed coefficient decomposition. The operation laws
are separate direct requests on the resulting native P/B definitions.
B is an independent c coefficient, with beta P = B requested afterward.

Cartan is recorded through the actual native classifying-space product
diagonal. Its completed expansion retains tau and rho at ell=2. No
bidegree-inconsistent printed odd-square formula is introduced.

All negative operation indices, naturality and both source suspension
identities are explicit theorem targets. Full uniqueness/generation of
all bistable operations and optional Adem-provider reconstruction remain
outside the selected source packet.

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

/-- Construct the canonical source family with native cycle normalization and the formal completed expansion. -/
def_wanted canonicalPowerCoefficientSource [PerfectField k] (hchar : (ell : k) ≠ 0) :
    CanonicalPowerCoefficientSource (canonical := canonical) (Rep := Rep) (U₀ := U₀)
      (hRep := hRep) (hSmash := hSmash) (Eprime := Eprime) (point := point)
      (t := t) (delta := delta) (c := c) hchar

variable [PerfectField k] {hchar : (ell : k) ≠ 0}
  (source : CanonicalPowerCoefficientSource (canonical := canonical) (Rep := Rep) (U₀ := U₀)
    (hRep := hRep) (hSmash := hSmash) (Eprime := Eprime) (point := point)
    (t := t) (delta := delta) (c := c) hchar)
  {Ls : CircleCycleOrientation (S₀ := S₀) T F}
  (σ : SuspensionEquivalences T F N B Zi K₀ F₀ D S M₁ hF U₀ Ls Lt ell)

/-- The product diagonal is fixed on every original simplex and classifying-space coordinate. -/
def_wanted classifyingPowerDiagonal (X Y : PointedSpaces (k := k)) :
    ClassifyingPowerDiagonal (geometricClassifyingSpace G) X Y

/-- Lemma 5.7's Cartan source equation uses the actual native shared-BS diagonal and cup. -/
theorem_wanted totalPowerProduct (X Y : PointedSpaces (k := k)) (d e : ℕ)
    (diag : ClassifyingPowerDiagonal (geometricClassifyingSpace G) X Y)
    (u : ReducedCohomology B F X (2 * (d : ℤ)) (d : ℤ) (ModCoefficients ell))
    (v : ReducedCohomology B F Y (2 * (e : ℤ)) (e : ℤ) (ModCoefficients ell)) :
    canonicalTotalPower source (smash X Y) (d + e)
      (regrade N (B := B) (R₁ := F) (smash X Y) (ModCoefficients ell)
        (by push_cast; ring) (by push_cast; ring)
        (externalCup N B K₀ F₀ D S F M₁ hF X Y (2 * (d : ℤ)) (d : ℤ)
          (2 * (e : ℤ)) (e : ℤ) _ _ _ (ringCoefficientMultiplication (ULift.{1} (ZMod ell))) u v)) =
      ReducedMotivicCohomologyModels.pullback B F diag.map
        (2 * ((ell * (d + e) : ℕ) : ℤ)) ((ell * (d + e) : ℕ) : ℤ) (ModCoefficients ell)
        (regrade N (B := B) (R₁ := F)
          (smash (smash X (geometricClassifyingSpace G)) (smash Y (geometricClassifyingSpace G)))
          (ModCoefficients ell) (by push_cast; ring) (by push_cast; ring)
          (externalCup N B K₀ F₀ D S F M₁ hF
            (smash X (geometricClassifyingSpace G)) (smash Y (geometricClassifyingSpace G))
            (2 * ((ell * d : ℕ) : ℤ)) ((ell * d : ℕ) : ℤ)
            (2 * ((ell * e : ℕ) : ℤ)) ((ell * e : ℕ) : ℤ) _ _ _
            (ringCoefficientMultiplication (ULift.{1} (ZMod ell)))
            (canonicalTotalPower source X d u) (canonicalTotalPower source Y e v)))

/-- Theorem 9.4 is a target on the canonical operation, rather than a source field. -/
theorem_wanted P_zero (X : PointedSpaces (k := k)) (p q : ℤ)
    (u : ReducedCohomology B F X p q (ModCoefficients ell)) :
    regrade N (B := B) (R₁ := F) X (ModCoefficients ell)
      (by simp [pShift]) (by simp [qShift]) (reducedPower source σ 0 X p q u) = u

/-- Theorem 9.3's negative operation vanishing is separate from the coefficient-index convention. -/
theorem_wanted P_negative (j : ℤ) (hj : j < 0) (X : PointedSpaces (k := k)) (p q : ℤ)
    (u : ReducedCohomology B F X p q (ModCoefficients ell)) :
    reducedPower source σ j X p q u = 0

/-- The independent c coefficient also has the source negative-operation vanishing theorem. -/
theorem_wanted B_negative (j : ℤ) (hj : j < 0) (X : PointedSpaces (k := k)) (p q : ℤ)
    (u : ReducedCohomology B F X p q (ModCoefficients ell)) :
    bocksteinPower source σ j X p q u = 0

/-- Lemma 9.5 relates the native coefficient boundary to the independently defined c coefficient. -/
theorem_wanted beta_P (j : ℤ) (X : PointedSpaces (k := k)) (p q : ℤ)
    (betaSource : CoefficientConeSource B (modSequence ell) (q + qShift ell j))
    (u : ReducedCohomology B F X p q (ModCoefficients ell)) :
    bockstein B ell F X (p + pShift ell j) (q + qShift ell j) betaSource
      (reducedPower source σ j X p q u) = bocksteinPower source σ j X p q u

/-- The other half of Lemma 9.5 remains a target on the native c coefficient. -/
theorem_wanted beta_B (j : ℤ) (X : PointedSpaces (k := k)) (p q : ℤ)
    (betaSource : CoefficientConeSource B (modSequence ell) (q + qShift ell j))
    (u : ReducedCohomology B F X p q (ModCoefficients ell)) :
    bockstein B ell F X (p + pShift ell j + 1) (q + qShift ell j) betaSource
      (bocksteinPower source σ j X p q u) = 0

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

/-- Naturality is a theorem on the actual all-degree suspension extension. -/
theorem_wanted P_natural (j : ℤ) (X Y : PointedSpaces (k := k)) (a : X ⟶ Y) (p q : ℤ)
    (u : ReducedCohomology B F Y p q (ModCoefficients ell)) :
    reducedPower source σ j X p q (ReducedMotivicCohomologyModels.pullback B F a p q
      (ModCoefficients ell) u) =
    ReducedMotivicCohomologyModels.pullback B F a (p + pShift ell j) (q + qShift ell j)
      (ModCoefficients ell) (reducedPower source σ j Y p q u)

/-- The independent B extension has the same native naturality target. -/
theorem_wanted B_natural (j : ℤ) (X Y : PointedSpaces (k := k)) (a : X ⟶ Y) (p q : ℤ)
    (u : ReducedCohomology B F Y p q (ModCoefficients ell)) :
    bocksteinPower source σ j X p q (ReducedMotivicCohomologyModels.pullback B F a p q
      (ModCoefficients ell) u) =
    ReducedMotivicCohomologyModels.pullback B F a (p + pShift ell j + 1) (q + qShift ell j)
      (ModCoefficients ell) (bocksteinPower source σ j Y p q u)

/-- The selected P extension commutes with the actual ordered-circle suspension source. -/
theorem_wanted P_simplicialSuspension (j : ℤ) (X : PointedSpaces (k := k)) (p q : ℤ)
    (u : ReducedCohomology B F X p q (ModCoefficients ell)) :
    regrade N (B := B) (R₁ := F) (smash X (simplicialCircle (k := k))) (ModCoefficients ell)
      (by omega) rfl
      (reducedPower source σ j (smash X (simplicialCircle (k := k))) (p + 1) q
        (σ.simplicial X p q u)) =
    σ.simplicial X (p + pShift ell j) (q + qShift ell j) (reducedPower source σ j X p q u)

/-- The selected P extension commutes with the actual torus graph suspension source. -/
theorem_wanted P_torusSuspension (j : ℤ) (X : PointedSpaces (k := k)) (p q : ℤ)
    (u : ReducedCohomology B F X p q (ModCoefficients ell)) :
    regrade N (B := B) (R₁ := F) (smash X (pointedTorus (P := P) (A := A))) (ModCoefficients ell)
      (by omega) (by omega)
      (reducedPower source σ j (smash X (pointedTorus (P := P) (A := A))) (p + 1) (q + 1)
        (σ.torus X p q u)) =
    σ.torus X (p + pShift ell j) (q + qShift ell j) (reducedPower source σ j X p q u)

/-- B's suspension target is stated independently of beta P = B. -/
theorem_wanted B_simplicialSuspension (j : ℤ) (X : PointedSpaces (k := k)) (p q : ℤ)
    (u : ReducedCohomology B F X p q (ModCoefficients ell)) :
    regrade N (B := B) (R₁ := F) (smash X (simplicialCircle (k := k))) (ModCoefficients ell)
      (by omega) rfl
      (bocksteinPower source σ j (smash X (simplicialCircle (k := k))) (p + 1) q
        (σ.simplicial X p q u)) =
    σ.simplicial X (p + pShift ell j + 1) (q + qShift ell j) (bocksteinPower source σ j X p q u)

/-- B retains the original torus suspension and exact Tate shift. -/
theorem_wanted B_torusSuspension (j : ℤ) (X : PointedSpaces (k := k)) (p q : ℤ)
    (u : ReducedCohomology B F X p q (ModCoefficients ell)) :
    regrade N (B := B) (R₁ := F) (smash X (pointedTorus (P := P) (A := A))) (ModCoefficients ell)
      (by omega) (by omega)
      (bocksteinPower source σ j (smash X (pointedTorus (P := P) (A := A))) (p + 1) (q + 1)
        (σ.torus X p q u)) =
    σ.torus X (p + pShift ell j + 1) (q + qShift ell j) (bocksteinPower source σ j X p q u)

end WantedExt.AlgebraicGeometry.MotivicReducedPowerWanted
