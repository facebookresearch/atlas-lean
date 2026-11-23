/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicPowerCartanModels

/-!
# The operation laws of a reduced-power coefficient source

`PowerOperationLaws source σ` collects Voevodsky's laws for the reduced powers `P^j` and their
independent Bockstein coefficients `B^j` defined from a coefficient source: the Cartan formula on
total powers (Lemma 5.7), `P^0 = id` and vanishing in negative degrees (Theorems 9.3–9.4),
`β P^j = B^j` and `β B^j = 0` (Lemma 9.5), naturality and the two suspension isomorphisms.

The normalization fields of `CanonicalPowerCoefficientSource` only test the power maps on cycle
classes of smooth affine schemes, which does not determine them on arbitrary pointed simplicial
spaces (at `ℓ = 2` the modification `u ↦ β(u) × c` passes every such test and changes `B`).
The laws are therefore requested together with the constructed source, not for every source.

Source: Voevodsky, arXiv:math/0107109v1, Equation 8.1, Theorems 9.3/9.4, Lemmas 5.7/9.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicPowerOperationLaws

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

variable [PerfectField k] {hchar : (ell : k) ≠ 0}
  {Ls : CircleCycleOrientation (S₀ := S₀) T F}

/-- Voevodsky's operation laws for the reduced powers of the coefficient source `source` with
the suspension isomorphisms `σ`. -/
structure PowerOperationLaws
    (source : CanonicalPowerCoefficientSource (canonical := canonical) (Rep := Rep) (U₀ := U₀)
      (hRep := hRep) (hSmash := hSmash) (Eprime := Eprime) (point := point)
      (t := t) (delta := delta) (c := c) hchar)
    (σ : SuspensionEquivalences T F N B Zi K₀ F₀ D S M₁ hF U₀ Ls Lt ell) : Prop where
  /-- Lemma 5.7's Cartan source equation uses the actual native shared-BS diagonal and cup. -/
  totalPowerProduct : ∀ (X Y : PointedSpaces (k := k)) (d e : ℕ)
      (diag : ClassifyingPowerDiagonal (geometricClassifyingSpace G) X Y)
      (u : ReducedCohomology B F X (2 * (d : ℤ)) (d : ℤ) (ModCoefficients ell))
      (v : ReducedCohomology B F Y (2 * (e : ℤ)) (e : ℤ) (ModCoefficients ell)),
      canonicalTotalPower source (smash X Y) (d + e)
        (regrade N (B := B) (R₁ := F) (smash X Y) (ModCoefficients ell)
          (by push_cast; ring) (by push_cast; ring)
          (externalCup N B K₀ F₀ D S F M₁ hF X Y (2 * (d : ℤ)) (d : ℤ)
            (2 * (e : ℤ)) (e : ℤ) _ _ _ (ringCoefficientMultiplication (ULift.{1}
              (ZMod ell))) u v)) =
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
  /-- Theorem 9.4: `P^0` is the identity. -/
  P_zero : ∀ (X : PointedSpaces (k := k)) (p q : ℤ)
      (u : ReducedCohomology B F X p q (ModCoefficients ell)),
      regrade N (B := B) (R₁ := F) X (ModCoefficients ell)
        (by simp [pShift]) (by simp [qShift]) (reducedPower source σ 0 X p q u) = u
  /-- Theorem 9.3: the reduced powers vanish in negative degrees. -/
  P_negative : ∀ (j : ℤ) (hj : j < 0) (X : PointedSpaces (k := k)) (p q : ℤ)
      (u : ReducedCohomology B F X p q (ModCoefficients ell)),
      reducedPower source σ j X p q u = 0
  /-- The independent c coefficient also has the source negative-operation vanishing theorem. -/
  B_negative : ∀ (j : ℤ) (hj : j < 0) (X : PointedSpaces (k := k)) (p q : ℤ)
      (u : ReducedCohomology B F X p q (ModCoefficients ell)),
      bocksteinPower source σ j X p q u = 0
  /-- Lemma 9.5: the Bockstein of `P^j` is the independently defined coefficient `B^j`. -/
  beta_P : ∀ (j : ℤ) (X : PointedSpaces (k := k)) (p q : ℤ)
      (betaSource : CoefficientConeSource B (modSequence ell) (q + qShift ell j))
      (u : ReducedCohomology B F X p q (ModCoefficients ell)),
      bockstein B ell F X (p + pShift ell j) (q + qShift ell j) betaSource
        (reducedPower source σ j X p q u) = bocksteinPower source σ j X p q u
  /-- The other half of Lemma 9.5 remains a target on the native c coefficient. -/
  beta_B : ∀ (j : ℤ) (X : PointedSpaces (k := k)) (p q : ℤ)
      (betaSource : CoefficientConeSource B (modSequence ell) (q + qShift ell j))
      (u : ReducedCohomology B F X p q (ModCoefficients ell)),
      bockstein B ell F X (p + pShift ell j + 1) (q + qShift ell j) betaSource
        (bocksteinPower source σ j X p q u) = 0
  /-- Naturality is a theorem on the actual all-degree suspension extension. -/
  P_natural : ∀ (j : ℤ) (X Y : PointedSpaces (k := k)) (a : X ⟶ Y) (p q : ℤ)
      (u : ReducedCohomology B F Y p q (ModCoefficients ell)),
      reducedPower source σ j X p q (ReducedMotivicCohomologyModels.pullback B F a p q
        (ModCoefficients ell) u) =
      ReducedMotivicCohomologyModels.pullback B F a (p + pShift ell j) (q + qShift ell j)
        (ModCoefficients ell) (reducedPower source σ j Y p q u)
  /-- The independent B extension has the same native naturality target. -/
  B_natural : ∀ (j : ℤ) (X Y : PointedSpaces (k := k)) (a : X ⟶ Y) (p q : ℤ)
      (u : ReducedCohomology B F Y p q (ModCoefficients ell)),
      bocksteinPower source σ j X p q (ReducedMotivicCohomologyModels.pullback B F a p q
        (ModCoefficients ell) u) =
      ReducedMotivicCohomologyModels.pullback B F a (p + pShift ell j + 1) (q + qShift ell j)
        (ModCoefficients ell) (bocksteinPower source σ j Y p q u)
  /-- The selected P extension commutes with the actual ordered-circle suspension source. -/
  P_simplicialSuspension : ∀ (j : ℤ) (X : PointedSpaces (k := k)) (p q : ℤ)
      (u : ReducedCohomology B F X p q (ModCoefficients ell)),
      regrade N (B := B) (R₁ := F) (smash X (simplicialCircle (k := k))) (ModCoefficients ell)
        (by omega) rfl
        (reducedPower source σ j (smash X (simplicialCircle (k := k))) (p + 1) q
          (σ.simplicial X p q u)) =
      σ.simplicial X (p + pShift ell j) (q + qShift ell j) (reducedPower source σ j X p q u)
  /-- The selected P extension commutes with the actual torus graph suspension source. -/
  P_torusSuspension : ∀ (j : ℤ) (X : PointedSpaces (k := k)) (p q : ℤ)
      (u : ReducedCohomology B F X p q (ModCoefficients ell)),
      regrade N (B := B) (R₁ := F) (smash X (pointedTorus (P := P) (A := A))) (ModCoefficients ell)
        (by omega) (by omega)
        (reducedPower source σ j (smash X (pointedTorus (P := P) (A := A))) (p + 1) (q + 1)
          (σ.torus X p q u)) =
      σ.torus X (p + pShift ell j) (q + qShift ell j) (reducedPower source σ j X p q u)
  /-- B's suspension target is stated independently of beta P = B. -/
  B_simplicialSuspension : ∀ (j : ℤ) (X : PointedSpaces (k := k)) (p q : ℤ)
      (u : ReducedCohomology B F X p q (ModCoefficients ell)),
      regrade N (B := B) (R₁ := F) (smash X (simplicialCircle (k := k))) (ModCoefficients ell)
        (by omega) rfl
        (bocksteinPower source σ j (smash X (simplicialCircle (k := k))) (p + 1) q
          (σ.simplicial X p q u)) =
      σ.simplicial X (p + pShift ell j + 1) (q + qShift ell j) (bocksteinPower source σ j X p q u)
  /-- B retains the original torus suspension and exact Tate shift. -/
  B_torusSuspension : ∀ (j : ℤ) (X : PointedSpaces (k := k)) (p q : ℤ)
      (u : ReducedCohomology B F X p q (ModCoefficients ell)),
      regrade N (B := B) (R₁ := F) (smash X (pointedTorus (P := P) (A := A))) (ModCoefficients ell)
        (by omega) (by omega)
        (bocksteinPower source σ j (smash X (pointedTorus (P := P) (A := A))) (p + 1) (q + 1)
          (σ.torus X p q u)) =
      σ.torus X (p + pShift ell j + 1) (q + qShift ell j) (bocksteinPower source σ j X p q u)

end MathlibExt.AlgebraicGeometry.MotivicPowerOperationLaws
