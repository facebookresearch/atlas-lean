/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicPrimeClassGeometry
public import Mathlib.Algebra.Ring.ULift

/-!
# Integral universal Euler class and its based coefficient lift

The global Thom class restricts to the source-normalized Thom class of
each actual cokernel xi_ell/O. Integral d is the pullback along the
original global zero section, before any coefficient reduction.

The class c has integral coefficient boundary d and vanishes on the
actual trivial-torsor point defined by the regular identity vector.
Both equations are essential, including at ell = 2. The construction
and uniqueness are direct source theorem requests in the companion.

The powers of d and the c*d^i monomials use the existing native cup.
Their zeroth monomial is the source-normalized affine rank-zero unit.

Source: Voevodsky, arXiv:math/0107109v1, Lemma 6.13,
Theorem 6.14, Lemma 6.15 and Theorem 6.16, printed pp. 25--27.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicPrimeClasses

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes EffectiveMotivicComplexModels PointedMotivicModels
open PointedMotivicQuotients ReducedMotivicCohomologyModels MotivicRealizationComparisons
open MotivicAffineQuotientModels MotivicAffineTateComparisons MotivicBundleModels GeneralMotivicBundleThom
open MotivicCycleProducts MotivicTensorOperations MotivicCohomologyProducts
open MotivicFinitePermutationModels MotivicGeometricClassifyingSpaces MotivicPrimeClassGeometry
open MotivicBocksteinModels MotivicTorusClassModels

/-- Rank of the actual permutation cokernel bundle. -/
abbrev primeWeight (ell : ℕ) : ℤ := ((ell - 1 : ℕ) : ℤ)

/-- Integral Euler degree of xi_ell/O. -/
abbrev dDegree (ell : ℕ) : ℤ := 2 * primeWeight ell

/-- The coefficient lift has one fewer cohomological degree. -/
abbrev cDegree (ell : ℕ) : ℤ := dDegree ell - 1

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D₀ : CompositionSystem k} {G₀ : GraphSystem k}
  [CorrespondenceLaws D₀ G₀] [CorrespondenceAdditivity D₀ G₀]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D₀ G₀ P E} {A : StandardSchemes P}
  {R₀ : RepresentableSystem D₀ G₀} {S₀ : TransferSheafificationModel D₀ G₀}
  {T : CycleComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R₀)}
  (N : NisTensorSystem k) [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  (B : CoefficientComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R₀) (S := S₀) T N)
  (I : KInjectiveResolutionSystem k) (Q : PointedSimplicialModuleFunctor k)
  (F : ReducedFreeNisSystem k) (J : ReducedFreeAdjunction F Q)
  {Msec : ModuleSectionSystem Q}
  (V : AffineTateMapSystem (N := N) (B := B) (I := I) (Q := Q))
  (T₀ : AffineThomCycleSections (D₀ := D₀) (G := G₀) (P := P)
    (A := A) (R := R₀) (N := N) (Q := Q) (M := Msec))
  {ell : ℕ}
  [Gconst : ConstantGroupGeometry (k := k) (H := Equiv.Perm (Fin ell))]
  {G : GeometricApproximation (k := k) (H := Equiv.Perm (Fin ell))}
  (Eprime : PrimeThomDiagram G)

/-- The integral class on the native Thom colimit restricts to the actual normalized bundle classes. -/
structure GlobalPrimeThomClass where
  stage : ∀ m : ℕ, ThomClass N B I Q F J V T₀ (Eprime.stage m).quotient
  value : ReducedCohomology B F (primeGlobalThom Eprime) (dDegree ell) (primeWeight ell)
    integerCoefficients
  restriction : ∀ m : ℕ,
    ReducedMotivicCohomologyModels.pullback B F (primeThomStageMap Eprime m)
      (dDegree ell) (primeWeight ell) integerCoefficients value = (stage m).value

/-- Integral d is the zero pullback of this exact quotient-bundle Thom class. -/
def integralD (t : GlobalPrimeThomClass N B I Q F J V T₀ Eprime) :
    ReducedCohomology B F (geometricClassifyingSpace G) (dDegree ell) (primeWeight ell)
      integerCoefficients :=
  ReducedMotivicCohomologyModels.pullback B F (primeGlobalZero Eprime)
    (dDegree ell) (primeWeight ell) integerCoefficients t.value

/-- Mod-ell d is defined after its integral Euler source. -/
def d (t : GlobalPrimeThomClass N B I Q F J V T₀ Eprime) :
    ReducedCohomology B F (geometricClassifyingSpace G) (dDegree ell) (primeWeight ell)
      (ModCoefficients ell) :=
  ReducedMotivicCohomologyModels.coefficientMap B F (geometricClassifyingSpace G)
    (dDegree ell) (primeWeight ell) (integralReduction ell) (integralD N B I Q F J V T₀ Eprime t)

/-- Both source equations of Theorem 6.14, on the actual trivial torsor point. -/
structure BasedIntegralLift (point : BasedApproximation P G)
    (t : GlobalPrimeThomClass N B I Q F J V T₀ Eprime)
    (delta : CoefficientConeSource B (integralSequence ell) (primeWeight ell)) where
  value : ReducedCohomology B F (geometricClassifyingSpace G) (cDegree ell) (primeWeight ell)
    (ModCoefficients ell)
  integralBoundary :
    regrade N (B := B) (R₁ := F) (geometricClassifyingSpace G) integerCoefficients
      (show cDegree ell + 1 = dDegree ell from by simp [cDegree]) rfl
      (integralBockstein B ell F (geometricClassifyingSpace G) (cDegree ell) (primeWeight ell)
        delta value) = integralD N B I Q F J V T₀ Eprime t
  augmentation : ReducedMotivicCohomologyModels.pullback B F (basepointMap point)
    (cDegree ell) (primeWeight ell) (ModCoefficients ell) value = 0

/-- The source-normalized rank-zero affine class gives the actual coefficient unit. -/
def integralUnit : ReducedCohomology B F (representedPointed P.unit) 0 0 integerCoefficients :=
  ReducedMotivicCohomologyModels.pullback B F
    (representedMap (A.zero 0) ≫ cofiberQuotient (representedMap (A.complementInclusion 0)))
    0 0 integerCoefficients (affineOrientation N B I Q F J V T₀ 0)

/-- The constant monomial is the unit pulled by the original structural colimit map. -/
def primeUnit : ReducedCohomology B F (geometricClassifyingSpace G) 0 0 (ModCoefficients ell) :=
  ReducedMotivicCohomologyModels.pullback B F (geometricProjection P G) 0 0 (ModCoefficients ell)
    (ReducedMotivicCohomologyModels.coefficientMap B F (representedPointed P.unit) 0 0
      (integralReduction ell) (integralUnit N B I Q F J V T₀))

variable {J₀ : TorusConcatenation A}
  {M₀ : SingularCycleProduct (S := S₀) N T J₀} {Z₀ : EilenbergZilberModel N}
  {V₀ : NegativeTensorComparison N}
  (K₀ : CoefficientMultiplicationSystem N T B M₀ Z₀ V₀)
  (F₀ : KFlatResolutionSystem N) (D : DerivedTensorSource N F₀)
  (S : DerivedTensorShifts N F₀ D) (M₁ : ReducedSmashComultiplication N F)
  (hF : IsFreeTensorComparison N F₀ D F)

/-- The native d^i, with exact integer bidegrees and the canonical constant term. -/
def dPower (t : GlobalPrimeThomClass N B I Q F J V T₀ Eprime) :
    (i : ℕ) → ReducedCohomology B F (geometricClassifyingSpace G)
      ((i : ℤ) * dDegree ell) ((i : ℤ) * primeWeight ell) (ModCoefficients ell)
  | 0 => by
      simpa only [Nat.cast_zero, zero_mul] using
        (primeUnit (G := G) (ell := ell) N B I Q F J V T₀)
  | i + 1 => regrade N (B := B) (R₁ := F) (geometricClassifyingSpace G) (ModCoefficients ell)
      (by push_cast; ring) (by push_cast; ring)
      (cupRing N B K₀ F₀ D S F M₁ hF (ULift.{1} (ZMod ell)) (geometricClassifyingSpace G)
        ((i : ℤ) * dDegree ell) ((i : ℤ) * primeWeight ell) (dDegree ell) (primeWeight ell)
          (dPower t i) (d N B I Q F J V T₀ Eprime t))

/-- The odd basis is c*d^i, rather than a separately chosen coefficient class. -/
def cDPower (point : BasedApproximation P G)
    (t : GlobalPrimeThomClass N B I Q F J V T₀ Eprime)
    (delta : CoefficientConeSource B (integralSequence ell) (primeWeight ell))
    (c : BasedIntegralLift N B I Q F J V T₀ Eprime point t delta) (i : ℕ) :
    ReducedCohomology B F (geometricClassifyingSpace G)
      (cDegree ell + (i : ℤ) * dDegree ell) (primeWeight ell + (i : ℤ) * primeWeight ell)
        (ModCoefficients ell) :=
  cupRing N B K₀ F₀ D S F M₁ hF (ULift.{1} (ZMod ell)) (geometricClassifyingSpace G)
    (cDegree ell) (primeWeight ell) ((i : ℤ) * dDegree ell) ((i : ℤ) * primeWeight ell)
      c.value (dPower N B I Q F J V T₀ Eprime K₀ F₀ D S M₁ hF t i)

end MathlibExt.AlgebraicGeometry.MotivicPrimeClasses
