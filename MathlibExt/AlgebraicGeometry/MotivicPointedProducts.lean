/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicCohomologyProducts
public import MathlibExt.AlgebraicGeometry.MotivicEilenbergMacLaneModels

/-!
# Pointed Tate multiplication with its fixed native derived class

A pointed product realizes the actual external cup of the two
tautological classes. Those classes are obtained from the identity maps
by reduced-free evaluation, native Dold--Kan/truncation and the specified
K-injective augmentation. No cohomology isomorphism or arbitrary cup is
used to specify the product. Construction remains a direct Wanted goal.

Source: Voevodsky arXiv:math/0107109v1, equation 2.1, pp. 3--4;
Mazza--Voevodsky--Weibel, Constructions 3.10--3.11.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicPointedProducts

open CategoryTheory
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open EffectiveMotivicComplexModels PointedMotivicModels
open ReducedMotivicCohomologyModels MotivicEilenbergMacLaneModels
open MotivicRealizationComparisons MotivicCycleProducts MotivicTensorOperations
open MotivicCohomologyProducts PointedMotivicQuotients

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D₀ : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D₀ G] [CorrespondenceAdditivity D₀ G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D₀ G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D₀ G} {S : TransferSheafificationModel D₀ G}
  {T : CycleComplexSystem (D := D₀) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R)}
  (N : NisTensorSystem k) [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  (B : CoefficientComplexSystem (D := D₀) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)
  (I : KInjectiveResolutionSystem k) (Q : PointedSimplicialModuleFunctor k)
  (F : ReducedFreeNisSystem k) (J : ReducedFreeAdjunction F Q)

/-- The actual universal class is the image of the literal identity map. -/
def tautological (p q : ℤ) (V : ModuleCat.{1} ℤ) :
    ReducedCohomology B F (K B I Q p q V) p q V :=
  realizationToCohomology B I Q F J (K B I Q p q V) p q V (𝟙 _)

variable {J₀ : TorusConcatenation A}
  {M₀ : SingularCycleProduct (S := S) N T J₀} {Z : EilenbergZilberModel N}
  {V₀ : NegativeTensorComparison N}
  (L : CoefficientMultiplicationSystem N T B M₀ Z V₀)
  (F₀ : KFlatResolutionSystem N) (D : DerivedTensorSource N F₀)
  (H : DerivedTensorShifts N F₀ D) (M : ReducedSmashComultiplication N F)
  (hF : IsFreeTensorComparison N F₀ D F)

/-- Actual pointed K products are fixed by the external-cycle/shuffle
cup of the actual universal classes, for all integer bidegrees/coefficients. -/
structure PointedTateProducts where
  map : ∀ (p q r s : ℤ) (A₁ A₂ A₃ : ModuleCat.{1} ℤ)
    (_μ : TensorProduct ℤ A₁ A₂ →ₗ[ℤ] A₃),
    smash (K B I Q p q A₁) (K B I Q r s A₂) ⟶ K B I Q (p + r) (q + s) A₃
  realized_class : ∀ (p q r s : ℤ) (A₁ A₂ A₃ : ModuleCat.{1} ℤ)
    (μ : TensorProduct ℤ A₁ A₂ →ₗ[ℤ] A₃),
    realizationToCohomology B I Q F J
      (smash (K B I Q p q A₁) (K B I Q r s A₂)) (p + r) (q + s) A₃
        (map p q r s A₁ A₂ A₃ μ) =
    externalCup N B L F₀ D H F M hF (K B I Q p q A₁) (K B I Q r s A₂)
      p q r s A₁ A₂ A₃ μ (tautological N B I Q F J p q A₁)
        (tautological N B I Q F J r s A₂)

end MathlibExt.AlgebraicGeometry.MotivicPointedProducts
