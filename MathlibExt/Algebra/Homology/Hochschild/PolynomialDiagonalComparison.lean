/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.KoszulComplexPolynomialDiagonal
public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBarResolutionComparison
public import MathlibExt.Algebra.Homology.KoszulComplex.BalancedCoefficients

/-!
# Polynomial Hochschild homology through the original diagonal resolution

The two resolutions of the same original regular enveloping
target are compared by the canonical projective-resolution lift. Applying
the original coefficient tensor functor gives Hochschild
homology computation with the native diagonal Koszul complex. The derived
tensor identification uses the same original functor and its native
resolution computation; no fixed-world integral Tor equality is assumed.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] (σ : Type v)

local notation "A" => MvPolynomial σ k
local notation "E" => MvPolynomial.PolynomialEnveloping k σ
local notation "P" => KoszulComplex.polynomialDiagonalProjectiveResolution k σ

attribute [local instance] Module.Projective.of_free

/-- The original bar and native diagonal resolutions have their augmentation-preserving comparison. -/
def barComparison :
    HomotopyEquiv (ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBar k A)
      (KoszulComplex.polynomialDiagonalComplex k σ) :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBarResolutionComparison k A P

/-- The forward comparison covers the original multiplication into the original target. -/
@[reassoc]
theorem barComparison_hom_augmentation :
    (barComparison k σ).hom ≫ KoszulComplex.polynomialDiagonalAugmentation k σ =
      ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBarAugmentationMap k A :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBarResolutionComparison_hom_π k A P

/-- The inverse comparison covers the very same original multiplication augmentation. -/
@[reassoc]
theorem barComparison_inv_augmentation :
    (barComparison k σ).inv ≫
        ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBarAugmentationMap k A =
      KoszulComplex.polynomialDiagonalAugmentation k σ :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBarResolutionComparison_inv_π k A P

/-- Every concrete original augmentation lift has the same comparison homotopy class. -/
def barComparisonLiftHomotopy
    (f : ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBar k A ⟶
      KoszulComplex.polynomialDiagonalComplex k σ)
    (hf : f ≫ KoszulComplex.polynomialDiagonalAugmentation k σ =
      ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBarAugmentationMap k A) :
    Homotopy f (barComparison k σ).hom :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBarResolutionComparisonLiftHomotopy k A P f hf

variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (MvPolynomial σ k) M] [Module (MvPolynomial σ k)ᵐᵒᵖ M]
  [SMulCommClass (MvPolynomial σ k) (MvPolynomial σ k)ᵐᵒᵖ M]
  [SMulCommClass k (MvPolynomial σ k) M] [SMulCommClass k (MvPolynomial σ k)ᵐᵒᵖ M]
  [IsScalarTower k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k)ᵐᵒᵖ M]

/-- The coefficient-first tensor of the original diagonal resolution. -/
def coefficientComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientResolutionTensorComplex k A M
    (KoszulComplex.polynomialDiagonalProjectiveResolution k σ)

/-- The original Hochschild complex is compared to the diagonal coefficient model by a proved homotopy
  equivalence. -/
def coefficientComparison :
    HomotopyEquiv (ModuleCat.Algebra.Hochschild.chainComplex k A M)
      (coefficientComplex k σ M) :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientHochschildResolutionComparison k A M P

/-- The forward map is the original unit-outer insertion followed by tensoring the bar lift. -/
theorem coefficientComparison_hom :
    (coefficientComparison k σ M).hom =
      (ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientTensorChainIso k A M).inv ≫
        ((ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientTensorFunctor k A M).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (barComparison k σ).hom :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientHochschildResolutionComparison_hom k A M P

/-- The inverse uses the inverse lift and original endpoint-sensitive cancellation. -/
theorem coefficientComparison_inv :
    (coefficientComparison k σ M).inv =
      ((ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientTensorFunctor k A M).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (barComparison k σ).inv ≫
          (ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientTensorChainIso k A M).hom :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientHochschildResolutionComparison_inv k A M P

/-- Actual arbitrary-bimodule polynomial Hochschild homology is the homology of the original coefficient diagonal
  complex. -/
def coefficientHomologyIso (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.chainComplex k A M).homology n ≅
      (coefficientComplex k σ M).homology n :=
  (coefficientComparison k σ M).toHomologyIso n

/-- The homology comparison retains homology of the constructed original chain map. -/
theorem coefficientHomologyIso_hom (n : ℕ) :
    (coefficientHomologyIso k σ M n).hom =
      HomologicalComplex.homologyMap (coefficientComparison k σ M).hom n := rfl

/-- The polynomial coefficient comparison computes the same derived balanced tensor functor. -/
theorem coefficientHomologyIso_derived (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientHochschildHomologyIsoDerived k A M n).hom ≫
        ((KoszulComplex.polynomialDiagonalProjectiveResolution k σ).isoLeftDerivedObj
          (ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientTensorFunctor k A M) n).hom =
      (coefficientHomologyIso k σ M n).hom :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientHochschildHomologyIsoForResolution_derived k A M P n

/-- Changing a concrete augmentation-preserving diagonal comparison does not change the resulting original homology
  map. -/
theorem coefficientHomologyIso_independent_lift
    (f : ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBar k A ⟶
      KoszulComplex.polynomialDiagonalComplex k σ)
    (hf : f ≫ KoszulComplex.polynomialDiagonalAugmentation k σ =
      ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBarAugmentationMap k A) (n : ℕ) :
    HomologicalComplex.homologyMap
      ((ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientTensorChainIso k A M).inv ≫
        ((ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientTensorFunctor k A M).mapHomologicalComplex
          (ComplexShape.down ℕ)).map f) n = (coefficientHomologyIso k σ M n).hom := by
  exact (ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientHochschildResolutionComparisonLiftHomotopy
    k A M P f hf).homologyMap_eq n

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
