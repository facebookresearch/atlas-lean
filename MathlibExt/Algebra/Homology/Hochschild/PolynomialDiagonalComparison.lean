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
# Polynomial Hochschild homology through the diagonal resolution

Let k be a commutative ring, A = k[σ] and E = A ⊗[k] Aᵐᵒᵖ. The enveloping bar and diagonal
Koszul projective resolutions of the regular E-module A admit an augmentation-preserving
homotopy equivalence. Any other augmentation-preserving bar-to-diagonal lift is homotopic to its
forward map.

For a compatible A-bimodule M, applying T_M(X) = M ⊗_E X and cancelling the bar endpoints gives
a homotopy equivalence between the Hochschild chain complex and the coefficient diagonal
complex. The induced homology comparison agrees with the computation of the left-derived
balanced tensor functor using the same diagonal resolution, and is independent of the
augmentation-preserving lift. No flatness or projectivity condition is placed on M.
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

/-- Let k be a commutative ring, σ any variable set, A = k[σ] and E = A ⊗[k] Aᵐᵒᵖ. The enveloping
bar resolution and the polynomial diagonal Koszul resolution are homotopy equivalent as
ℕ-indexed chain complexes of E-modules. Both resolve the regular E-module A through
multiplication E → A, and the comparison preserves these augmentations. -/
def barComparison :
    HomotopyEquiv (ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBar k A)
      (KoszulComplex.polynomialDiagonalComplex k σ) :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBarResolutionComparison k A P

/-- Let k be a commutative ring, σ any variable set, A = k[σ] and E = A ⊗[k] Aᵐᵒᵖ. If F =
(barComparison k σ).hom, εdiag is the diagonal augmentation and εbar is the bar augmentation,
then F ≫ εdiag = εbar. -/
@[reassoc]
theorem barComparison_hom_augmentation :
    (barComparison k σ).hom ≫ KoszulComplex.polynomialDiagonalAugmentation k σ =
      ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBarAugmentationMap k A :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBarResolutionComparison_hom_π k A P

/-- Let k be a commutative ring, σ any variable set, A = k[σ] and E = A ⊗[k] Aᵐᵒᵖ. If G =
(barComparison k σ).inv, then G ≫ εbar = εdiag, where both augmentations target the regular
E-module A concentrated in degree zero. -/
@[reassoc]
theorem barComparison_inv_augmentation :
    (barComparison k σ).inv ≫
        ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBarAugmentationMap k A =
      KoszulComplex.polynomialDiagonalAugmentation k σ :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.envelopingBarResolutionComparison_inv_π k A P

/-- Let k be a commutative ring, σ any variable set, A = k[σ] and E = A ⊗[k] Aᵐᵒᵖ. For a chain map f
from the enveloping bar resolution to the diagonal Koszul resolution satisfying f ≫ εdiag =
εbar, there is a chain homotopy f ∼ (barComparison k σ).hom. -/
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

/-- Let k be a commutative ring, σ any variable set, A = k[σ] and E = A ⊗[k] Aᵐᵒᵖ. Let M be an
A-bimodule with commuting left and right actions compatible with its k-action, and let T_M(X) =
M ⊗_E X. Apply the additive functor T_M to the polynomial diagonal projective resolution of A
over E. The resulting k-module chain complex is coefficientComplex k σ M, with degree-n term M
⊗_E ∧ⁿ_E(⊕ᵢ∈σ E·eᵢ). -/
def coefficientComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientResolutionTensorComplex k A M
    (KoszulComplex.polynomialDiagonalProjectiveResolution k σ)

/-- Let k be a commutative ring, σ any variable set, A = k[σ] and E = A ⊗[k] Aᵐᵒᵖ. Let M be an
A-bimodule with commuting left and right actions compatible with its k-action, and let T_M(X) =
M ⊗_E X. Tensoring the augmentation-preserving bar-to-diagonal homotopy equivalence with M and
identifying the coefficient bar with Hochschild chains gives a homotopy equivalence Cₙ(A,M) = M
⊗[k] A^{⊗n} ∼ coefficientComplex k σ M. -/
def coefficientComparison :
    HomotopyEquiv (ModuleCat.Algebra.Hochschild.chainComplex k A M)
      (coefficientComplex k σ M) :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientHochschildResolutionComparison k A M P

/-- Let k be a commutative ring, σ any variable set, A = k[σ] and E = A ⊗[k] Aᵐᵒᵖ. Let M be an
A-bimodule with commuting left and right actions compatible with its k-action, and let T_M(X) =
M ⊗_E X. Let C be the coefficient bar-to-Hochschild isomorphism and F = (barComparison k σ).hom.
Then (coefficientComparison k σ M).hom = C.inv ≫ T_M(F), as a map from Hochschild chains to the
coefficient diagonal complex. -/
theorem coefficientComparison_hom :
    (coefficientComparison k σ M).hom =
      (ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientTensorChainIso k A M).inv ≫
        ((ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientTensorFunctor k A M).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (barComparison k σ).hom :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientHochschildResolutionComparison_hom k A M P

/-- Let k be a commutative ring, σ any variable set, A = k[σ] and E = A ⊗[k] Aᵐᵒᵖ. Let M be an
A-bimodule with commuting left and right actions compatible with its k-action, and let T_M(X) =
M ⊗_E X. Let C be the coefficient bar-to-Hochschild isomorphism and G = (barComparison k σ).inv.
Then (coefficientComparison k σ M).inv = T_M(G) ≫ C.hom. -/
theorem coefficientComparison_inv :
    (coefficientComparison k σ M).inv =
      ((ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientTensorFunctor k A M).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (barComparison k σ).inv ≫
          (ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientTensorChainIso k A M).hom :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientHochschildResolutionComparison_inv k A M P

/-- Let k be a commutative ring, σ any variable set, A = k[σ] and E = A ⊗[k] Aᵐᵒᵖ. Let M be an
A-bimodule with commuting left and right actions compatible with its k-action, and let T_M(X) =
M ⊗_E X. For every n : ℕ, the coefficient resolution comparison induces an isomorphism HHₙ(A,M)
≅ Hₙ(coefficientComplex k σ M). -/
def coefficientHomologyIso (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.chainComplex k A M).homology n ≅
      (coefficientComplex k σ M).homology n :=
  (coefficientComparison k σ M).toHomologyIso n

/-- Let k be a commutative ring, σ any variable set, A = k[σ] and E = A ⊗[k] Aᵐᵒᵖ. Let M be an
A-bimodule with commuting left and right actions compatible with its k-action, and let T_M(X) =
M ⊗_E X. In degree n : ℕ, the forward map of coefficientHomologyIso equals the homology map
induced by (coefficientComparison k σ M).hom. -/
theorem coefficientHomologyIso_hom (n : ℕ) :
    (coefficientHomologyIso k σ M n).hom =
      HomologicalComplex.homologyMap (coefficientComparison k σ M).hom n := rfl

/-- Let k be a commutative ring, σ any variable set, A = k[σ] and E = A ⊗[k] Aᵐᵒᵖ. Let M be an
A-bimodule with commuting left and right actions compatible with its k-action, and let T_M(X) =
M ⊗_E X. In degree n : ℕ, compose the bar comparison HHₙ(A,M) → (LₙT_M)(A) with the diagonal
projective-resolution computation (LₙT_M)(A) → Hₙ(T_M(Pdiag)). This composite equals the forward
map of coefficientHomologyIso k σ M n. -/
theorem coefficientHomologyIso_derived (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientHochschildHomologyIsoDerived k A M n).hom ≫
        ((KoszulComplex.polynomialDiagonalProjectiveResolution k σ).isoLeftDerivedObj
          (ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientTensorFunctor k A M) n).hom =
      (coefficientHomologyIso k σ M n).hom :=
  ModuleCat.Algebra.Hochschild.AdjacentBar.coefficientHochschildHomologyIsoForResolution_derived k A M P n

/-- Let k be a commutative ring, σ any variable set, A = k[σ] and E = A ⊗[k] Aᵐᵒᵖ. Let M be an
A-bimodule with commuting left and right actions compatible with its k-action, and let T_M(X) =
M ⊗_E X. If f : Pbar → Pdiag satisfies f ≫ εdiag = εbar, then the homology map of C.inv ≫
T_M(f), where C is the coefficient bar-to-Hochschild isomorphism, equals (coefficientHomologyIso
k σ M n).hom in every degree n : ℕ. -/
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
