/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.RingHomInduction.Adjunction
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor
public import MathlibExt.CategoryTheory.Monad.AdjunctionBarRelativeResolutionHomology
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Balanced tensor comparisons of relative resolutions

For an associative ring homomorphism, the induction–restriction adjunction supplies the free Bar.
Applying the integer-balanced tensor functor gives augmentation-compatible comparison maps and
homology isomorphisms with any split termwise relative projective resolution. The coefficient and
left-module worlds are included through the stated ULift maps.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open Opposite MulOpposite
universe u v w m z
namespace ModuleCat.RingHomInduction

variable {k : Type u} {R : Type v} [Ring k] [Ring R] (φ : k →+* R)


/-- The integer-balanced coefficient functor is additive. -/
local instance integerBalanced_additive (M : ModuleCat.{m} Rᵐᵒᵖ) :
    (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M).Additive :=
  ModuleCat.BalancedTensor.additive.{0, v, m, z} ℤ R M

/-- Apply the existing balanced coefficient functor to the original induction Bar chain. -/
abbrev balancedFreeBarChain (M : ModuleCat.{m} Rᵐᵒᵖ) (N : ModuleCat.{max u v w} R) :
    ChainComplex (ModuleCat.{max u v w m} ℤ) ℕ :=
  CategoryTheory.Adjunction.mappedFreeBarResolution (ModuleCat.BalancedTensor.functor.{0, v, m, max u v w} ℤ R M)
    (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ) N

/-- The original independent left-module universe is included by its ULift. -/
abbrev balancedOriginalFreeBarChain (M : ModuleCat.{m} Rᵐᵒᵖ) (N : ModuleCat.{w} R) :
    ChainComplex (ModuleCat.{max u v w m} ℤ) ℕ :=
  balancedFreeBarChain.{u, v, w, m} φ M ((ModuleCat.uliftFunctor.{max u v, w} R).obj N)

/-- The full mapped counit augmentation has its original induced-tensor value. -/
theorem balancedFreeBar_augmentation_zero (M : ModuleCat.{m} Rᵐᵒᵖ)
    (N : ModuleCat.{max u v w} R) (a : M) (r : R) (n : N) :
    let : Module ℤ ((CategoryTheory.Adjunction.freeBarResolutionChain (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ)
      N).X 0) :=
      Module.compHom _ (algebraMap ℤ R)
    let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    (((ModuleCat.BalancedTensor.functor.{0, v, m, max u v w} ℤ R M).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (CategoryTheory.Adjunction.freeBarResolutionAugmentation (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ)
          N)).f 0
      (TensorProduct.Balanced.mk ℤ R M
        ((CategoryTheory.Adjunction.freeBarResolutionChain (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ) N).X 0) a
        (tensor φ ((ModuleCat.restrictScalars.{max u v w} φ).obj N) r n)) =
      TensorProduct.Balanced.mk ℤ R M N a (r • n) := by
  dsimp only
  rw [CategoryTheory.Adjunction.mappedFreeBarResolutionAugmentation_zero]
  let : Module ℤ
      (((ModuleCat.restrictScalars.{max u v w} φ) ⋙ ModuleCat.induceScalars.{u, v, w} φ).obj N) :=
    Module.compHom _ (algebraMap ℤ R)
  let : Module ℤ ((𝟭 (ModuleCat.{max u v w} R)).obj N) :=
    Module.compHom _ (algebraMap ℤ R)
  let nₖ : (ModuleCat.restrictScalars.{max u v w} φ).obj N := n
  let c := (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).counit.app N
  let x : ((ModuleCat.restrictScalars.{max u v w} φ) ⋙
      ModuleCat.induceScalars.{u, v, w} φ).obj N :=
    tensor φ ((ModuleCat.restrictScalars.{max u v w} φ).obj N) r nₖ
  change (ModuleCat.BalancedTensor.map ℤ R M c).hom
      (TensorProduct.Balanced.mk ℤ R M
        (((ModuleCat.restrictScalars.{max u v w} φ) ⋙
          ModuleCat.induceScalars.{u, v, w} φ).obj N) a x) =
    TensorProduct.Balanced.mk ℤ R M ((𝟭 (ModuleCat.{max u v w} R)).obj N) a (r • n)
  calc
    _ = TensorProduct.Balanced.mk ℤ R M ((𝟭 (ModuleCat.{max u v w} R)).obj N) a (c.hom x) :=
      ModuleCat.BalancedTensor.map_mk.{0, v, m, max u v w} ℤ R M c a x
    _ = _ := congrArg (fun y =>
      TensorProduct.Balanced.mk ℤ R M ((𝟭 (ModuleCat.{max u v w} R)).obj N) a y)
      (ModuleCat.induceRestrictScalarsAdj_counit.{u, v, w} φ N r n)

/-- Every original endpoint map induces an balanced comparison homology map. -/
def balancedBarComparisonHomologyMap (M : ModuleCat.{m} Rᵐᵒᵖ)
    (N Y : ModuleCat.{max u v w} R) (P : ChainComplex (ModuleCat.{max u v w} R) ℕ)
    (β : P ⟶ (ChainComplex.single₀ (ModuleCat.{max u v w} R)).obj Y)
    (σ : Functor.AugmentationSplit (ModuleCat.restrictScalars.{max u v w} φ) P Y β) (f : N ⟶ Y) (n : ℕ) :
    (balancedFreeBarChain.{u, v, w, m} φ M N).homology n ⟶
      (Functor.mappedResolution (ModuleCat.BalancedTensor.functor.{0, v, m, max u v w} ℤ R M) P).homology n :=
  CategoryTheory.Adjunction.freeBarResolutionComparisonHomologyMap (ModuleCat.BalancedTensor.functor.{0, v, m, max u v
    w} ℤ R M) (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ) N Y P β σ f n

/-- Balanced comparison homology is independent of every original map over the same augmentation. -/
theorem balancedBarComparisonHomologyMap_eq_of_augmentation (M : ModuleCat.{m} Rᵐᵒᵖ)
    (N Y : ModuleCat.{max u v w} R) (P : ChainComplex (ModuleCat.{max u v w} R) ℕ)
    (β : P ⟶ (ChainComplex.single₀ (ModuleCat.{max u v w} R)).obj Y)
    (σ : Functor.AugmentationSplit (ModuleCat.restrictScalars.{max u v w} φ) P Y β) (f : N ⟶ Y)
    (g : CategoryTheory.Adjunction.freeBarResolutionChain (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ) N ⟶ P)
    (hg : g ≫ β = CategoryTheory.Adjunction.freeBarResolutionAugmentation (ModuleCat.induceRestrictScalarsAdj.{u, v,
      w} φ) N ≫
      (ChainComplex.single₀ (ModuleCat.{max u v w} R)).map f) (n : ℕ) :
    balancedBarComparisonHomologyMap.{u, v, w, m} φ M N Y P β σ f n =
      homologyMap (((ModuleCat.BalancedTensor.functor.{0, v, m, max u v w} ℤ R M).mapHomologicalComplex
        (ComplexShape.down ℕ)).map g) n :=
  CategoryTheory.Adjunction.freeBarResolutionComparisonHomologyMap_eq_of_augmentation
    (ModuleCat.BalancedTensor.functor.{0, v, m, max u v w} ℤ R M) (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ) N Y
      P β σ f g hg n

/-- The integer-balanced comparison isomorphism is constructed from the two relative comparisons. -/
def balancedBarComparisonHomologyIso (M : ModuleCat.{m} Rᵐᵒᵖ)
    (N : ModuleCat.{max u v w} R) (P : ChainComplex (ModuleCat.{max u v w} R) ℕ)
    (β : P ⟶ (ChainComplex.single₀ (ModuleCat.{max u v w} R)).obj N)
    (σ : Functor.AugmentationSplit (ModuleCat.restrictScalars.{max u v w} φ) P N β) (hP : ∀ i,
      (ModuleCat.restrictScalars.{max u v w} φ).IsRelativeProjective (P.X i))
    (n : ℕ) :
    (balancedFreeBarChain.{u, v, w, m} φ M N).homology n ≅
      (Functor.mappedResolution (ModuleCat.BalancedTensor.functor.{0, v, m, max u v w} ℤ R M) P).homology n :=
  CategoryTheory.Adjunction.freeBarResolutionComparisonHomologyIso (ModuleCat.BalancedTensor.functor.{0, v, m, max u v
    w} ℤ R M) (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ) N P β σ hP n

/-- The constructed isomorphism's hom is precisely the computed balanced original identity comparison. -/
theorem balancedBarComparisonHomologyIso_hom (M : ModuleCat.{m} Rᵐᵒᵖ)
    (N : ModuleCat.{max u v w} R) (P : ChainComplex (ModuleCat.{max u v w} R) ℕ)
    (β : P ⟶ (ChainComplex.single₀ (ModuleCat.{max u v w} R)).obj N)
    (σ : Functor.AugmentationSplit (ModuleCat.restrictScalars.{max u v w} φ) P N β) (hP : ∀ i,
      (ModuleCat.restrictScalars.{max u v w} φ).IsRelativeProjective (P.X i))
    (n : ℕ) :
    (balancedBarComparisonHomologyIso.{u, v, w, m} φ M N P β σ hP n).hom =
      balancedBarComparisonHomologyMap.{u, v, w, m} φ M N N P β σ (𝟙 N) n :=
  CategoryTheory.Adjunction.freeBarResolutionComparisonHomologyIso_hom (ModuleCat.BalancedTensor.functor.{0, v, m, max
    u v w} ℤ R M) (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ) N P β σ hP n

/-- The original left carrier gets a relative-resolution comparison through ULift only. -/
def balancedOriginalBarComparisonHomologyIso (M : ModuleCat.{m} Rᵐᵒᵖ) (N : ModuleCat.{w} R)
    (P : ChainComplex (ModuleCat.{max u v w} R) ℕ)
    (β : P ⟶ (ChainComplex.single₀ (ModuleCat.{max u v w} R)).obj
      ((ModuleCat.uliftFunctor.{max u v, w} R).obj N))
    (σ : Functor.AugmentationSplit (ModuleCat.restrictScalars.{max u v w} φ) P ((ModuleCat.uliftFunctor.{max u v, w}
      R).obj N) β)
    (hP : ∀ i, (ModuleCat.restrictScalars.{max u v w} φ).IsRelativeProjective (P.X i)) (n : ℕ) :
    (balancedOriginalFreeBarChain.{u, v, w, m} φ M N).homology n ≅
      (Functor.mappedResolution (ModuleCat.BalancedTensor.functor.{0, v, m, max u v w} ℤ R M) P).homology n :=
  balancedBarComparisonHomologyIso.{u, v, w, m} φ M
    ((ModuleCat.uliftFunctor.{max u v, w} R).obj N) P β σ hP n

end ModuleCat.RingHomInduction
