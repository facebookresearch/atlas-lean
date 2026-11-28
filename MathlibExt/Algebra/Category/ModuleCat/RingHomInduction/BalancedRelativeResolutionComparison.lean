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
# Balanced tensor comparisons with an induction bar resolution

For a homomorphism `φ : k → R` of associative rings, the
induction–restriction adjunction gives the bar chain complex of a
left `R`-module `N`. Applying `M ⊗[R] -` for a right `R`-module `M`
gives integer-module-valued comparison maps with any augmented chain
complex split after restriction to `k`. If that complex also has
restriction-relative-projective terms, inverse comparisons give a
homology isomorphism. Coefficient and original left-module worlds
remain independent, with explicit lifts to the common resolution height.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open Opposite MulOpposite
universe u v w m z
namespace ModuleCat.RingHomInduction

variable {k : Type u} {R : Type v} [Ring k] [Ring R] (φ : k →+* R)


/-- For a ring `R`, right `R`-module `M` in universe `m`, and left
modules in universe `z`, the integer-valued balanced tensor functor
`M ⊗[R] -` to `ModuleCat_max(m,z)(ℤ)` is additive. -/
local instance integerBalanced_additive (M : ModuleCat.{m} Rᵐᵒᵖ) :
    (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M).Additive :=
  ModuleCat.BalancedTensor.additive.{0, v, m, z} ℤ R M

/-- Let `k,R` be rings in universes `u,v`, `φ : k → R` a ring
homomorphism, and `M` a right `R`-module in universe `m`. Put
`T=max(u,v,w)` for the left-module resolution carrier world. For `N : ModuleCat_T(R)`, tensoring the induction–restriction
bar chain complex with `M` gives a nonnegative chain complex
`M ⊗[R] Bar_φ(N)` in `ModuleCat_max(T,m)(ℤ)`. -/
abbrev balancedFreeBarChain (M : ModuleCat.{m} Rᵐᵒᵖ) (N : ModuleCat.{max u v w} R) :
    ChainComplex (ModuleCat.{max u v w m} ℤ) ℕ :=
  CategoryTheory.Adjunction.mappedFreeBarResolution (ModuleCat.BalancedTensor.functor.{0, v, m, max u v w} ℤ R M)
    (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ) N

/-- Let `k,R` be rings in universes `u,v`, `φ : k → R` a ring
homomorphism, and `M` a right `R`-module in universe `m`. Put
`T=max(u,v,w)` for the left-module resolution carrier world. For an original `N : ModuleCat_w(R)`, first lifting `N`
to `T` and then forming its balanced bar chain gives a complex in
`ModuleCat_max(T,m)(ℤ)`. -/
abbrev balancedOriginalFreeBarChain (M : ModuleCat.{m} Rᵐᵒᵖ) (N : ModuleCat.{w} R) :
    ChainComplex (ModuleCat.{max u v w m} ℤ) ℕ :=
  balancedFreeBarChain.{u, v, w, m} φ M ((ModuleCat.uliftFunctor.{max u v, w} R).obj N)

/-- Let `k,R` be rings in universes `u,v`, `φ : k → R` a ring
homomorphism, and `M` a right `R`-module in universe `m`. Put
`T=max(u,v,w)` for the left-module resolution carrier world. For `N : ModuleCat_T(R)`, the degree-zero balanced bar
augmentation sends `[a ⊗ (r ⊗ n)]` to `[a ⊗ (r • n)]`, using
the induction counit on the left factor. -/
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

/-- Let `k,R` be rings in universes `u,v`, `φ : k → R` a ring
homomorphism, and `M` a right `R`-module in universe `m`. Put
`T=max(u,v,w)` for the left-module resolution carrier world. Let `P → Y[0]` be an augmented complex split by a contracting
family after restriction along `φ`, and let `f : N → Y`.
The relative comparison gives
`H_n(M ⊗[R] Bar_φ(N)) → H_n(M ⊗[R] P)`. -/
def balancedBarComparisonHomologyMap (M : ModuleCat.{m} Rᵐᵒᵖ)
    (N Y : ModuleCat.{max u v w} R) (P : ChainComplex (ModuleCat.{max u v w} R) ℕ)
    (β : P ⟶ (ChainComplex.single₀ (ModuleCat.{max u v w} R)).obj Y)
    (σ : Functor.AugmentationSplit (ModuleCat.restrictScalars.{max u v w} φ) P Y β) (f : N ⟶ Y) (n : ℕ) :
    (balancedFreeBarChain.{u, v, w, m} φ M N).homology n ⟶
      (Functor.mappedResolution (ModuleCat.BalancedTensor.functor.{0, v, m, max u v w} ℤ R M) P).homology n :=
  CategoryTheory.Adjunction.freeBarResolutionComparisonHomologyMap (ModuleCat.BalancedTensor.functor.{0, v, m, max u v
    w} ℤ R M) (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ) N Y P β σ f n

/-- Let `k,R` be rings in universes `u,v`, `φ : k → R` a ring
homomorphism, and `M` a right `R`-module in universe `m`. Put
`T=max(u,v,w)` for the left-module resolution carrier world. For `P → Y[0]` split after restriction and `f : N → Y`,
any bar-to-`P` chain map preserving the augmentation over `f` computes
the canonical balanced comparison map on homology. -/
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

/-- Let `k,R` be rings in universes `u,v`, `φ : k → R` a ring
homomorphism, and `M` a right `R`-module in universe `m`. Put
`T=max(u,v,w)` for the left-module resolution carrier world. For `P → N[0]` split after restriction along `φ`, with all
terms relative-projective for that restriction, inverse relative
comparisons give `H_n(M ⊗[R] Bar_φ(N)) ≅ H_n(M ⊗[R] P)`. -/
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

/-- Let `k,R` be rings in universes `u,v`, `φ : k → R` a ring
homomorphism, and `M` a right `R`-module in universe `m`. Put
`T=max(u,v,w)` for the left-module resolution carrier world. For a split termwise restriction-relative-projective
augmentation `P → N[0]`, the forward balanced bar homology isomorphism
is the canonical comparison map over `𝟙 N`. -/
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

/-- Let `k,R` be rings in universes `u,v`, `φ : k → R` a ring
homomorphism, and `M` a right `R`-module in universe `m`. Put
`T=max(u,v,w)` for the left-module resolution carrier world. Let `N : ModuleCat_w(R)` and `P` augment to its lift in
world `T`, split after restriction along `φ` and with relative-projective
terms. The lifted-original bar and `P` have canonically isomorphic
homology after balanced tensoring with `M`. -/
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
