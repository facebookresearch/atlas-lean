/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.RingHomInduction.BalancedRelativeResolutionComparison
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.Along
public import Mathlib.Algebra.Homology.Additive

/-!
# Coefficient naturality of balanced relative comparisons

A map of right modules `g : M → M′` over an associative ring induces
`M ⊗[R] N → M′ ⊗[R] N`, taking `[a ⊗ x]` to `[g(a) ⊗ x]`.
These maps prolong to arbitrary chain complexes and commute with
chain maps and homology. For an induction–restriction bar resolution,
they also commute with relative comparison maps and the full counit
augmentation. Coefficient and resolution worlds are independent.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology
universe u v w m z
namespace ModuleCat.RingHomInduction

variable {R : Type v} [Ring R]

/-- Let `R` be a ring, `M,M′` right `R`-modules with carriers in `m`,
and `g : M → M′` a right-module map. Restricting its scalar action gives the canonical
integer-linear map on the underlying additive groups. -/
abbrev coefficientIntMap {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M') : M →ₗ[ℤ] M' :=
  g.hom.toAddMonoidHom.toIntLinearMap

/-- Let `R` be a ring, `M,M′` right `R`-modules with carriers in `m`,
and `g : M → M′` a right-module map. Its integer-linear restriction satisfies
`g((op r) • a) = (op r) • g(a)` for every `r : R`, `a : M`. -/
theorem coefficientIntMap_equivariant {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M')
    (r : R) (a : M) :
    coefficientIntMap g (MulOpposite.op r • a) = MulOpposite.op r • coefficientIntMap g a := by
  change g.hom (MulOpposite.op r • a) = MulOpposite.op r • g.hom a
  exact g.hom.map_smul (MulOpposite.op r) a

/-- Let `R` be a ring, `M,M′` right `R`-modules with carriers in `m`,
and `g : M → M′` a right-module map. Balanced tensoring in the coefficient gives a natural
transformation of integer-module-valued functors
`M ⊗[R] - → M′ ⊗[R] -` on left `R`-modules. -/
def balancedCoefficientNatTrans {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M') :
    ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M ⟶
      ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M' :=
  (Functor.leftUnitor (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M)).inv ≫
    (Functor.isoWhiskerRight (ModuleCat.restrictScalarsId.{z} R)
      (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M)).inv ≫
    ModuleCat.BalancedTensor.Along.natTrans ℤ (AlgHom.id ℤ R) (coefficientIntMap g)
      (fun r a => coefficientIntMap_equivariant g r a)

/-- Let `R` be a ring, `M,M′` right `R`-modules with carriers in `m`,
and `g : M → M′` a right-module map. For a left module `N` in an independent universe `z`, the
coefficient transformation sends `[a ⊗ x]` to `[g(a) ⊗ x]`. -/
theorem balancedCoefficientNatTrans_mk {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M')
    (N : ModuleCat.{z} R) (a : M) (x : N) :
    let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    ((balancedCoefficientNatTrans.{v, m, z} g).app N).hom
      (TensorProduct.Balanced.mk ℤ R M N a x) = TensorProduct.Balanced.mk ℤ R M' N (g.hom a) x := by
  dsimp only
  let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  let nR := (ModuleCat.restrictScalars.{z} (AlgHom.id ℤ R).toRingHom).obj N
  let : Module ℤ nR := Module.compHom nR (algebraMap ℤ R)
  let c : N ⟶ nR := (ModuleCat.restrictScalarsId'.{z} (AlgHom.id ℤ R).toRingHom rfl).inv.app N
  have hf : ∀ (r : R) (a : M), coefficientIntMap g (MulOpposite.op r • a) =
      MulOpposite.op ((AlgHom.id ℤ R) r) • coefficientIntMap g a := by
    intro r a
    exact coefficientIntMap_equivariant g r a
  let t := ModuleCat.BalancedTensor.Along.component ℤ (AlgHom.id ℤ R) (coefficientIntMap g) hf N
  change t.hom ((ModuleCat.BalancedTensor.map ℤ R M c).hom
    (TensorProduct.Balanced.mk ℤ R M N a x)) = _
  have hm : (ModuleCat.BalancedTensor.map ℤ R M c).hom
      (TensorProduct.Balanced.mk ℤ R M N a x) =
      ModuleCat.BalancedTensor.Along.sourceMk ℤ (AlgHom.id ℤ R) N a x :=
    ModuleCat.BalancedTensor.map_mk.{0, v, m, z} ℤ R M c a x
  have ht : t.hom (ModuleCat.BalancedTensor.Along.sourceMk ℤ (AlgHom.id ℤ R) N a x) =
      TensorProduct.Balanced.mk ℤ R M' N (g.hom a) x :=
    ModuleCat.BalancedTensor.Along.component_mk ℤ (AlgHom.id ℤ R)
      (coefficientIntMap g) hf N a x
  exact (congrArg t.hom hm).trans ht

local instance balanced_additive (M : ModuleCat.{m} Rᵐᵒᵖ) :
    (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M).Additive :=
  ModuleCat.BalancedTensor.additive.{0, v, m, z} ℤ R M

/-- Let `R` be a ring, `M,M′` right `R`-modules with carriers in `m`,
and `g : M → M′` a right-module map. For any nonnegative chain complex `Q` of left modules in
universe `z`, applying the coefficient transformation in every degree
gives `M ⊗[R] Q → M′ ⊗[R] Q`. -/
abbrev balancedCoefficientChainMap {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M')
    (Q : ChainComplex (ModuleCat.{z} R) ℕ) :
    Functor.mappedResolution (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M) Q ⟶
      Functor.mappedResolution (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M') Q :=
  (NatTrans.mapHomologicalComplex (balancedCoefficientNatTrans.{v, m, z} g) (.down ℕ)).app Q

/-- Let `R` be a ring, `M,M′` right `R`-modules with carriers in `m`,
and `g : M → M′` a right-module map. For a chain map `f : Q → P`, the coefficient chain maps
commute with `M ⊗[R] f` and `M′ ⊗[R] f`. -/
theorem balancedCoefficientChainMap_naturality {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M')
    {Q P : ChainComplex (ModuleCat.{z} R) ℕ} (f : Q ⟶ P) :
    ((ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M).mapHomologicalComplex (.down ℕ)).map f ≫
        balancedCoefficientChainMap g P =
      balancedCoefficientChainMap g Q ≫
        ((ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M').mapHomologicalComplex (.down ℕ)).map f :=
  NatTrans.mapHomologicalComplex_naturality (balancedCoefficientNatTrans.{v, m, z} g) f

/-- Let `R` be a ring, `M,M′` right `R`-modules with carriers in `m`,
and `g : M → M′` a right-module map. For any chain complex `Q` and degree `n`, the coefficient
chain map induces `H_n(M ⊗[R] Q) → H_n(M′ ⊗[R] Q)`. -/
abbrev balancedCoefficientHomologyMap {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M')
    (Q : ChainComplex (ModuleCat.{z} R) ℕ) (n : ℕ) :
    (Functor.mappedResolution (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M) Q).homology n ⟶
      (Functor.mappedResolution (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M') Q).homology n :=
  homologyMap (balancedCoefficientChainMap g Q) n

/-- Let `R` be a ring, `M,M′` right `R`-modules with carriers in `m`,
and `g : M → M′` a right-module map. For any chain map `f : Q → P`, the induced coefficient
homology maps commute with the tensor images of `f`, in every degree
and without exactness conditions on the complexes. -/
theorem balancedCoefficientHomologyMap_naturality {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M')
    {Q P : ChainComplex (ModuleCat.{z} R) ℕ} (f : Q ⟶ P) (n : ℕ) :
    homologyMap
        (((ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M).mapHomologicalComplex (.down ℕ)).map f) n ≫
        balancedCoefficientHomologyMap g P n =
      balancedCoefficientHomologyMap g Q n ≫
        homologyMap
          (((ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M').mapHomologicalComplex (.down ℕ)).map f) n := by
  have h := congrArg (fun h => homologyMap h n) (balancedCoefficientChainMap_naturality g f)
  simpa only [homologyMap_comp] using h

variable {k : Type u} [Ring k] (φ : k →+* R)

/-- Let `k,R` be rings, `φ : k → R`, and `f : N → N′` a map of
left `R`-modules at the common ring-containing resolution height.
The map of induction bar chain complexes induced by `f` satisfies
`Bar(f) ≫ ε_N′ = ε_N ≫ f[0]` for their counit augmentations. -/
theorem nativeFreeBarChainMap_augmentation {N N' : ModuleCat.{max u v w} R} (f : N ⟶ N') :
    (alternatingFaceMapComplex (ModuleCat.{max u v w} R)).map
        ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarFunctor.map f) ≫
        (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarResolutionAugmentation N' =
      (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarResolutionAugmentation N ≫
        (ChainComplex.single₀ (ModuleCat.{max u v w} R)).map f :=
  AlternatingFaceMapComplex.ε.naturality
    ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarAugmentedFunctor.map f)

/-- Let `k,R` be rings in universes `u,v`, `φ : k → R` a ring
homomorphism, and `M` a right `R`-module in universe `m`. Put
`T=max(u,v,w)` for the left-module resolution carrier world. For `f : N → N′`, the canonical balanced relative comparison
from the bar of `N` to the bar of `N′` is the homology map of
`M ⊗[R] Bar_φ(f)`. -/
theorem balancedBarComparisonHomologyMap_eq_nativeFreeBarMap (M : ModuleCat.{m} Rᵐᵒᵖ)
    {N N' : ModuleCat.{max u v w} R} (f : N ⟶ N') (n : ℕ) :
    balancedBarComparisonHomologyMap.{u, v, w, m} φ M N N'
        ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarResolutionChain N')
        ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarResolutionAugmentation N')
        ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarResolutionSplit N') f n =
      homologyMap
        (((ModuleCat.BalancedTensor.functor.{0, v, m, max u v w} ℤ R M).mapHomologicalComplex (.down ℕ)).map
          ((alternatingFaceMapComplex (ModuleCat.{max u v w} R)).map
            ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarFunctor.map f))) n :=
  balancedBarComparisonHomologyMap_eq_of_augmentation φ M N N' _ _ _ f _
    (nativeFreeBarChainMap_augmentation φ f) n

/-- Let `k,R` be rings in universes `u,v`, `φ : k → R` a ring
homomorphism, and `M` a right `R`-module in universe `m`. Put
`T=max(u,v,w)` for the left-module resolution carrier world. For a right-module map `g : M → M′`, a split relative
augmentation `P → Y[0]` and `f : N → Y`, the balanced comparison
map commutes with the coefficient homology maps on the bar of `N`
and on `P`. -/
theorem balancedBarComparisonHomologyMap_coefficient_naturality
    {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M') (N Y : ModuleCat.{max u v w} R)
    (P : ChainComplex (ModuleCat.{max u v w} R) ℕ)
    (β : P ⟶ (ChainComplex.single₀ (ModuleCat.{max u v w} R)).obj Y)
    (σ : Functor.AugmentationSplit (ModuleCat.restrictScalars.{max u v w} φ) P Y β)
    (f : N ⟶ Y) (n : ℕ) :
    balancedBarComparisonHomologyMap.{u, v, w, m} φ M N Y P β σ f n ≫
        balancedCoefficientHomologyMap g P n =
      balancedCoefficientHomologyMap g
          ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarResolutionChain N) n ≫
        balancedBarComparisonHomologyMap.{u, v, w, m} φ M' N Y P β σ f n :=
  balancedCoefficientHomologyMap_naturality g
    ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarResolutionComparison N Y P β σ f) n

/-- Let `k,R` be rings in universes `u,v`, `φ : k → R` a ring
homomorphism, and `M` a right `R`-module in universe `m`. Put
`T=max(u,v,w)` for the left-module resolution carrier world. For a right-module map `g : M → M′` and left module `N`,
the coefficient chain maps commute with the balanced tensor images
of the full bar counit augmentation `Bar_φ(N) → N[0]`. -/
theorem balancedFreeBar_coefficient_augmentation_naturality
    {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M') (N : ModuleCat.{max u v w} R) :
    ((ModuleCat.BalancedTensor.functor.{0, v, m, max u v w} ℤ R M).mapHomologicalComplex (.down ℕ)).map
        ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarResolutionAugmentation N) ≫
        balancedCoefficientChainMap g ((ChainComplex.single₀ (ModuleCat.{max u v w} R)).obj N) =
      balancedCoefficientChainMap g
          ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarResolutionChain N) ≫
        ((ModuleCat.BalancedTensor.functor.{0, v, m, max u v w} ℤ R M').mapHomologicalComplex (.down ℕ)).map
          ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarResolutionAugmentation N) :=
  balancedCoefficientChainMap_naturality g
    ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarResolutionAugmentation N)

end ModuleCat.RingHomInduction
