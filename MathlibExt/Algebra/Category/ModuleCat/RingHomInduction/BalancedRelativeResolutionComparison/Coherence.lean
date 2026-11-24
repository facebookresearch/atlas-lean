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
# Coefficient naturality of relative tensor comparisons

The scalar-changing balanced transformation for the identity ring map gives the coefficient
natural transformation. Prolongation to chain complexes and homology yields naturality of
comparison maps and counit augmentations. Coefficient and resolution universes are independent.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology
universe u v w m z
namespace ModuleCat.RingHomInduction

variable {R : Type v} [Ring R]

/-- The original right-module map has its canonical integer-linearity. -/
abbrev coefficientIntMap {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M') : M →ₗ[ℤ] M' :=
  g.hom.toAddMonoidHom.toIntLinearMap

/-- The original right action gives the exact equivariance required by the balanced map. -/
theorem coefficientIntMap_equivariant {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M')
    (r : R) (a : M) :
    coefficientIntMap g (MulOpposite.op r • a) = MulOpposite.op r • coefficientIntMap g a := by
  change g.hom (MulOpposite.op r • a) = MulOpposite.op r • g.hom a
  exact g.hom.map_smul (MulOpposite.op r) a

/-- The coefficient transformation reuses balancing and the identity restriction iso. -/
def balancedCoefficientNatTrans {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M') :
    ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M ⟶
      ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M' :=
  (Functor.leftUnitor (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M)).inv ≫
    (Functor.isoWhiskerRight (ModuleCat.restrictScalarsId.{z} R)
      (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M)).inv ≫
    ModuleCat.BalancedTensor.Along.natTrans ℤ (AlgHom.id ℤ R) (coefficientIntMap g)
      (fun r a => coefficientIntMap_equivariant g r a)

/-- The coefficient transformation changes the original right coefficient and leaves the left element. -/
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

/-- Prolongation applies the original coefficient transformation to every chain term. -/
abbrev balancedCoefficientChainMap {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M')
    (Q : ChainComplex (ModuleCat.{z} R) ℕ) :
    Functor.mappedResolution (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M) Q ⟶
      Functor.mappedResolution (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M') Q :=
  (NatTrans.mapHomologicalComplex (balancedCoefficientNatTrans.{v, m, z} g) (.down ℕ)).app Q

/-- Coefficient naturality is a literal chain-map square for every original map. -/
theorem balancedCoefficientChainMap_naturality {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M')
    {Q P : ChainComplex (ModuleCat.{z} R) ℕ} (f : Q ⟶ P) :
    ((ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M).mapHomologicalComplex (.down ℕ)).map f ≫
        balancedCoefficientChainMap g P =
      balancedCoefficientChainMap g Q ≫
        ((ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M').mapHomologicalComplex (.down ℕ)).map f :=
  NatTrans.mapHomologicalComplex_naturality (balancedCoefficientNatTrans.{v, m, z} g) f

/-- The original coefficient transformation induces its homology map. -/
abbrev balancedCoefficientHomologyMap {M M' : ModuleCat.{m} Rᵐᵒᵖ} (g : M ⟶ M')
    (Q : ChainComplex (ModuleCat.{z} R) ℕ) (n : ℕ) :
    (Functor.mappedResolution (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M) Q).homology n ⟶
      (Functor.mappedResolution (ModuleCat.BalancedTensor.functor.{0, v, m, z} ℤ R M') Q).homology n :=
  homologyMap (balancedCoefficientChainMap g Q) n

/-- The full original coefficient square commutes after homology, with no exactness premise. -/
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

/-- The existing free Bar functor preserves its full original counit augmentation. -/
theorem nativeFreeBarChainMap_augmentation {N N' : ModuleCat.{max u v w} R} (f : N ⟶ N') :
    (alternatingFaceMapComplex (ModuleCat.{max u v w} R)).map
        ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarFunctor.map f) ≫
        (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarResolutionAugmentation N' =
      (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarResolutionAugmentation N ≫
        (ChainComplex.single₀ (ModuleCat.{max u v w} R)).map f :=
  AlternatingFaceMapComplex.ε.naturality
    ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).freeBarAugmentedFunctor.map f)

/-- The computed relative comparison agrees with the free Bar functor on homology. -/
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

/-- The relative comparison is natural in every original right coefficient map. -/
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

/-- The same coefficient transformation preserves the original full counit augmentation square. -/
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
