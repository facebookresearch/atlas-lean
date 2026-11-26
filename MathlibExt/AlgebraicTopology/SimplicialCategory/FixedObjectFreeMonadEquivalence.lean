/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFreeMonadComparison

/-!
# Monadicity of fixed-object simplicial enrichment

Simplicial enrichments on an object set `O` are algebras for the free-path
monad on `O × O`-indexed simplicial sets. The comparison sends an
enrichment to its Hom family with path-composition action. Its inverse
recovers identities and composition from empty and two-edge paths.

## References

- Clemens Berger and Ieke Moerdijk, *On the homotopy theory of enriched
  categories*, Section 3.3(e), for the fixed-object free enriched category
  construction, https://arxiv.org/abs/1201.2134.
-/

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectFree

variable {O : Type u}

/-- The reconstructed path action map retains each full algebra action. -/
theorem homMap_actionMap (A : (pathMonad O).Algebra) (x y : O) :
    homMap (actionMap A) x y = action A x y := homMap_ofHomMaps _ _ _ x y

/-- Reconstruction and comparison recover the algebra, including its
path action. -/
def algebraIso (A : (pathMonad O).Algebra) : comparison.obj (ofAlgebra A) ≅ A :=
  Monad.Algebra.isoMk (Iso.refl A.A) (by
    erw [Functor.map_id, Category.id_comp, Category.comp_id]
    funext p
    change action A p.1 p.2 = homMap (evaluate (ofAlgebra A)) p.1 p.2
    exact (homMap_actionMap A p.1 p.2).symm.trans
      (congrArg (fun f => homMap f p.1 p.2) (evaluate_ofAlgebra A).symm))

/-- The forward algebra comparison is the identity on its Hom family. -/
theorem algebraIso_hom_f (A : (pathMonad O).Algebra) :
    (algebraIso A).hom.f = 𝟙 A.A := rfl

/-- The inverse algebra comparison is the identity on that same Hom family. -/
theorem algebraIso_inv_f (A : (pathMonad O).Algebra) :
    (algebraIso A).inv.f = 𝟙 A.A := rfl

/-- The identity-family algebra comparison is natural in every complete algebra
morphism. -/
def algebraNatIso : 𝟭 ((pathMonad O).Algebra) ≅ realization ⋙ comparison :=
  NatIso.ofComponents (fun A => (algebraIso A).symm) (by
    intro A B f
    apply Monad.Algebra.Hom.ext
    funext p
    change f.f p = homMap (algebraMap f) p.1 p.2
    exact (homMap_algebraMap f p.1 p.2).symm)

/-- The enriched comparison is natural in every fixed-object map. -/
def originalNatIso : comparison ⋙ realization ≅ 𝟭 (FixedObjects O) :=
  NatIso.ofComponents originalIso (by
    intro C D f
    apply homMaps_ext
    intro x y
    erw [homMap_comp])

/-- The category of algebras for the free-path monad on `O × O`-indexed simplicial sets
is equivalent to the category of simplicial enrichments on `O`. -/
def equivalence : (pathMonad O).Algebra ≌ FixedObjects O where
  functor := realization
  inverse := comparison
  unitIso := algebraNatIso
  counitIso := originalNatIso
  functor_unitIso_comp A := by
    apply homMaps_ext
    intro x y
    change homMap (algebraMap (algebraIso A).inv ≫ originalMap (ofAlgebra A)) x y =
      homMap (𝟙 (ofAlgebra A)) x y
    erw [homMap_comp, homMap_algebraMap, algebraIso_inv_f]

/-- Simplicial enrichments on `O` are monadic over `O × O`-indexed families of simplicial sets. -/
theorem comparison_isEquivalence : (comparison (O := O)).IsEquivalence :=
  (equivalence (O := O)).isEquivalence_inverse

/-- Hom forgetting from simplicial enrichments on `O` to `O × O`-indexed simplicial sets
is monadic. -/
@[instance_reducible]
def underlyingMonadic : MonadicRightAdjoint (underlyingFunctor (O := O)) where
  L := freeFunctor
  adj := adjunction
  eqv := comparison_isEquivalence

end CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectFree
