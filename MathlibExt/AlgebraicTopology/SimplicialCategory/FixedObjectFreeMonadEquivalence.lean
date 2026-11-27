/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFreeMonadComparison

/-!
# Genuine monadicity of the original fixed-object simplicial enrichment

The canonical free-path algebra comparison is an actual equivalence. The
constructed inverse preserves every original object and complete Hom family.
The unit and counit have identity maps on all original Homs; both complete
path actions are recovered. No monadicity or structure-comparison certificate
is supplied as a hypothesis.
-/

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectFree

variable {O : Type u}

/-- The actual reconstructed path action map retains each full original algebra action. -/
theorem homMap_actionMap (A : (pathMonad O).Algebra) (x y : O) :
    homMap (actionMap A) x y = action A x y := homMap_ofHomMaps _ _ _ x y

/-- Actual reconstruction and comparison recover the entire original algebra, including its
whole path action. -/
def algebraIso (A : (pathMonad O).Algebra) : comparison.obj (ofAlgebra A) ≅ A :=
  Monad.Algebra.isoMk (Iso.refl A.A) (by
    erw [Functor.map_id, Category.id_comp, Category.comp_id]
    funext p
    change action A p.1 p.2 = homMap (evaluate (ofAlgebra A)) p.1 p.2
    exact (homMap_actionMap A p.1 p.2).symm.trans
      (congrArg (fun f => homMap f p.1 p.2) (evaluate_ofAlgebra A).symm))

/-- The forward algebra comparison is the identity on its entire original Hom family. -/
theorem algebraIso_hom_f (A : (pathMonad O).Algebra) :
    (algebraIso A).hom.f = 𝟙 A.A := rfl

/-- The inverse algebra comparison is the identity on that same original Hom family. -/
theorem algebraIso_inv_f (A : (pathMonad O).Algebra) :
    (algebraIso A).inv.f = 𝟙 A.A := rfl

/-- The identity-family algebra comparison is natural in every complete original algebra
morphism. -/
def algebraNatIso : 𝟭 ((pathMonad O).Algebra) ≅ realization ⋙ comparison :=
  NatIso.ofComponents (fun A => (algebraIso A).symm) (by
    intro A B f
    apply Monad.Algebra.Hom.ext
    funext p
    change f.f p = homMap (algebraMap f) p.1 p.2
    exact (homMap_algebraMap f p.1 p.2).symm)

/-- The whole original enriched comparison is natural in every original fixed-object map. -/
def originalNatIso : comparison ⋙ realization ≅ 𝟭 (FixedObjects O) :=
  NatIso.ofComponents originalIso (by
    intro C D f
    apply homMaps_ext
    intro x y
    erw [homMap_comp])

/-- The actual fixed-object simplicial enrichments are precisely the canonical free-path
algebras. -/
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

/-- The actual native canonical monad comparison is an equivalence, with no supplied
monadicity premise. -/
theorem comparison_isEquivalence : (comparison (O := O)).IsEquivalence :=
  (equivalence (O := O)).isEquivalence_inverse

/-- The actual original whole-Hom forgetful functor is monadic through its canonical free
adjunction. -/
@[instance_reducible]
def underlyingMonadic : MonadicRightAdjoint (underlyingFunctor (O := O)) where
  L := freeFunctor
  adj := adjunction
  eqv := comparison_isEquivalence

end CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectFree
