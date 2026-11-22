/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveObjectHomULiftIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftContainedIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaQuillenAIndependentHoms

/-!
# The same original nerve map with contained target lift

The existing fully independent nerve adapter retains every original
object and arrow. Its target lift lies in the target's original value
universe and is lowered by the full canonical coefficient isomorphism.
The same original comma point maps prove this actual map weak.
-/

@[expose] public section


noncomputable section

universe u w vA vB

open CategoryTheory Opposite

attribute [local instance] CategoryTheory.uliftCategory

namespace SSet

variable {A : Type u} {B : Type (max u w)} [Category.{vA} A] [Category.{max vA vB} B]

/-- The same complete original nerve map from its explicit original coefficient universe lift. -/
def nerveMapULiftToTarget (F : A ⥤ B) :
    uliftFunctor.{max u w vA vB,max u vA}.obj (nerve A) ⟶ nerve B :=
  nerveMapULift F ≫ (uliftContainedIso.{max u vA,max w vB} (nerve B)).hom

/-- Every same original chain is mapped by the original full functor. -/
theorem nerveMapULiftToTarget_chain (F : A ⥤ B) (q : SimplexCategoryᵒᵖ)
    (c : ComposableArrows A q.unop.len) :
    (nerveMapULiftToTarget F).app q (ULift.up c) =
      (F.mapComposableArrows q.unop.len).obj c := rfl

/-- The original object and Hom lift gives exactly the same full original coefficient-lifted nerve map. -/
theorem nerveMapULiftToTarget_sourceLift (F : A ⥤ B) :
    (nerveObjectHomULiftIso.{u,vA,w,vB} A).hom ≫
      nerveMap (ULift.downFunctor.{max vA vB,u,w} ⋙ ULiftHom.down.{vA,u,vB} ⋙ F) =
        nerveMapULiftToTarget F := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro c
  rfl

/-- Every full original comma point map supplies weakness of the SAME actual original coefficient-lifted nerve map. -/
theorem nerveMapULiftToTarget_weak_of_rightComma (F : A ⥤ B)
    (hPoint : ∀ b : B, realizationWeakEquivalences
      (stdSimplex.isTerminalObj₀.from (nerve (CostructuredArrow F b)))) :
    realizationWeakEquivalences (nerveMapULiftToTarget F) := by
  have h := realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso (nerveObjectHomULiftIso.{u,vA,w,vB} A).hom)
    (nerveMap_liftedSourceHom_weak_of_rightComma F hPoint)
  exact nerveMapULiftToTarget_sourceLift F ▸ h

end SSet
