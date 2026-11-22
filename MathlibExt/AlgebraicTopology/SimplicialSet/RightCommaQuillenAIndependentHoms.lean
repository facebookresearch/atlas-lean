/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Comma.CostructuredArrowULiftHomSource
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaQuillenAObjectUniverses
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveIndependentHomEquivalenceWeak

/-!
# Genuine original right-comma Quillen A with independent original Hom universes

The canonical source Hom lift retains every original arrow and full
comma triangle. Its complete inverse comma equivalence and actual
nerve-lift point theorem supply the genuine original comma hypotheses
for the established object-universe Quillen A map.
-/

@[expose] public section


noncomputable section

universe u w vA vB

open CategoryTheory Opposite
open scoped Simplicial

attribute [local instance] CategoryTheory.uliftCategory

namespace SSet

variable {A : Type u} {B : Type (max u w)} [Category.{vA} A] [Category.{max vA vB} B]

/-- The same actual original nerve map with canonical source Hom and object lifts is genuinely weak from every full
original comma point map. -/
theorem nerveMap_liftedSourceHom_weak_of_rightComma (F : A ⥤ B)
    (hPoint : ∀ b : B, realizationWeakEquivalences (stdSimplex.isTerminalObj₀.from (nerve (CostructuredArrow F b)))) :
    realizationWeakEquivalences (nerveMap
      (ULift.downFunctor.{max vA vB,u,w} ⋙ ULiftHom.down.{vA,u,vB} ⋙ F)) := by
  let H : ULiftHom.{vB} A ⥤ B := ULiftHom.down ⋙ F
  apply nerveMap_liftedSource_weak_of_rightComma H
  intro b
  let e := costructuredArrowULiftHomSourceEquivalence.{u,max u w,vA,max vA vB,vB} F b
  have hf := nerveMap_mem_realizationWeakEquivalences_of_isEquivalence e.functor
  have hp := (nerveULiftHom_point_weak_iff (CostructuredArrow F b)).mpr (hPoint b)
  have he : nerveMap e.functor ≫ stdSimplex.isTerminalObj₀.from (nerve (ULiftHom.{vB} (CostructuredArrow F b))) =
      stdSimplex.isTerminalObj₀.from (nerve (CostructuredArrow H b)) := stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ realizationWeakEquivalences.comp_mem _ _ hf hp

end SSet
