/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Comma.CostructuredArrowULiftSource
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaQuillenACommonUniverse
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence

/-!
# Genuine right-comma Quillen A across original object universes

The actual original functor has source objects in u and target objects
in max u w, with the same original Hom universe. A canonical source
object lift retains every original map. The actual source-comma full
inverse functors and original point-map lift theorem supply every
comma input to the established genuine Quillen A theorem.
-/

@[expose] public section


noncomputable section

universe u w v

open CategoryTheory Opposite
open scoped Simplicial

attribute [local instance] CategoryTheory.uliftCategory

namespace SSet

variable {A : Type u} {B : Type (max u w)} [Category.{v} A] [Category.{v} B]

/-- The same actual lifted-source original nerve map is weak from every entire original comma point map. -/
theorem nerveMap_liftedSource_weak_of_rightComma (F : A ⥤ B)
    (hPoint : ∀ b : B, realizationWeakEquivalences
      (stdSimplex.isTerminalObj₀.from (nerve (CostructuredArrow F b)))) :
    realizationWeakEquivalences (nerveMap (ULift.downFunctor.{v,u,w} (C := A) ⋙ F)) := by
  let G : ULift.{w} A ⥤ B := ULift.downFunctor.{v,u,w} (C := A) ⋙ F
  apply nerveMapCommonHom_weak_of_rightComma.{max u w, v, 0} G
  intro b
  change realizationWeakEquivalences (stdSimplex.isTerminalObj₀.from (nerve (CostructuredArrow G b)))
  let e := costructuredArrowULiftSourceEquivalence.{u,max u w,v,w} F b
  have hf := nerveMap_mem_realizationWeakEquivalences_of_isEquivalence e.functor
  have hp := (nerveULiftObject_point_weak_iff (CostructuredArrow F b)).mpr (hPoint b)
  have he : nerveMap e.functor ≫ stdSimplex.isTerminalObj₀.from (nerve (ULift.{w} (CostructuredArrow F b))) =
      stdSimplex.isTerminalObj₀.from (nerve (CostructuredArrow G b)) := stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ realizationWeakEquivalences.comp_mem _ _ hf hp

end SSet
