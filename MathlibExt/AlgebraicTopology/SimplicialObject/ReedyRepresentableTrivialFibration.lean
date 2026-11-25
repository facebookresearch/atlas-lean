/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.SimplicialObject.CoefficientReedyMorphismPropertyTransport
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RelativeMatchingTrivialFibration
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Original representables send Reedy trivial fibrations to Kan trivial fibrations

An original cofibrant object lifts against every original trivial
fibration. Its representable therefore sends every actual relative
matching map to an epimorphism. Canonical coefficient matching transport
and the established Kan boundary recognition prove a genuine trivial
fibration of the full Hom simplicial objects. Category object and Hom
universes are independent; no new functor model is constructed.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite HomotopicalAlgebra MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [ModelCategory C]

private theorem representable_trivialFibration_epi (A : C) [IsCofibrant A]
    {X Y : C} (p : X ⟶ Y) (hp : trivialFibrations C p) :
    Epi ((coyoneda.obj (op A)).map p) := by
  let _ : Fibration p := (fibration_iff p).mpr hp.1
  let _ : WeakEquivalence p := (weakEquivalence_iff p).mpr hp.2
  apply (CategoryTheory.epi_iff_surjective _).mpr
  intro g
  let sq : CommSq (initial.to X) (initial.to A) p g := ⟨initialIsInitial.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- The SAME actual Reedy right trivial class induces a genuine Kan trivial fibration on full
original
representables. -/
theorem representable_reedy_trivialFibration
    [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C] (A : C) [IsCofibrant A]
    {X Y : SimplicialObject C} (f : X ⟶ Y) (hf : reedyRight (trivialFibrations C) f) :
    trivialFibrations SSet.{v} (Functor.whiskerRight f (coyoneda.obj (op A))) := by
  apply SSet.modelCategoryQuillen.trivialFibration_of_relativeMatching_epimorphisms
  intro n
  have hE : epimorphisms (Type v)
      ((coyoneda.obj (op A)).map (relativeMatchingMap f n)) :=
    representable_trivialFibration_epi A (relativeMatchingMap f n) (hf n)
  exact (CoefficientReedyTransport.relativeMatching_mem_iff (coyoneda.obj (op A))
    (epimorphisms (Type v)) n f).mp hE

end CategoryTheory.SimplicialObject
