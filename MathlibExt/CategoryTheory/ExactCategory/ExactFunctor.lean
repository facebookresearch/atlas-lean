/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import MathlibExt.CategoryTheory.ExactCategory.Abelian
public import MathlibExt.CategoryTheory.ExactCategory.Functor

/-!
# Exact functors between abelian categories

For abelian categories with their canonical exact structures, Quillen exact functors are exactly
Mathlib's functors preserving finite limits and finite colimits.
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- For canonical exact structures on abelian categories, preserving admissible exact sequences is
 equivalent to preserving finite limits and finite colimits. -/
lemma Functor.isExact_iff_preservesFiniteLimits_and_colimits (F : C ⥤ D) [F.Additive] :
    F.IsExact ↔ PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  constructor
  · intro hF
    exact ((Functor.exact_tfae F).out 1 4).1 fun S hS => hF.map_admissibleExact S hS
  · intro hF
    exact ⟨((Functor.exact_tfae F).out 4 1).1 hF⟩

/-- For canonical exact structures on abelian categories, Quillen exactness agrees with Mathlib's
`exactFunctor` property. -/
lemma Functor.isExact_iff_exactFunctor (F : C ⥤ D) [F.Additive] :
    F.IsExact ↔ exactFunctor C D F := by
  rw [exactFunctor_iff]
  exact F.isExact_iff_preservesFiniteLimits_and_colimits

end CategoryTheory
