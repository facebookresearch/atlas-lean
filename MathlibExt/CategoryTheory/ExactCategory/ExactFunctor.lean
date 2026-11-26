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
# Exact functors for canonical abelian exact structures

Let C,D be abelian categories equipped with their canonical exact structures and F : C → D an
additive functor. Preserving admissible exact sequences is equivalent to preserving finite
limits and finite colimits.

Thus the Quillen exact-functor property agrees with exactFunctor C D F in this abelian
setting.
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- Let C,D be abelian categories with their canonical exact structures and F : C → D an additive
functor. Then F.IsExact holds if and only if F preserves finite limits and finite colimits.
The exact structure declares the ordinary short exact sequences admissible. -/
lemma Functor.isExact_iff_preservesFiniteLimits_and_colimits (F : C ⥤ D) [F.Additive] :
    F.IsExact ↔ PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  constructor
  · intro hF
    exact ((Functor.exact_tfae F).out 1 4).1 fun S hS => hF.map_admissibleExact S hS
  · intro hF
    exact ⟨((Functor.exact_tfae F).out 4 1).1 hF⟩

/-- For an additive functor F : C → D between abelian categories with canonical exact structures,
F.IsExact is equivalent to exactFunctor C D F. The equivalence identifies preservation of
admissible short exact sequences with the abelian exact-functor property. -/
lemma Functor.isExact_iff_exactFunctor (F : C ⥤ D) [F.Additive] :
    F.IsExact ↔ exactFunctor C D F := by
  rw [exactFunctor_iff]
  exact F.isExact_iff_preservesFiniteLimits_and_colimits

end CategoryTheory
