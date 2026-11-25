/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Enriched/OppositeFunctor.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import Mathlib.CategoryTheory.Enriched.Opposite

/-!
# Opposite enriched functors

A functor between categories enriched in a braided monoidal category also acts on their
opposites. Its map on the Hom object from `op X` to `op Y` is the original map from `Y` to
`X`. Naturality of the braiding makes this map preserve opposite composition.

This applies in particular to differential graded functors: the braiding of cochain complexes
supplies the Koszul sign in opposite composition, and the same chain maps define the opposite
functor. The construction is useful when a left action is expressed as a right action of an
opposite differential graded category.

## References

* `Mathlib.CategoryTheory.Enriched.Opposite`, for the opposite enriched category.
-/

@[expose] public section

namespace CategoryTheory.EnrichedFunctor

open MonoidalCategory BraidedCategory Opposite

universe v₁ u₁ v₂ u₂ u₃

variable {V : Type u₁} [Category.{v₁} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u₂} {D : Type u₃} [EnrichedCategory V C] [EnrichedCategory V D]

/-- The opposite of an enriched functor, with the same map on each Hom object after reversing
its source and target. -/
@[simps]
def op (F : EnrichedFunctor V C D) : EnrichedFunctor V Cᵒᵖ Dᵒᵖ where
  obj X := Opposite.op (F.obj X.unop)
  map X Y := F.map Y.unop X.unop
  map_id X := F.map_id X.unop
  map_comp X Y Z := by
    rw [eComp_op_eq_assoc, F.map_comp]
    exact (tensorHom_eComp_op_eq ..).symm

/-- Taking opposites sends the identity enriched functor to the identity. -/
@[simp]
theorem op_id :
    (EnrichedFunctor.id V C).op = EnrichedFunctor.id V Cᵒᵖ := rfl

/-- Taking opposites preserves composition of enriched functors. -/
@[simp]
theorem op_comp {E : Type*} [EnrichedCategory V E]
    (F : EnrichedFunctor V C D) (G : EnrichedFunctor V D E) :
    (F.comp V G).op = F.op.comp V G.op := rfl

end CategoryTheory.EnrichedFunctor
