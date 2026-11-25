/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-!
# Brown's lemma for fibrant objects and a target morphism class

A functor from a model category carries weak equivalences between fibrant
objects into a target morphism class containing isomorphisms and satisfying
two-out-of-three, provided it carries trivial fibrations between fibrant
objects into that class. The proof uses the native `FibrantBrownFactorization`.

## References

* D.-C. Cisinski, *Higher Categories and Homotopical Algebra*, Proposition
  2.2.7, in its fibrant dual form.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ v₁ v₂

open CategoryTheory HomotopicalAlgebra CategoryTheory.MorphismProperty

namespace CategoryTheory.Functor

/-- A functor from a model category sends weak equivalences between
fibrant objects into any target class with two-out-of-three containing
isomorphisms, if it sends trivial fibrations between fibrant objects
into that class. -/
theorem map_mem_of_weakEquivalence_of_fibrant
    {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    (V : MorphismProperty D) [V.HasTwoOutOfThreeProperty]
    (hIso : isomorphisms D ≤ V)
    (hTF : ∀ {A B : C} (p : A ⟶ B) [IsFibrant A] [IsFibrant B],
      trivialFibrations C p → V (F.map p))
    {X Y : C} (f : X ⟶ Y) [IsFibrant X] [IsFibrant Y]
    [WeakEquivalence f] : V (F.map f) := by
  let h : FibrantBrownFactorization f := Classical.choice inferInstance
  let _ : WeakEquivalence h.p := inferInstance
  let _ : WeakEquivalence h.r := inferInstance
  let _ : IsFibrant h.Z := isFibrant_of_fibration h.p
  have hp : V (F.map h.p) := hTF h.p (mem_trivialFibrations h.p)
  have hr : V (F.map h.r) := hTF h.r (mem_trivialFibrations h.r)
  have hir : V (F.map h.i ≫ F.map h.r) := by
    rw [← F.map_comp, h.i_r, F.map_id]
    exact hIso _ (isomorphisms.infer_property _)
  have hi : V (F.map h.i) := V.of_postcomp _ _ hr hir
  rw [← h.fac, F.map_comp]
  exact V.comp_mem _ _ hi hp

end CategoryTheory.Functor
