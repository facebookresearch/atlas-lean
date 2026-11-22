/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-!
# Quillen functors and Brown's lemma

A left Quillen functor preserves weak equivalences between cofibrant objects,
and a right Quillen functor preserves weak equivalences between fibrant
objects.  The proofs use Brown's factorizations; no preservation statement is
made for arbitrary objects.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace CategoryTheory.Adjunction.IsQuillenAdjunction

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} {adj : L ⊣ R}

/-- A left Quillen functor preserves weak equivalences between cofibrant
objects. -/
theorem map_weakEquivalence_of_cofibrant {X Y : C} (f : X ⟶ Y)
    [IsQuillenAdjunction adj] [WeakEquivalence f]
    [IsCofibrant X] [IsCofibrant Y] :
    WeakEquivalence (L.map f) := by
  let h : CofibrantBrownFactorization f := Classical.choice inferInstance
  let _ : WeakEquivalence h.i := inferInstance
  let _ : WeakEquivalence h.s := inferInstance
  have hi : trivialCofibrations D (L.map h.i) :=
    (inferInstance : IsQuillenAdjunction adj).preservesTrivialCofibrations
      h.i (mem_trivialCofibrations h.i)
  have hs : trivialCofibrations D (L.map h.s) :=
    (inferInstance : IsQuillenAdjunction adj).preservesTrivialCofibrations
      h.s (mem_trivialCofibrations h.s)
  let _ : WeakEquivalence (L.map h.i) :=
    ((mem_trivialCofibrations_iff (f := L.map h.i)).mp hi).2
  let _ : WeakEquivalence (L.map h.s) :=
    ((mem_trivialCofibrations_iff (f := L.map h.s)).mp hs).2
  have hs_p : L.map h.s ≫ L.map h.p = 𝟙 (L.obj Y) := by
    rw [← L.map_comp, h.s_p, L.map_id]
  let _ : WeakEquivalence (L.map h.p) :=
    weakEquivalence_of_precomp_of_fac hs_p
  rw [← h.fac, L.map_comp]
  infer_instance

/-- A right Quillen functor preserves weak equivalences between fibrant
objects. -/
theorem map_weakEquivalence_of_fibrant {X Y : D} (f : X ⟶ Y)
    [IsQuillenAdjunction adj] [WeakEquivalence f]
    [IsFibrant X] [IsFibrant Y] :
    WeakEquivalence (R.map f) := by
  let h : FibrantBrownFactorization f := Classical.choice inferInstance
  let _ : WeakEquivalence h.p := inferInstance
  let _ : WeakEquivalence h.r := inferInstance
  have hp : trivialFibrations C (R.map h.p) :=
    (preservesTrivialFibrations (adj := adj))
      h.p (mem_trivialFibrations h.p)
  have hr : trivialFibrations C (R.map h.r) :=
    (preservesTrivialFibrations (adj := adj))
      h.r (mem_trivialFibrations h.r)
  let _ : WeakEquivalence (R.map h.p) :=
    ((mem_trivialFibrations_iff (f := R.map h.p)).mp hp).2
  let _ : WeakEquivalence (R.map h.r) :=
    ((mem_trivialFibrations_iff (f := R.map h.r)).mp hr).2
  have hi_r : R.map h.i ≫ R.map h.r = 𝟙 (R.obj X) := by
    rw [← R.map_comp, h.i_r, R.map_id]
  let _ : WeakEquivalence (R.map h.i) :=
    weakEquivalence_of_postcomp_of_fac hi_r
  rw [← h.fac, R.map_comp]
  infer_instance

end CategoryTheory.Adjunction.IsQuillenAdjunction
