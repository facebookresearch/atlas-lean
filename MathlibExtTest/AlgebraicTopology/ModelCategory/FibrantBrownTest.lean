/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FibrantBrown

/-! # A Brown-lemma client with a target weak-equivalence category -/

set_option autoImplicit false

universe u₁ u₂ v₁ v₂

open CategoryTheory HomotopicalAlgebra CategoryTheory.MorphismProperty

/-- The generic theorem can produce a target `WeakEquivalence` instance
from the weak-equivalence-category interface and class-valued preservation
of trivial fibrations. -/
example {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [CategoryWithWeakEquivalences D]
    [(weakEquivalences D).ContainsIdentities]
    [(weakEquivalences D).RespectsIso]
    [(weakEquivalences D).HasTwoOutOfThreeProperty]
    (F : C ⥤ D)
    (hTF : ∀ {A B : C} (p : A ⟶ B) [IsFibrant A] [IsFibrant B]
      [Fibration p] [WeakEquivalence p], WeakEquivalence (F.map p))
    {X Y : C} (f : X ⟶ Y) [IsFibrant X] [IsFibrant Y]
    [WeakEquivalence f] : WeakEquivalence (F.map f) := by
  apply (weakEquivalence_iff (F.map f)).mpr
  apply F.map_mem_of_weakEquivalence_of_fibrant (weakEquivalences D)
    (isomorphisms_le_of_containsIdentities (weakEquivalences D))
  intro A B p _ _ hp
  let _ : Fibration p := (fibration_iff p).mpr hp.1
  let _ : WeakEquivalence p := (weakEquivalence_iff p).mpr hp.2
  let _ : WeakEquivalence (F.map p) := hTF p
  exact mem_weakEquivalences (F.map p)
