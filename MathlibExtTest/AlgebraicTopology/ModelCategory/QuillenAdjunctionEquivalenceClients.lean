/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence

/-! # Clients of the Quillen adjunction and equivalence interfaces -/

open CategoryTheory HomotopicalAlgebra

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {E : Type u₃} [Category.{v₃} E] [ModelCategory E]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {L' : D ⥤ E} {R' : E ⥤ D} (adj' : L' ⊣ R')

-- Build the Quillen structure from right preservation, then consume left
-- preservation on a cofibrant object. No left preservation is assumed.
example (hf : PreservesFibrations R) (ht : PreservesTrivialFibrations R)
    (X : C) [IsCofibrant X] : IsCofibrant (L.obj X) := by
  let := (Adjunction.IsQuillenAdjunction.isQuillenAdjunction_iff (adj := adj)).mpr ⟨hf, ht⟩
  exact (Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj)).isCofibrant
    inferInstance

-- A left-preservation witness also lets a client transport terminal fibrancy.
example [adj.IsQuillenAdjunction] (Y : D) [IsFibrant Y] : IsFibrant (R.obj Y) :=
  (Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj)).isFibrant inferInstance

-- Use the composite equivalence on an actual arrow. Intermediate cofibrancy
-- and fibrancy witnesses must come from the equivalences, not the client.
example [adj.IsQuillenEquivalence] [adj'.IsQuillenEquivalence]
    {X : C} [IsCofibrant X] {Z : E} [IsFibrant Z] (f : L'.obj (L.obj X) ⟶ Z) :
    WeakEquivalence f ↔
      WeakEquivalence (adj.homEquiv X (R'.obj Z) (adj'.homEquiv (L.obj X) Z f)) := by
  simpa only [Adjunction.comp_homEquiv, Equiv.trans_apply] using
    (Adjunction.IsQuillenEquivalence.weakEquivalence_homEquiv_iff
      (adj := adj.comp adj') f)

-- A fibrant target alone is not the counit criterion: the right image must
-- also be cofibrant. This tests the theorem with the exact endpoint classes.
example [adj.IsQuillenEquivalence] (Y : D) [IsFibrant Y] [IsCofibrant (R.obj Y)] :
    WeakEquivalence (adj.counit.app Y) :=
  Adjunction.IsQuillenEquivalence.weakEquivalence_counit (adj := adj) Y
