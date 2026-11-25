/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Original sequential maps preserve a composition-stable arrow property

The native sequence constructor keeps its entire original object sequence
and successor maps. A genuine composition-stable property on those same
successor maps therefore holds on every full original sequence map.
-/

@[expose] public section

universe u v
open CategoryTheory
namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] {X : ℕ → C}
  (f : ∀ n, X n ⟶ X (n + 1))
  (W : MorphismProperty C) [W.ContainsIdentities] [W.IsStableUnderComposition]

/-- Every full original sequence map has the supplied genuine successor-map property. -/
theorem ofSequence_map_property (hf : ∀ n, W (f n)) {i j : ℕ} (g : i ⟶ j) :
    W ((ofSequence f).map g) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (leOfHom g)
  subst j
  induction k with
  | zero =>
      have hg : g = 𝟙 i := Subsingleton.elim _ _
      rw [hg, (ofSequence f).map_id]
      exact W.id_mem _
  | succ k ih =>
      have h : g = homOfLE (show i ≤ i+k by omega) ≫ homOfLE (show i+k ≤ i+k+1 by omega) :=
        Subsingleton.elim _ _
      rw [h, (ofSequence f).map_comp, ofSequence_map_homOfLE_succ]
      exact W.comp_mem _ _ (ih _) (hf _)

end CategoryTheory.Functor
