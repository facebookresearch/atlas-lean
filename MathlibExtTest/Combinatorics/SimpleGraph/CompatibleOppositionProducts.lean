/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fin.Rev
import MathlibExt.Combinatorics.SimpleGraph.CompatibleOppositionProducts

open MetaMathlibExt SimpleGraph

private theorem pathThreeCompatible : IsCompatiblyAlmostOpposable (pathGraph 3) := by
  let S : Set (Fin 3) := {1}
  let a : pathGraph 3 ≃g pathGraph 3 :=
    ⟨Fin.revPerm, (by decide : ∀ x y : Fin 3,
      (pathGraph 3).Adj x.rev y.rev ↔ (pathGraph 3).Adj x y) _ _⟩
  have ha : Function.Involutive a := Fin.rev_involutive
  have hclosed : S ⊆ insert 1 ((pathGraph 3).neighborSet 1) :=
    fun _ hx => Set.mem_insert_iff.mpr (Or.inl hx)
  have hmaps : Set.MapsTo a Sᶜ Sᶜ := by
    intro x hx
    exact (by decide : ∀ x : Fin 3, x ≠ 1 → x.rev ≠ 1) x hx
  have hbij : Set.BijOn a Sᶜ Sᶜ :=
    ⟨hmaps, a.injective.injOn, fun x hx => ⟨a x, hmaps hx, ha x⟩⟩
  refine ⟨1, S, rfl, hclosed, a, ha, a.induce hbij, ?_, fun _ => rfl⟩
  intro x
  have hfar : ∀ x : Fin 3, x ≠ 1 → x.rev ≠ x ∧ ¬ (pathGraph 3).Adj x x.rev := by decide
  obtain ⟨hne, hnadj⟩ := hfar x x.2
  exact ⟨Subtype.ext (ha x), fun h => hne (congrArg Subtype.val h), hnadj⟩

private theorem unitCompatible : IsCompatiblyAlmostOpposable (⊥ : SimpleGraph Unit) := by
  refine ⟨(), Set.univ, Set.mem_univ _, ?_, .refl, fun _ => rfl, .refl, ?_, fun _ => rfl⟩
  · intro x _
    exact Set.mem_insert_iff.mpr (Or.inl (Subsingleton.elim _ _))
  · intro x
    exact (x.2 (Set.mem_univ _)).elim

-- Reflection in each factor deletes the central pair, leaving both kinds of surviving coordinate.
example : IsCompatiblyAlmostOpposable (strongProd (pathGraph 3) (pathGraph 3)) :=
  isCompatiblyAlmostOpposable_strongProd _ _ pathThreeCompatible pathThreeCompatible

-- Only one factor has surviving vertices, and either coordinate can be that factor.
example : IsCompatiblyAlmostOpposable (strongProd (⊥ : SimpleGraph Unit) (pathGraph 3)) :=
  isCompatiblyAlmostOpposable_strongProd _ _ unitCompatible pathThreeCompatible

example : IsCompatiblyAlmostOpposable (strongProd (pathGraph 3) (⊥ : SimpleGraph Unit)) :=
  isCompatiblyAlmostOpposable_strongProd _ _ pathThreeCompatible unitCompatible
