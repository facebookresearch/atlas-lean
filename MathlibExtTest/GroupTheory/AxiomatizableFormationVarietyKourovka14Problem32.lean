/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.AxiomatizableFormationVarietyKourovka14Problem32
import Mathlib.Algebra.Group.PUnit
import Mathlib.Tactic.Group

/-!
Tests for formations, first-order axiomatizable classes and varieties of groups
(Kourovka Notebook Problem 14.32).
-/

open FirstOrder FirstOrder.Language
open MathlibExt.GroupTheory.AxiomatizableFormationVarietyKourovka14Problem32Wanted

-- The Gaglione–Spellman question has a negative answer.
example : ¬ axiomatizableFormationIsVariety := axiomatizableFormationIsVariety_refuted

-- The class of all groups is a formation, axiomatized by the empty theory, and a variety
-- defined by the empty set of laws.
example : IsFormation (fun _ _ => True) :=
  ⟨⟨Unit, inferInstance, trivial⟩, fun _ _ _ _ _ _ _ => trivial,
    fun _ _ _ _ _ _ _ _ => trivial⟩

example : IsAxiomatizable (fun _ _ => True) :=
  ⟨∅, fun G _ => by simp [Theory.model_iff]⟩

example : IsVariety (fun _ _ => True) :=
  ⟨∅, fun _ _ => by simp⟩

-- Formations are nonempty, so the empty class is not one.
example : ¬ IsFormation (fun _ _ => False) := fun h => by
  obtain ⟨_, _, h⟩ := h.1
  exact h

-- Every formation contains the trivial group.
example (𝔉 : GroupClass) (h : IsFormation 𝔉) : 𝔉 Unit := by
  obtain ⟨G, _, hG⟩ := h.1
  exact h.2.1 G Unit (1 : G →* Unit) (fun _ => ⟨1, Subsingleton.elim _ _⟩) hG

-- The abelian groups form the variety defined by the law `x₀ x₁ x₀⁻¹ x₁⁻¹ = 1`.
example : IsVariety (fun G _ => ∀ a b : G, a * b = b * a) := by
  refine ⟨{FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹},
    fun G _ => ?_⟩
  simp only [Set.mem_singleton_iff, forall_eq, map_mul, map_inv, FreeGroup.lift_apply_of]
  constructor
  · intro h x
    rw [h (x 0) (x 1)]
    group
  · intro h a b
    have hab := h fun n => if n = 0 then a else b
    simp only [↓reduceIte, one_ne_zero] at hab
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hab
    exact hab

-- A variety is closed under subgroups; the refutation exhibits a formation that is not.
example (𝔉 : GroupClass) (h𝔉 : IsVariety 𝔉) (G : Type) [Group G] (H : Subgroup G)
    (hG : 𝔉 G) : 𝔉 H := by
  obtain ⟨W, hW⟩ := h𝔉
  refine (hW H).mpr fun w hw x => Subtype.ext ?_
  have hlift : H.subtype (FreeGroup.lift x w) = FreeGroup.lift (H.subtype ∘ x) w :=
    FreeGroup.lift_unique (H.subtype.comp (FreeGroup.lift x)) fun a => by simp
  rw [← Subgroup.coe_subtype, hlift, (hW G).mp hG w hw _, map_one]
