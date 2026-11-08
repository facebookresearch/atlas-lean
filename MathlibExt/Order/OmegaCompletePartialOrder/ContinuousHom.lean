/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bottom, currying, and least fixed points for Scott-continuous maps
-/
module

public import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Bottom, currying, and least fixed points for Scott-continuous maps

Mathlib's `Mathlib.Order.OmegaCompletePartialOrder` provides Scott-continuous
maps `α →𝒄 β` with their pointwise ω-complete order, continuity of the
projections (`ωScottContinuous_fst`, `ωScottContinuous_snd`), application
(`ContinuousHom.Prod.apply`), `ContinuousHom.flip`, and Kleene iteration
(`fixedPoints.iterateChain` with `fixedPoints.ωSup_iterate_mem_fixedPoint` and
`fixedPoints.ωSup_iterate_le_prefixedPoint`). This file adds what the
denotational semantics of a typed functional language needs on top of that:

* `ContinuousHom.instOrderBot`: the constantly-`⊥` map is the least continuous
  map, so continuous function spaces into pointed ω-CPOs are pointed;
* `ContinuousHom.ωScottContinuous_of_apply`: a map into a continuous function
  space is continuous when it is continuous at every argument;
* `ContinuousHom.curry`: currying of continuous maps out of a product;
* `ContinuousHom.lfp`: the least fixed point of a continuous endomap of a
  pointed ω-CPO, the supremum of the Kleene chain, with `lfp_eq`, `lfp_le`,
  `lfp_mono`, and the continuity of `lfp` itself (`lfp_ωScottContinuous`,
  bundled as `ContinuousHom.lfpHom`).

These are the standard facts of Scott's model of PCF (Plotkin, *LCF considered
as a programming language*, TCS 5, 1977; Streicher, *Domain-Theoretic
Foundations of Functional Programming*, 2006, ch. 2-4).
-/

@[expose] public section

namespace OmegaCompletePartialOrder

namespace ContinuousHom

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
variable [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
variable [OmegaCompletePartialOrder γ]

/-- The constantly-`⊥` continuous map is the least continuous map. -/
instance instOrderBot [OrderBot β] : OrderBot (α →𝒄 β) where
  bot := const ⊥
  bot_le _ _ := bot_le

@[simp] theorem bot_apply [OrderBot β] (a : α) : (⊥ : α →𝒄 β) a = ⊥ := rfl

/-- A map into a continuous function space is continuous if it is continuous
at each argument. -/
theorem ωScottContinuous_of_apply {g : α → β →𝒄 γ}
    (h : ∀ b, ωScottContinuous fun a => g a b) : ωScottContinuous g := by
  have hmono : Monotone g := fun a a' haa' b => (h b).monotone haa'
  refine ωScottContinuous.of_monotone_map_ωSup ⟨hmono, fun c => ContinuousHom.ext _ _ fun b => ?_⟩
  rw [(h b).map_ωSup, ωSup_def, ωSup_apply]
  apply le_antisymm <;> apply ωSup_le_ωSup_of_le <;> intro i <;> exact ⟨i, le_rfl⟩

/-- Currying of continuous maps out of a product. -/
def curry (f : α × β →𝒄 γ) : α →𝒄 (β →𝒄 γ) :=
  ofFun (fun a => ofFun (fun b => f (a, b)))
    (ωScottContinuous_of_apply fun b => show ωScottContinuous (fun a => f (a, b)) by fun_prop)

@[simp] theorem curry_apply (f : α × β →𝒄 γ) (a : α) (b : β) : curry f a b = f (a, b) := rfl

section Fix

variable {D : Type u} [OmegaCompletePartialOrder D] [OrderBot D]

/-- The least fixed point of a continuous endomap of a pointed ω-CPO: the
supremum of the Kleene chain `⊥ ≤ f ⊥ ≤ f (f ⊥) ≤ …`. -/
def lfp (f : D →𝒄 D) : D := ωSup (fixedPoints.iterateChain f ⊥ bot_le)

theorem lfp_def (f : D →𝒄 D) : lfp f = ωSup (fixedPoints.iterateChain f ⊥ bot_le) := rfl

/-- `lfp f` is a fixed point. -/
theorem lfp_eq (f : D →𝒄 D) : f (lfp f) = lfp f :=
  fixedPoints.ωSup_iterate_mem_fixedPoint f ⊥ bot_le

/-- `lfp f` is below every prefixed point, so it is the least fixed point. -/
theorem lfp_le (f : D →𝒄 D) {a : D} (h : f a ≤ a) : lfp f ≤ a :=
  fixedPoints.ωSup_iterate_le_prefixedPoint f ⊥ bot_le h bot_le

theorem lfp_mono : Monotone (lfp : (D →𝒄 D) → D) := by
  intro f g hfg
  apply lfp_le
  calc f (lfp g) ≤ g (lfp g) := hfg _
    _ = lfp g := lfp_eq g

/-- The least-fixed-point operator is itself continuous. -/
theorem lfp_ωScottContinuous : ωScottContinuous (lfp : (D →𝒄 D) → D) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨lfp_mono, fun c => le_antisymm ?_ ?_⟩
  · apply lfp_le
    rw [ωSup_def, ωSup_apply]
    apply ωSup_le
    intro j
    change (c j) (ωSup (c.map ⟨lfp, lfp_mono⟩)) ≤ _
    rw [(c j).continuous]
    apply ωSup_le
    intro i
    apply le_ωSup_of_le (max i j)
    change (c j) (lfp (c i)) ≤ lfp (c (max i j))
    calc (c j) (lfp (c i)) ≤ (c (max i j)) (lfp (c (max i j))) :=
          apply_mono (c.monotone (le_max_right i j)) (lfp_mono (c.monotone (le_max_left i j)))
      _ = lfp (c (max i j)) := lfp_eq _
  · apply ωSup_le
    intro i
    exact lfp_mono (le_ωSup c i)

/-- The least-fixed-point operator as a continuous map. -/
def lfpHom : (D →𝒄 D) →𝒄 D := ofFun lfp lfp_ωScottContinuous

@[simp] theorem lfpHom_apply (f : D →𝒄 D) : lfpHom f = lfp f := rfl

end Fix

end ContinuousHom

end OmegaCompletePartialOrder
