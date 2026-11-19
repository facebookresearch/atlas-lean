/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Order.ScottContinuity.FunctionSpace
public import Mathlib.Tactic

open MathlibExt.Order.ScottContinuity.FunctionSpace

/-- The pointwise supremum of the directed pair `{x ↦ ∅, id}` of Scott-continuous maps on
`Set ℕ` is Scott-continuous. -/
example : ScottContinuous fun x : Set ℕ =>
    sSup ((fun f : Set ℕ → Set ℕ => f x) '' ({fun _ => ∅, id} : Set (Set ℕ → Set ℕ))) := by
  refine scottContinuous_sSup_image_of_directedOn ?_ ?_
  · rintro f (rfl | rfl) g (rfl | rfl)
    all_goals exact ⟨id, Or.inr rfl, fun x => by simp, fun x => by simp⟩
  · rintro f (rfl | rfl)
    · exact ScottContinuous.const _
    · exact ScottContinuous.id

/-- Arbitrary pointwise suprema of Scott-continuous maps between complete lattices. -/
example : ScottContinuous (sSup ({fun _ => ∅, id} : Set (Set ℕ → Set ℕ))) := by
  refine scottContinuous_sSup ?_
  rintro f (rfl | rfl)
  · exact ScottContinuous.const _
  · exact ScottContinuous.id

private theorem scottContinuous_sup_zero : ScottContinuous fun x : Set ℕ => x ⊔ {0} :=
  (ScottContinuous.id.prodMk (ScottContinuous.const {0})).comp ScottContinuous.sup₂

/-- Kleene: the least fixed point of `x ↦ x ∪ {0}` on `Set ℕ` is `{0}`. -/
example : (⨆ n, (fun x : Set ℕ => x ⊔ {0})^[n] ⊥) = {0} := by
  apply le_antisymm (iSup_iterate_bot_le scottContinuous_sup_zero (by simp))
  have h := map_iSup_iterate_bot scottContinuous_sup_zero
  intro m hm
  rw [← h]
  exact Or.inr hm

/-- The dcpo Kleene supremum is the repository's ω-chain least fixed point, by definition. -/
example : (⨆ n, (fun x : Set ℕ => x ⊔ {0})^[n] ⊥) =
    OmegaCompletePartialOrder.ContinuousHom.lfp
      (OmegaCompletePartialOrder.ContinuousHom.ofFun _ scottContinuous_sup_zero.ωScottContinuous) :=
  iSup_iterate_bot_eq_lfp scottContinuous_sup_zero
