/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Order.OmegaCompletePartialOrder.ContinuousHom

/-!
# Tests for bottom, currying, and least fixed points of continuous maps

* `⊥` of a continuous function space is pointwise `⊥`; `curry` computes.
* The least fixed point of the identity is `⊥`, of a constant map the constant.
* The factorial functional on `ℕ → Part ℕ`: its least fixed point is computed at
  `3` by unfolding `lfp_eq`, and it is total.
* `lfpHom` is the bundled `lfp`.
-/

@[expose] public section

namespace OmegaCompletePartialOrder.ContinuousHom.Tests

example (x : Part ℕ) : (⊥ : Part ℕ →𝒄 Part ℕ) x = Part.none := rfl

example (f : Part ℕ × Part ℕ →𝒄 Part ℕ) (a b : Part ℕ) : curry f a b = f (a, b) := by simp

/-- The least fixed point of the identity is `⊥`. -/
example : lfp (ContinuousHom.id : Part ℕ →𝒄 Part ℕ) = ⊥ :=
  le_antisymm (lfp_le _ le_rfl) bot_le

/-- The least fixed point of a constant map is the constant. -/
example : lfp (const (Part.some 3) : Part ℕ →𝒄 Part ℕ) = Part.some 3 := (lfp_eq _).symm

/-- The factorial functional: `F g n = 1` if `n = 0`, else `n * g (n - 1)`. -/
noncomputable def factF : (ℕ → Part ℕ) →𝒄 (ℕ → Part ℕ) :=
  ofFun (fun g n => if n = 0 then Part.some 1 else (g (n - 1)).map (· * n))
    (ωScottContinuous.of_apply₂ fun n => by
      by_cases hn : n = 0
      · simp only [hn, ↓reduceIte]
        exact ωScottContinuous.const
      · simpa [hn] using ContinuousHom.ωScottContinuous.map (f := (· * n))
          (ωScottContinuous.apply (β := fun _ : ℕ => Part ℕ) (n - 1)))

theorem lfp_factF_succ (n : ℕ) : lfp factF (n + 1) = (lfp factF n).map (· * (n + 1)) := by
  conv_lhs => rw [← lfp_eq factF]
  simp [factF]

theorem lfp_factF_zero : lfp factF 0 = Part.some 1 := by
  conv_lhs => rw [← lfp_eq factF]
  simp [factF]

example : lfp factF 3 = Part.some 6 := by
  simp [lfp_factF_succ, lfp_factF_zero]

/-- The least fixed point of the factorial functional is total. -/
example (n : ℕ) : (lfp factF n).Dom := by
  induction n with
  | zero => simp [lfp_factF_zero]
  | succ n ih => rw [lfp_factF_succ]; exact ih

example (f : Part ℕ →𝒄 Part ℕ) : lfpHom f = lfp f := rfl

end OmegaCompletePartialOrder.ContinuousHom.Tests
