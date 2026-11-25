/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.Separations.CountercurrentBalance
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Domains.Chemistry.Separations.CountercurrentBalance

-- Two stages, with different carrier flows and nonconstant component flows.
example : (2 : ℝ) * 1 + 1 * 9 = 2 * 3 + 1 * 5 := by
  let x (k : ℕ) : ℝ := k + 1
  let y (k : ℕ) : ℝ := 2 * (k : ℝ) + 3
  have hstage (k : ℕ) (_ : k < 2) :
      (2 : ℝ) * x k + 1 * y (k + 2) = 2 * x (k + 1) + 1 * y (k + 1) := by
    dsimp only [x, y]
    push_cast
    ring
  have h := external_component_balance 2 (by norm_num) (fun _ => 2) (fun _ => 1) x y
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) hstage
  change (2 : ℝ) * x 0 + 1 * y 3 = 2 * x 2 + 1 * y 1 at h
  simpa only [show x 0 = 1 by norm_num [x], show x 2 = 3 by norm_num [x],
    show y 3 = 9 by norm_num [y], show y 1 = 5 by norm_num [y]] using h

-- A single stage has exactly the four boundary streams.
example (L V x y : ℕ → ℝ) (hL : ∀ k ≤ 1, 0 < L k) (hV : ∀ k ≤ 1, 0 < V (k + 1))
    (h : L 0 * x 0 + V 2 * y 2 = L 1 * x 1 + V 1 * y 1) :
    L 0 * x 0 + V 2 * y 2 = L 1 * x 1 + V 1 * y 1 := by
  apply external_component_balance 1 (by norm_num) L V x y hL hV
  intro k hk
  have hk₀ : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
  subst k
  exact h
