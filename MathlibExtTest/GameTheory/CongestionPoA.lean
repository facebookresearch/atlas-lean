/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.CongestionPoA

import Mathlib.Tactic

open MathlibExt.GameTheory.CongestionGame

/-- Boundary check: the optimal profile itself, when it satisfies the
deviation-to-`opt` hypothesis, satisfies the bound with room to spare. -/
example {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (a b : R → ℝ) (ha : ∀ r, 0 ≤ a r) (hb : ∀ r, 0 ≤ b r) (opt : Fin n → R)
    (hNash : ∀ (i : Fin n),
      a (opt i) * (loadOf opt (opt i) : ℝ) + b (opt i) ≤
        a (opt i) * ((loadOf (Function.update opt i (opt i)) (opt i) : ℝ))
          + b (opt i)) :
    socialCost a b opt ≤ (5 / 2) * socialCost a b opt :=
  congestion_poa a b ha hb opt opt hNash

/-- Load computation: with one player, their resource has load `1`. -/
example (r : Fin 2) : loadOf (fun _ : Fin 1 => r) r = 1 := by
  simp [loadOf]

/-- Concrete two-player game with affine delays `a = 1`, `b = 0`:
the split profile has load `1` on each resource and social cost `2`,
while the all-on-`0` profile has social cost `4`. -/
example : loadOf (fun i : Fin 2 => i) (0 : Fin 2) = 1 ∧
    loadOf (fun i : Fin 2 => i) (1 : Fin 2) = 1 ∧
    socialCost (fun _ : Fin 2 => (1 : ℝ)) (fun _ => (0 : ℝ))
      (fun i : Fin 2 => i) = 2 ∧
    socialCost (fun _ : Fin 2 => (1 : ℝ)) (fun _ => (0 : ℝ))
      (fun _ : Fin 2 => (0 : Fin 2)) = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · have h0 : loadOf (fun i : Fin 2 => i) (0 : Fin 2) = 1 := by decide
    have h1 : loadOf (fun i : Fin 2 => i) (1 : Fin 2) = 1 := by decide
    simp [socialCost, Fin.sum_univ_two, h0, h1]
    norm_num
  · have h2 : loadOf (fun _ : Fin 2 => (0 : Fin 2)) (0 : Fin 2) = 2 := by decide
    simp [socialCost, h2]
    norm_num

/-- In the concrete game above, the split profile satisfies the
deviation-to-`opt` hypothesis against the all-on-`0` profile, and the
`5 / 2` bound is nontrivial (`2 ≤ 10`). -/
example : socialCost (fun _ : Fin 2 => (1 : ℝ)) (fun _ => (0 : ℝ))
      (fun i : Fin 2 => i) ≤
    (5 / 2) * socialCost (fun _ : Fin 2 => (1 : ℝ)) (fun _ => (0 : ℝ))
      (fun _ : Fin 2 => (0 : Fin 2)) := by
  apply congestion_poa (fun _ : Fin 2 => (1 : ℝ)) (fun _ => (0 : ℝ))
    (fun _ => by norm_num) (fun _ => by norm_num)
    (fun i : Fin 2 => i) (fun _ : Fin 2 => (0 : Fin 2))
  intro i
  fin_cases i
  · simp [loadOf]
  · simp [loadOf]
    decide
