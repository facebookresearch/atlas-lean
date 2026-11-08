/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.LotkaVolterra

/-! Tests for the Lotka–Volterra first integral: concrete values, the equilibrium solution as a
non-vacuity witness, and the minimum at the coexistence equilibrium. -/

open Real

namespace MathlibExtTest.Biology.Dynamics.LotkaVolterra

open MathlibExt.Biology.Dynamics.LotkaVolterra

example : firstIntegral 1 1 1 1 1 1 = 2 := by norm_num [firstIntegral]

example (x y : ℝ) : firstIntegral 0 0 0 0 x y = 0 := by simp [firstIntegral]

/-- Outside the positive quadrant `V` takes a junk value: `log 0 = 0` gives `V(0, 1) = 1`. -/
example : firstIntegral 1 1 1 1 0 1 = 1 := by simp [firstIntegral]

/-- **Non-vacuity witness.** With `α = 2`, `β = 1`, `γ = 3`, `δ = 1`, the coexistence equilibrium
`x ≡ γ / δ = 3`, `y ≡ α / β = 2` solves the system and stays positive, so the hypotheses of
`firstIntegral_eq` are satisfiable. -/
example (t : ℝ) (ht : 0 ≤ t) :
    firstIntegral 2 1 3 1 ((fun _ => (3 : ℝ)) t) ((fun _ => (2 : ℝ)) t) =
      firstIntegral 2 1 3 1 ((fun _ => (3 : ℝ)) 0) ((fun _ => (2 : ℝ)) 0) :=
  firstIntegral_eq (α := 2) (β := 1) (γ := 3) (δ := 1) (x := fun _ => 3) (y := fun _ => 2)
    (fun t _ => by convert hasDerivAt_const t (3 : ℝ) using 1; norm_num)
    (fun t _ => by convert hasDerivAt_const t (2 : ℝ) using 1; norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) ht

/-- The equilibrium `(γ / δ, α / β) = (1, 1)` minimizes `V` for unit parameters. -/
example : firstIntegral 1 1 1 1 1 1 ≤ firstIntegral 1 1 1 1 2 (1 / 2) := by
  simpa using firstIntegral_equilibrium_le (x := 2) (y := 1 / 2) one_pos one_pos one_pos one_pos
    two_pos (by norm_num)

/-- Equivalently, `2 ≤ 2 - log 2 + 1 / 2 - log (1 / 2)`, i.e. `0 ≤ 1 / 2`. -/
example : (2 : ℝ) ≤ firstIntegral 1 1 1 1 2 (1 / 2) := by
  have := firstIntegral_equilibrium_le (α := 1) (β := 1) (γ := 1) (δ := 1) (x := 2) (y := 1 / 2)
    one_pos one_pos one_pos one_pos two_pos (by norm_num)
  norm_num [firstIntegral] at this ⊢
  linarith

end MathlibExtTest.Biology.Dynamics.LotkaVolterra
