/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.IterateLipschitzNullFixedPoint

/-! # Tests for fixed points of maps with contracting iterates -/

open Filter MathlibExt.Analysis.Calculus.IterateLipschitzNullFixedPointWanted

-- The shift on pairs has Lipschitz constant one, and its square is constant.
-- The bound at index zero can be zero even though the zeroth iterate is the identity.
example : ∃ p : ℝ × ℝ, (p.2, (0 : ℝ)) = p := by
  let f : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.2, 0)
  let q : ℕ → ℝ := fun n ↦ if n = 1 then 1 else 0
  apply exists_fixedPoint_of_iterate_lipschitz_tendsto_zero _ f q
  · intro n
    simp [q, apply_ite]
  · rintro ⟨n, hn⟩ x y
    change dist (f^[n] x) (f^[n] y) ≤ q n * dist x y
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    cases k with
    | zero => simp [f, q, Prod.dist_eq]
    | succ k => simp [Function.iterate_succ_apply, f, q]
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 1] with n hn
    simp [q, hn]
