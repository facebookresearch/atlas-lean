/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.FisherKPPExistence

@[expose] public section

open Real Filter Topology
open MathlibExt.Biology.Dynamics.FisherKPP

namespace MathlibExtTest.Biology.Dynamics.FisherKPPExistence

/-! ### Minimal-speed boundary -/

/-- The critical speed for `D = r = 1` is `c = 2`, and a strictly decreasing front exists
there. -/
example : ∃ U U' : ℝ → ℝ, IsFront 1 1 2 U U' ∧ StrictAnti U := by
  simpa using exists_isFront_two_mul_sqrt (D := 1) (r := 1) one_pos one_pos

/-- The critical speed through the general theorem, with `D = 4`, `r = 1`: `2 √(1 · 4) = 4`. -/
example : ∃ U U' : ℝ → ℝ, IsFront 4 1 4 U U' ∧ StrictAnti U :=
  exists_isFront_of_le (by norm_num) one_pos (by
    rw [show (1 : ℝ) * 4 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num)

/-- Squared form exactly at the boundary: `4 r D = c²` for `D = r = 1`, `c = 2`. -/
example : ∃ U U' : ℝ → ℝ, IsFront 1 1 2 U U' ∧ StrictAnti U :=
  exists_isFront_of_sq_le one_pos one_pos (by norm_num) (by norm_num)

/-! ### Supercritical speeds -/

/-- A supercritical speed `c = 3 > 2` for `D = r = 1`. -/
example : ∃ U U' : ℝ → ℝ, IsFront 1 1 3 U U' ∧ StrictAnti U :=
  exists_isFront_of_sq_le one_pos one_pos (by norm_num) (by norm_num)

/-- Anisotropic parameters: `D = 1/2`, `r = 2`, `c = 2` is critical (`4 r D = 4 = c²`). -/
example : ∃ U U' : ℝ → ℝ, IsFront (1 / 2) 2 2 U U' ∧ StrictAnti U :=
  exists_isFront_of_sq_le (by norm_num) two_pos (by norm_num) (by norm_num)

/-! ### Non-vacuity of the conclusion -/

/-- The produced front is a genuine transition: it is strictly between the equilibria, decreases,
and connects `1` at `-∞` to `0` at `+∞`. -/
example : ∃ U : ℝ → ℝ, 0 < U 0 ∧ U 1 < U 0 ∧ U 0 < 1 ∧ Tendsto U atBot (𝓝 1) ∧
    Tendsto U atTop (𝓝 0) := by
  obtain ⟨U, U', ⟨-, hb, h1, h0⟩, hanti⟩ :=
    exists_isFront_of_sq_le (D := 1) (r := 1) (c := 2) one_pos one_pos (by norm_num)
      (by norm_num)
  exact ⟨U, (hb 0).1, hanti one_pos, (hb 0).2, h1, h0⟩

/-- `c = 2` is the minimal nonnegative front speed for `D = r = 1`: a front exists at `2`, and
none exists at any `0 ≤ c < 2`. -/
example : (∃ U U' : ℝ → ℝ, IsFront 1 1 2 U U' ∧ StrictAnti U) ∧
    ∀ c : ℝ, 0 ≤ c → c < 2 → ∀ U U' : ℝ → ℝ, ¬ IsFront 1 1 c U U' :=
  ⟨exists_isFront_of_sq_le one_pos one_pos (by norm_num) (by norm_num),
    fun c hc0 hc2 _ _ => not_isFront_of_sq_lt one_pos one_pos (by nlinarith)⟩

end MathlibExtTest.Biology.Dynamics.FisherKPPExistence
