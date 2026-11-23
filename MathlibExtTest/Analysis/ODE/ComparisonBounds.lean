/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.ComparisonBounds
import Mathlib.Tactic

/-!
# Tests for the scalar comparison bounds

* `abs_le_of_decay` on `w(t) = e^{-2t}`, `a ≡ 2`, `g ≡ 0`, `λ = 1`: `|w t| ≤ e^{-t}`, a
  strict improvement on the trivial bound only because `a ≥ λ`;
* `abs_le_of_drift` on `d(t) = t`, `d' ≡ 1`, `H(t) = t`: the bound `|d t| ≤ |d 0| + H t` is
  attained with equality, so the drift constant cannot be lowered;
* `le_of_decay` with forcing `g ≡ 1` and `w ≡ 1`, `a ≡ 1`, `λ = 1`: the steady state `w ≡ G/λ`
  shows the `G/λ` term is needed.
-/

open Real Set

namespace MathlibExtTest.Analysis.ODE.ComparisonBounds

open MathlibExt.Analysis.ODE.ComparisonBounds

/-- Pure decay: `e^{-2t} ≤ e^{-t}` through `abs_le_of_decay`. -/
example {t : ℝ} (ht : 0 ≤ t) : |exp (-2 * t)| ≤ exp (-t) := by
  have := abs_le_of_decay (w := fun r ↦ exp (-2 * r)) (a := fun _ ↦ 2) (g := fun _ ↦ 0)
    (lam := 1) (G := 0) one_pos
    (fun r _ ↦ by
      have h := ((hasDerivAt_id' r).const_mul (-2)).exp
      convert h using 1; simp; ring)
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ by simp) ht
  simpa using this

/-- Drift with equality: `d(t) = t`, `H(t) = t`. -/
example {t : ℝ} (ht : 0 ≤ t) : |t| ≤ |(0 : ℝ)| + t :=
  abs_le_of_drift (d := id) (d' := fun _ ↦ 1) (H := id) (h := fun _ ↦ 1)
    (fun r _ ↦ hasDerivAt_id r) (fun r _ ↦ hasDerivAt_id r) rfl (fun _ hr ↦ hr)
    (fun _ _ _ ↦ le_rfl) (fun r hr hd ↦ by norm_num) ht

/-- Steady state `w ≡ 1` of `w' = -w + 1` meets the bound `|w 0| e^{-t} + G/λ`. -/
example {t : ℝ} (ht : 0 ≤ t) : (1 : ℝ) ≤ |1| * exp (-1 * t) + 1 / 1 :=
  le_of_decay (w := fun _ ↦ 1) (a := fun _ ↦ 1) (g := fun _ ↦ 1) (lam := 1) (G := 1) one_pos
    zero_le_one (fun r _ ↦ (hasDerivAt_const r (1 : ℝ)).congr_deriv (by ring))
    (fun _ _ ↦ le_rfl) (fun _ _ ↦ le_rfl) ht

end MathlibExtTest.Analysis.ODE.ComparisonBounds
