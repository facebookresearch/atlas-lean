/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.MirrorProxSaddle
import Mathlib.Analysis.Convex.Mul

open Finset MathlibExt.Analysis.Convex.MirrorDescent

namespace MathlibExt.Analysis.Convex.MirrorProx

/-- The linear form `(u₁, u₂) ↦ a u₁ + b u₂` on `ℝ × ℝ`. -/
noncomputable def lf (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem lf_apply (a b : ℝ) (u : ℝ × ℝ) : lf a b u = a * u.1 + b * u.2 := by
  simp [lf]

theorem norm_lf_le (a b : ℝ) : ‖lf a b‖ ≤ |a| + |b| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  rw [lf_apply, Real.norm_eq_abs, add_mul]
  calc |a * u.1 + b * u.2| ≤ |a| * |u.1| + |b| * |u.2| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |a| * ‖u‖ + |b| * ‖u‖ := by
        gcongr
        · exact (Real.norm_eq_abs u.1).symm.le.trans (norm_fst_le u)
        · exact (Real.norm_eq_abs u.2).symm.le.trans (norm_snd_le u)

-- Extragradient on the saddle function `f(x, y) = x² - y²` over `ℝ × ℝ` (saddle point `(0, 0)`),
-- with `F(x, y) = (2x, 2y)`, which is `4`-Lipschitz for the max norm, the Euclidean setup
-- `ω = (x² + y²)/2` (`1`-strongly convex for the max norm) and `γ = 1/4`: from `z₀ = (1, 1)`,
-- `w_t = z_t / 2` and `z_{t+1} = 3 z_t / 4`, and the saddle gap of the averages is controlled.
example (N : ℕ) (hN : 0 < N) (x y : ℝ) :
    (fun p : ℝ × ℝ => p.1 ^ 2 - p.2 ^ 2)
        (((N : ℝ)⁻¹ • ∑ t ∈ range N, ((1 / 2 : ℝ) * (3 / 4) ^ t, (1 / 2 : ℝ) * (3 / 4) ^ t)).1, y) -
      (fun p : ℝ × ℝ => p.1 ^ 2 - p.2 ^ 2)
        (x, ((N : ℝ)⁻¹ • ∑ t ∈ range N, ((1 / 2 : ℝ) * (3 / 4) ^ t, (1 / 2 : ℝ) * (3 / 4) ^ t)).2) ≤
      bregman (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) / 2) (fun p => lf p.1 p.2)
        ((3 / 4) ^ 0, (3 / 4) ^ 0) (x, y) / ((1 / 4) * N) := by
  refine mirror_prox_saddle_le (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) / 2) (fun p => lf p.1 p.2)
    (γ := 1 / 4) (L := 4) (f := fun p : ℝ × ℝ => p.1 ^ 2 - p.2 ^ 2) (x := x) (y := y) one_pos
    (by norm_num) (by norm_num) (X := Set.univ) (Y := Set.univ)
    (fun p _ q _ => ?_) (fun yy _ => ?_) (fun xx _ => ?_) (fun p => lf (2 * p.1) (2 * p.2))
    (fun p => (2 * p.1) • ContinuousLinearMap.id ℝ ℝ)
    (fun p => (-2 * p.2) • ContinuousLinearMap.id ℝ ℝ) (fun p q => ?_) (fun p _ x' _ => ?_)
    (fun p _ y' _ => ?_) (fun a _ b _ => ?_) (z := fun t => ((3 / 4) ^ t, (3 / 4) ^ t))
    (w := fun t => ((1 / 2) * (3 / 4) ^ t, (1 / 2) * (3 / 4) ^ t)) (fun _ => ⟨trivial, trivial⟩)
    (fun _ => ⟨trivial, trivial⟩) (fun t u _ => ?_) (fun t u _ => ?_) hN trivial trivial
  · -- strong convexity for the max norm
    simp only [bregman, lf_apply, Prod.fst_sub, Prod.snd_sub]
    have h1 : ‖q - p‖ ^ 2 ≤ (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      rcases le_total |(q - p).1| |(q - p).2| with h | h
      · rw [max_eq_right h, sq_abs]; simp only [Prod.snd_sub]; nlinarith [sq_nonneg (q.1 - p.1)]
      · rw [max_eq_left h, sq_abs]; simp only [Prod.fst_sub]; nlinarith [sq_nonneg (q.2 - p.2)]
    nlinarith
  · have e : (fun x : ℝ => (x, yy).1 ^ 2 - (x, yy).2 ^ 2) = fun x => x ^ 2 + -(yy ^ 2) := by
      funext x; simp only; ring
    rw [e]
    exact (Even.convexOn_pow even_two).add_const _
  · have e : (fun y : ℝ => (xx, y).1 ^ 2 - (xx, y).2 ^ 2) = fun y => -(y ^ 2) + xx ^ 2 := by
      funext y; simp only; ring
    rw [e]
    exact (Even.convexOn_pow even_two).neg.add_const _
  · simp [lf_apply]
  · simp; nlinarith [sq_nonneg (x' - p.1)]
  · simp; nlinarith [sq_nonneg (y' - p.2)]
  · have : lf (2 * a.1) (2 * a.2) - lf (2 * b.1) (2 * b.2) =
        lf (2 * (a - b).1) (2 * (a - b).2) := by
      ext <;> simp [lf] <;> ring
    rw [this]
    refine (norm_lf_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_two, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    nlinarith [norm_fst_le (a - b), norm_snd_le (a - b)]
  · simp [lf_apply]; ring_nf; exact le_rfl
  · simp [lf_apply, pow_succ]; ring_nf; exact le_rfl

end MathlibExt.Analysis.Convex.MirrorProx
