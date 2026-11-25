/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Group.ContinuousDiv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Kronecker's lemma

If `b n` is a nondecreasing sequence of reals tending to `+∞` and the series `∑ x k` converges,
then `(∑_{k < n} b k * x k) / b n → 0`. With `b k = (k + 1)²` this is the step that turns the
almost-sure convergence of a martingale series into a strong law of large numbers.

## Main results

* `MetaMathlibExt.tendsto_sum_range_mul_div_of_tendsto`: Kronecker's lemma, by summation by parts
  and Cesàro's lemma for the weights `b (k + 1) - b k`.
* `MetaMathlibExt.tendsto_sum_range_add_one_sq_mul_div_of_tendsto`: the case `b k = (k + 1)²`.

## References

* D. Williams, *Probability with Martingales*, Cambridge University Press (1991), §12.7.
-/

@[expose] public section

namespace MetaMathlibExt

open Filter Finset Topology

/-- **Kronecker's lemma.** Let $(b_n)_{n \ge 0}$ be a nondecreasing sequence of real numbers with
$b_n \to +\infty$, and let $(x_k)_{k \ge 0}$ be a real sequence whose series $\sum_k x_k$
converges. Then $\frac{1}{b_n} \sum_{k < n} b_k x_k \to 0$ as $n \to \infty$.

Proof: with $S_n = \sum_{k < n} x_k \to s$, summation by parts gives
$\sum_{k < n} b_k x_k = b_n (S_n - s) + s\, b_0 - \sum_{k < n} (b_{k+1} - b_k)(S_{k+1} - s)$, and
the last sum is $o(b_n)$ because its nonnegative weights add up to $b_n - b_0$ and
$S_{k+1} - s \to 0$ (Cesàro's lemma).

Source: D. Williams, *Probability with Martingales*, Cambridge University Press (1991), §12.7,
Kronecker's Lemma, stated there for weights $0 < b_n \uparrow \infty$ and the series
$\sum_k x_k / b_k$: here $x_k$ plays the role of Williams's $x_k / b_k$, and the weights need not
be positive.
-/
theorem tendsto_sum_range_mul_div_of_tendsto {b x : ℕ → ℝ} {s : ℝ} (hb_mono : Monotone b)
    (hb_unbounded : Tendsto b atTop atTop)
    (hx : Tendsto (fun n => ∑ k ∈ range n, x k) atTop (𝓝 s)) :
    Tendsto (fun n => (∑ k ∈ range n, b k * x k) / b n) atTop (𝓝 0) := by
  set S : ℕ → ℝ := fun n => ∑ k ∈ range n, x k with hS
  set u : ℕ → ℝ := fun k => S (k + 1) - s with hu
  have hS1 : ∀ n, S (n + 1) = S n + x n := fun n => sum_range_succ _ _
  -- summation by parts
  have habel : ∀ n, ∑ k ∈ range n, b k * x k =
      b n * (S n - s) + s * b 0 - ∑ k ∈ range n, (b (k + 1) - b k) * u k := by
    intro n
    induction n with
    | zero => simp [hS]; ring
    | succ n ih =>
      rw [sum_range_succ, ih, sum_range_succ, hS1]
      simp only [hu, hS1]
      ring
  have hd : ∀ k, 0 ≤ b (k + 1) - b k := fun k => sub_nonneg.2 (hb_mono k.le_succ)
  have hu0 : Tendsto u atTop (𝓝 0) := by
    have := (hx.comp (tendsto_add_atTop_nat 1)).sub_const s
    rw [sub_self] at this
    exact this
  -- Cesàro's lemma for the weights `b (k + 1) - b k`
  have hcesaro : Tendsto (fun n => (∑ k ∈ range n, (b (k + 1) - b k) * u k) / b n) atTop
      (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hu0 (ε / 2) (by positivity)
    set C := ∑ k ∈ range N, (b (k + 1) - b k) * |u k| - ε / 2 * b N with hC
    obtain ⟨N', hN'⟩ := eventually_atTop.1
      (hb_unbounded.eventually_gt_atTop (max 0 (2 * |C| / ε)))
    refine ⟨max N N', fun n hn => ?_⟩
    have hnN : N ≤ n := le_of_max_le_left hn
    have hbn : max 0 (2 * |C| / ε) < b n := hN' n (le_of_max_le_right hn)
    have hbn0 : 0 < b n := lt_of_le_of_lt (le_max_left _ _) hbn
    have hC2 : 2 * |C| < b n * ε := by
      have := lt_of_le_of_lt (le_max_right _ _) hbn
      rwa [div_lt_iff₀ hε] at this
    have h1 : |∑ k ∈ range N, (b (k + 1) - b k) * u k| ≤
        ∑ k ∈ range N, (b (k + 1) - b k) * |u k| :=
      (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun k _ => by
        rw [abs_mul, abs_of_nonneg (hd k)]))
    have h2 : |∑ k ∈ Ico N n, (b (k + 1) - b k) * u k| ≤ ε / 2 * (b n - b N) := by
      calc |∑ k ∈ Ico N n, (b (k + 1) - b k) * u k|
          ≤ ∑ k ∈ Ico N n, (b (k + 1) - b k) * (ε / 2) :=
            (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => by
              rw [abs_mul, abs_of_nonneg (hd k)]
              refine mul_le_mul_of_nonneg_left ?_ (hd k)
              have := hN k (mem_Ico.1 hk).1
              rw [Real.dist_eq, sub_zero] at this
              exact this.le)
        _ = ε / 2 * (b n - b N) := by
            rw [← sum_mul, sum_Ico_eq_sub _ hnN, sum_range_sub, sum_range_sub]
            ring
    have h3 : |∑ k ∈ range n, (b (k + 1) - b k) * u k| ≤ C + ε / 2 * b n := by
      rw [← sum_range_add_sum_Ico _ hnN]
      have := abs_add_le (∑ k ∈ range N, (b (k + 1) - b k) * u k)
        (∑ k ∈ Ico N n, (b (k + 1) - b k) * u k)
      rw [hC]
      linarith
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hbn0, div_lt_iff₀ hbn0]
    nlinarith [le_abs_self C]
  have hS0 : Tendsto (fun n => S n - s) atTop (𝓝 0) := by
    have := hx.sub_const s
    rwa [sub_self] at this
  have hb0 : Tendsto (fun n => s * b 0 / b n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hb_unbounded
  have heq : (fun n => (S n - s) + s * b 0 / b n -
      (∑ k ∈ range n, (b (k + 1) - b k) * u k) / b n) =ᶠ[atTop]
      fun n => (∑ k ∈ range n, b k * x k) / b n :=
    (hb_unbounded.eventually_gt_atTop 0).mono fun n hn => by
      dsimp only
      rw [habel]
      field_simp
  have := (hS0.add hb0).sub hcesaro
  rw [add_zero, sub_zero] at this
  exact this.congr' heq

theorem tendsto_sum_range_add_one_sq_mul_div_of_tendsto {x : ℕ → ℝ} {s : ℝ}
    (hx : Tendsto (fun n => ∑ k ∈ range n, x k) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ => (∑ k ∈ range n, ((k : ℝ) + 1) ^ 2 * x k) / ((n : ℝ) + 1) ^ 2) atTop
      (𝓝 0) :=
  tendsto_sum_range_mul_div_of_tendsto (b := fun k : ℕ => ((k : ℝ) + 1) ^ 2)
    (fun a c hac => by
      have : (a : ℝ) ≤ c := by exact_mod_cast hac
      dsimp only
      gcongr)
    ((tendsto_pow_atTop two_ne_zero).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)) hx

end MetaMathlibExt
