/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Averaging recursions with divergent gains

For gains `a t ∈ [0, 1]` whose sum diverges, the recursion
`x (t + 1) = (1 - a t) * x t + a t * z t` replaces `x t` by a convex combination of itself and
the input `z t`. If the inputs tend to `0`, so do the iterates, whatever the initial value `x 0`
(`MetaMathlibExt.tendsto_zero_of_averaging`). The same holds when the inputs are noise whose
weighted series `∑ t, a t * w t` converges
(`MetaMathlibExt.tendsto_zero_of_averaging_of_tendsto_sum`).

These are the deterministic steps of the noise-averaging lemma of stochastic approximation
(Tsitsiklis 1994, Lemma 1): its probabilistic part shows that the weighted noise series converges
almost surely, and the second result then gives convergence of the iterates to `0` along every
such path.

## Main results

* `MetaMathlibExt.tendsto_zero_of_averaging`: inputs tending to `0` give iterates tending to `0`.
* `MetaMathlibExt.tendsto_zero_of_averaging_of_tendsto_sum`: a convergent weighted noise series
  gives iterates tending to `0`.

## Implementation notes

For `ε > 0`, once `|z t| ≤ ε` the quantity `max (|x t| - ε) 0` is multiplied by at most `1 - a t`
at each step, and `∏ (1 - a t) ≤ exp (-∑ a t)`, which tends to `0`. For the second result,
`U t = W t - (S t - l)`, where `S t = ∑ s ∈ Finset.range t, a s * w s` and `l` is its limit,
follows the same recursion with inputs `l - S t`, which tend to `0`.

## References

* J. N. Tsitsiklis, *Asynchronous stochastic approximation and Q-learning*, Machine Learning 16
  (1994), 185–202, Lemma 1 (p. 190).
-/

@[expose] public section

open Filter Topology

namespace MetaMathlibExt

private theorem eventually_abs_le_two_mul_of_averaging {a z x : ℕ → ℝ}
    (ha : ∀ t, a t ∈ Set.Icc (0 : ℝ) 1)
    (hdiv : Tendsto (fun n => ∑ t ∈ Finset.range n, a t) atTop atTop)
    (hz : Tendsto z atTop (𝓝 0))
    (hx : ∀ t, x (t + 1) = (1 - a t) * x t + a t * z t)
    {e : ℝ} (he : 0 < e) : ∀ᶠ t in atTop, |x t| ≤ 2 * e := by
  have ha0 : ∀ t, 0 ≤ a t := fun t => (ha t).1
  have ha1 : ∀ t, a t ≤ 1 := fun t => (ha t).2
  have h1a : ∀ t, 0 ≤ 1 - a t := fun t => by linarith [ha1 t]
  have hzT : ∀ᶠ t in atTop, |z t| ≤ e := by
    have h := Metric.tendsto_nhds.mp hz e he
    filter_upwards [h] with t ht
    rw [Real.dist_eq, sub_zero] at ht
    exact le_of_lt ht
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hzT
  have hrec : ∀ t, T ≤ t → max (|x (t + 1)| - e) 0 ≤ (1 - a t) * max (|x t| - e) 0 := by
    intro t ht
    have hzt : |z t| ≤ e := hT t ht
    have hx1 : |x (t + 1)| ≤ (1 - a t) * |x t| + a t * e := by
      rw [hx t]
      have h1 : |(1 - a t) * x t + a t * z t| ≤ |(1 - a t) * x t| + |a t * z t| :=
        abs_add_le _ _
      rw [abs_mul, abs_mul, abs_of_nonneg (h1a t), abs_of_nonneg (ha0 t)] at h1
      have h2 : a t * |z t| ≤ a t * e := mul_le_mul_of_nonneg_left hzt (ha0 t)
      have h3 : (1 - a t) * |x t| + a t * |z t| ≤ (1 - a t) * |x t| + a t * e := by
        linarith [h2]
      exact h1.trans h3
    have hsub : |x (t + 1)| - e ≤ (1 - a t) * (|x t| - e) := by
      have h := sub_le_sub_right hx1 e
      rw [show (1 - a t) * |x t| + a t * e - e = (1 - a t) * (|x t| - e) from by ring] at h
      exact h
    have hle1 : |x (t + 1)| - e ≤ (1 - a t) * max (|x t| - e) 0 :=
      le_trans hsub (mul_le_mul_of_nonneg_left (le_max_left _ _) (h1a t))
    have hle0 : (0 : ℝ) ≤ (1 - a t) * max (|x t| - e) 0 :=
      mul_nonneg (h1a t) (le_max_right _ _)
    exact max_le hle1 hle0
  have hbound : ∀ n, max (|x (T + n)| - e) 0
      ≤ Real.exp (-((∑ s ∈ Finset.range (T + n), a s) - (∑ s ∈ Finset.range T, a s)))
        * max (|x T| - e) 0 := by
    intro n
    induction n with
    | zero =>
      rw [Nat.add_zero, sub_self, neg_zero, Real.exp_zero, one_mul]
    | succ n ih =>
      have hTle : T ≤ T + n := Nat.le_add_right T n
      have hidx : T + (n + 1) = (T + n) + 1 := by ring
      have hstep : max (|x ((T + n) + 1)| - e) 0
          ≤ (1 - a (T + n)) * max (|x (T + n)| - e) 0 :=
        hrec (T + n) hTle
      have h1a_exp : 1 - a (T + n) ≤ Real.exp (-a (T + n)) := by
        have h := Real.add_one_le_exp (-a (T + n))
        linarith
      have harg : (-((∑ s ∈ Finset.range (T + n), a s) + a (T + n)
          - (∑ s ∈ Finset.range T, a s)))
          = (-a (T + n) + -((∑ s ∈ Finset.range (T + n), a s)
            - (∑ s ∈ Finset.range T, a s))) := by
        ring
      have hfin : Real.exp (-a (T + n))
            * (Real.exp (-((∑ s ∈ Finset.range (T + n), a s)
              - (∑ s ∈ Finset.range T, a s))) * max (|x T| - e) 0)
          = Real.exp (-((∑ s ∈ Finset.range (T + n), a s) + a (T + n)
            - (∑ s ∈ Finset.range T, a s))) * max (|x T| - e) 0 := by
        rw [harg, Real.exp_add, mul_assoc]
      calc max (|x (T + (n + 1))| - e) 0
          = max (|x ((T + n) + 1)| - e) 0 := by rw [hidx]
        _ ≤ (1 - a (T + n)) * max (|x (T + n)| - e) 0 := hstep
        _ ≤ Real.exp (-a (T + n)) * max (|x (T + n)| - e) 0 :=
            mul_le_mul_of_nonneg_right h1a_exp (le_max_right _ _)
        _ ≤ Real.exp (-a (T + n)) * (Real.exp (-((∑ s ∈ Finset.range (T + n), a s)
              - (∑ s ∈ Finset.range T, a s))) * max (|x T| - e) 0) :=
            mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
        _ = Real.exp (-((∑ s ∈ Finset.range (T + n), a s) + a (T + n)
            - (∑ s ∈ Finset.range T, a s))) * max (|x T| - e) 0 := hfin
        _ = Real.exp (-((∑ s ∈ Finset.range (T + (n + 1)), a s)
            - (∑ s ∈ Finset.range T, a s))) * max (|x T| - e) 0 := by
            rw [hidx, Finset.sum_range_succ]
  have htail : Tendsto (fun t => (∑ s ∈ Finset.range t, a s) - (∑ s ∈ Finset.range T, a s))
      atTop atTop := by
    have h := Filter.tendsto_atTop_add_const_right atTop (-(∑ s ∈ Finset.range T, a s)) hdiv
    simpa [sub_eq_add_neg] using h
  have hexp0 : Tendsto (fun t => Real.exp (-((∑ s ∈ Finset.range t, a s)
      - (∑ s ∈ Finset.range T, a s)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp htail
  have hbound0 : Tendsto (fun t => Real.exp (-((∑ s ∈ Finset.range t, a s)
      - (∑ s ∈ Finset.range T, a s))) * max (|x T| - e) 0) atTop (𝓝 0) := by
    have h : Tendsto (fun t => Real.exp (-((∑ s ∈ Finset.range t, a s)
        - (∑ s ∈ Finset.range T, a s))) * max (|x T| - e) 0) atTop
        (𝓝 (0 * max (|x T| - e) 0)) :=
      hexp0.mul tendsto_const_nhds
    simpa using h
  have hy0 : Tendsto (fun t => max (|x t| - e) 0) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound0
    · filter_upwards with t
      exact le_max_right _ _
    · filter_upwards [eventually_ge_atTop T] with t ht
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
      exact hbound n
  have hev : ∀ᶠ t in atTop, max (|x t| - e) 0 < e := hy0.eventually (eventually_lt_nhds he)
  filter_upwards [hev] with t ht
  have hmax : |x t| - e ≤ max (|x t| - e) 0 := le_max_left _ _
  linarith [hmax, ht]

/-- **Averaging recursion.** Let `x (t + 1) = (1 - a t) * x t + a t * z t` with gains
`a t ∈ [0, 1]` whose partial sums tend to infinity. If the inputs `z t` tend to `0`, then so do
the iterates `x t`, for every initial value `x 0`. -/
theorem tendsto_zero_of_averaging {a z x : ℕ → ℝ} (ha : ∀ t, a t ∈ Set.Icc (0 : ℝ) 1)
    (hdiv : Tendsto (fun n => ∑ t ∈ Finset.range n, a t) atTop atTop)
    (hz : Tendsto z atTop (𝓝 0))
    (hx : ∀ t, x (t + 1) = (1 - a t) * x t + a t * z t) :
    Tendsto x atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h := eventually_abs_le_two_mul_of_averaging ha hdiv hz hx (show 0 < ε / 3 by linarith)
  filter_upwards [h] with t ht
  rw [Real.dist_eq, sub_zero]
  linarith [ht]

/-- **Averaging a convergent noise series.** Let `W (t + 1) = (1 - a t) * W t + a t * w t` with
gains `a t ∈ [0, 1]` whose partial sums tend to infinity. If the weighted noise series
`∑ t ∈ Finset.range n, a t * w t` converges to some `l`, then `W t` tends to `0`, for every
initial value `W 0`. -/
theorem tendsto_zero_of_averaging_of_tendsto_sum {a w W : ℕ → ℝ} {l : ℝ}
    (ha : ∀ t, a t ∈ Set.Icc (0 : ℝ) 1)
    (hdiv : Tendsto (fun n => ∑ t ∈ Finset.range n, a t) atTop atTop)
    (hS : Tendsto (fun n => ∑ t ∈ Finset.range n, a t * w t) atTop (𝓝 l))
    (hW : ∀ t, W (t + 1) = (1 - a t) * W t + a t * w t) :
    Tendsto W atTop (𝓝 0) := by
  have hS1 : ∀ t, (∑ u ∈ Finset.range (t + 1), a u * w u)
      = (∑ u ∈ Finset.range t, a u * w u) + a t * w t := by
    intro t
    rw [Finset.sum_range_succ]
  have hz : Tendsto (fun t => -((∑ u ∈ Finset.range t, a u * w u) - l)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => (∑ u ∈ Finset.range t, a u * w u) - l) atTop (𝓝 (l - l)) :=
      hS.sub_const l
    have h2 := h1.neg
    simpa using h2
  have hx : ∀ t, (fun t => W t - ((∑ u ∈ Finset.range t, a u * w u) - l)) (t + 1)
      = (1 - a t) * (fun t => W t - ((∑ u ∈ Finset.range t, a u * w u) - l)) t
        + a t * (fun t => -((∑ u ∈ Finset.range t, a u * w u) - l)) t := by
    intro t
    change W (t + 1) - ((∑ u ∈ Finset.range (t + 1), a u * w u) - l)
      = (1 - a t) * (W t - ((∑ u ∈ Finset.range t, a u * w u) - l))
        + a t * (-((∑ u ∈ Finset.range t, a u * w u) - l))
    rw [hW t, hS1 t]
    ring
  have hU := tendsto_zero_of_averaging (a := a)
      (z := fun t => -((∑ u ∈ Finset.range t, a u * w u) - l))
      (x := fun t => W t - ((∑ u ∈ Finset.range t, a u * w u) - l)) ha hdiv hz hx
  have hSl : Tendsto (fun t => (∑ u ∈ Finset.range t, a u * w u) - l) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => (∑ u ∈ Finset.range t, a u * w u) - l) atTop (𝓝 (l - l)) :=
      hS.sub_const l
    simpa using h1
  have hW0 := hU.add hSl
  simpa using hW0

end MetaMathlibExt
