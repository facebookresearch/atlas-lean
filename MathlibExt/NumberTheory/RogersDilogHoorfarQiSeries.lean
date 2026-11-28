/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import MathlibExt.Analysis.SpecialFunctions.RogersDilog

/-!
# The Hoorfar–Qi dilogarithm series

For positive integers `p` and `q` and reals `0 < θ, β < 1`, the Rogers dilogarithm series
in Theorem 1 of Sanford sums to two finite sums and a boundary term. Abel's five-term
relation produces two differences with shifts `q` and `p`, respectively. Their tails
converge by continuity of the Rogers dilogarithm on the closed unit interval. A zero
shift would make both sides vanish; the statement uses positive natural shifts.

## References

* Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
  INTEGERS 25 (2025), Article A52, pp. 1–15, Theorem 1 and equation (2).
* Abdolhossein Hoorfar and Feng Qi, *Sums of series of Rogers dilogarithm functions*,
  The Ramanujan Journal 18 (2009), pp. 231–238, as cited in Sanford's Theorem 1.
* `MathlibExt.Analysis.SpecialFunctions.RogersDilog` supplies Abel's relation and the Rogers
  dilogarithm API. The passage from finite sums to `HasSum` adapts the proof of
  `rogersDilog_sanford_symmetric_series` in `MathlibExt.NumberTheory.SanfordSymmetricSeries`.
-/

open Filter Real Set
open scoped Topology

namespace MetaMathlibExt

/-- **Hoorfar–Qi dilogarithm series.** Write $L(x) = \sum_{m \ge 1} x^m/m^2 +
\frac{1}{2} \log x \log(1 - x)$ for the Rogers dilogarithm on $[0, 1]$ (with $\log 0 = 0$). For
positive integers $p, q$ and real numbers $\theta, \beta$ with $0 < \theta < 1$ and
$0 < \beta < 1$,
$$
\sum_{n \ge 0} L\left(\frac{\beta(1 - \theta^p)(1 - \theta^q)\theta^n}
{(1 - \beta\theta^{n+p})(1 - \beta\theta^{n+q})}\right) =
\sum_{n=0}^{q-1} L\left(\frac{\beta(1 - \theta^p)\theta^n}{1 - \beta\theta^{n+p}}\right) +
\sum_{n=0}^{p-1} L\left(\frac{1 - \theta^q}{1 - \beta\theta^{n+q}}\right) - p\,L(1 - \theta^q).
$$

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 1, quoting Hoorfar and Qi (`integers-2025-A52-thm-1`). -/
public theorem rogersDilog_hoorfarQi_series {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {θ β : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    ∑' n : ℕ, L (β * (1 - θ ^ p) * (1 - θ ^ q) * θ ^ n /
        ((1 - β * θ ^ (n + p)) * (1 - β * θ ^ (n + q)))) =
      ∑ n ∈ Finset.range q, L (β * (1 - θ ^ p) * θ ^ n / (1 - β * θ ^ (n + p))) +
        ∑ n ∈ Finset.range p, L ((1 - θ ^ q) / (1 - β * θ ^ (n + q))) - p * L (1 - θ ^ q) := by
  intro R
  let a := θ ^ p
  let b := θ ^ q
  let z (n : ℕ) := β * θ ^ n
  let X (t : ℝ) := t * (1 - a) / (1 - t * a)
  let Y (t : ℝ) := (1 - b) / (1 - t * b)
  have ha : a ∈ Ioo (0 : ℝ) 1 := ⟨pow_pos hθ₀ _, pow_lt_one₀ hθ₀.le hθ₁ hp.ne'⟩
  have hb : b ∈ Ioo (0 : ℝ) 1 := ⟨pow_pos hθ₀ _, pow_lt_one₀ hθ₀.le hθ₁ hq.ne'⟩
  have hz (n : ℕ) : z n ∈ Ioo (0 : ℝ) 1 :=
    ⟨mul_pos hβ₀ (pow_pos hθ₀ _),
      (mul_le_of_le_one_right hβ₀.le (pow_le_one₀ hθ₀.le hθ₁.le)).trans_lt hβ₁⟩
  have hmul {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
      x * y ∈ Ioo (0 : ℝ) 1 := by
    simpa only [Ioo.coe_mul] using (((⟨x, hx⟩ : Ioo (0 : ℝ) 1) * ⟨y, hy⟩).2)
  have hXa {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : X t ∈ Ioo (0 : ℝ) 1 :=
    abel_five_term_arg_mem_Ioo ht ha
  have hYb {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : Y t ∈ Ioo (0 : ℝ) 1 := by
    have hd := sub_pos.mpr (hmul ht hb).2
    exact ⟨div_pos (sub_pos.mpr hb.2) hd,
      (div_lt_one hd).2 (sub_lt_sub_left (mul_lt_of_lt_one_left hb.1 ht.2) 1)⟩
  have hza (n : ℕ) : z n * a = z (n + p) := by simp [z, a, pow_add, mul_assoc]
  have hzb (n : ℕ) : z n * b = z (n + q) := by simp [z, b, pow_add, mul_assoc]
  -- The two new five-term arguments replace `t` by `t * b` and `t * a`.
  have hstep {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      X t * (1 - Y t) / (1 - X t * Y t) = X (t * b) ∧
        Y t * (1 - X t) / (1 - Y t * X t) = Y (t * a) := by
    have h1 := (sub_pos.mpr (hmul ht ha).2).ne'
    have h2 := (sub_pos.mpr (hmul ht hb).2).ne'
    have h3 := (sub_pos.mpr (hmul (hmul ht ha) hb).2).ne'
    have h4 := (sub_pos.mpr (hmul (hmul ht hb) ha).2).ne'
    have ht' := (sub_pos.mpr ht.2).ne'
    have hcomp : 1 - X t * Y t = (1 - t) * (1 - t * a * b) / ((1 - t * a) * (1 - t * b)) := by
      dsimp only [X, Y]
      field_simp [h1, h2]
      ring
    constructor
    · rw [hcomp]
      dsimp only [X, Y]
      field_simp [h1, h2, h3, h4, ht']
      ring
    · have hXcomp : 1 - X t = (1 - t) / (1 - t * a) := by
        dsimp only [X]
        field_simp [h1]
        ring
      rw [mul_comm (Y t) (X t), hcomp, hXcomp]
      dsimp only [Y]
      rw [div_mul_div_comm, mul_comm (1 - t * b) (1 - t * a),
        div_div_div_cancel_right₀ (mul_ne_zero h1 h2), mul_comm (1 - t) (1 - t * a * b)]
      exact mul_div_mul_right _ _ ht'
  let U (n : ℕ) := rogersDilog (X (z n))
  let V (n : ℕ) := rogersDilog (Y (z n))
  let S (n : ℕ) := rogersDilog (X (z n) * Y (z n))
  have hterm (n : ℕ) : S n = (U n - U (n + q)) + (V n - V (n + p)) := by
    have h := rogersDilog_five_term (hXa (hz n)) (hYb (hz n))
    rw [(hstep (hz n)).1, (hstep (hz n)).2, hzb, hza] at h
    change U n + V n = S n + U (n + q) + V (n + p) at h
    linarith
  have telescope (f : ℕ → ℝ) (N k : ℕ) :
      (∑ n ∈ Finset.range N, (f n - f (n + k))) =
        (∑ n ∈ Finset.range k, f n) - ∑ n ∈ Finset.range k, f (N + n) := by
    rw [Finset.sum_sub_distrib]
    have h := Finset.sum_range_add f k N
    rw [Nat.add_comm k N, Finset.sum_range_add f N k] at h
    simp only [Nat.add_comm k] at h
    linarith
  have hpartial (N : ℕ) : ∑ n ∈ Finset.range N, S n =
      ((∑ n ∈ Finset.range q, U n) - ∑ n ∈ Finset.range q, U (N + n)) +
        ((∑ n ∈ Finset.range p, V n) - ∑ n ∈ Finset.range p, V (N + n)) := by
    simp only [hterm, Finset.sum_add_distrib, telescope]
  have hzlim : Tendsto z atTop (𝓝 0) := by
    simpa only [z, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ₀.le hθ₁).const_mul β
  have hXlim : Tendsto (fun n => X (z n)) atTop (𝓝 0) := by
    simpa only [X, Pi.div_def, zero_mul, sub_zero, div_one] using
      (hzlim.mul_const (1 - a)).div ((hzlim.mul_const a).const_sub 1) (by norm_num)
  have hYlim : Tendsto (fun n => Y (z n)) atTop (𝓝 (1 - b)) := by
    simpa only [Y, Pi.div_def, zero_mul, sub_zero, div_one] using
      (tendsto_const_nhds (x := 1 - b)).div ((hzlim.mul_const b).const_sub 1) (by norm_num)
  have hUlim : Tendsto U atTop (𝓝 0) := by
    rw [← rogersDilog_zero]
    exact (continuousOn_rogersDilog 0 (by simp)).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hXlim
        (Eventually.of_forall fun n => Ioo_subset_Icc_self (hXa (hz n))))
  have hVlim : Tendsto V atTop (𝓝 (rogersDilog (1 - b))) :=
    (continuousOn_rogersDilog (1 - b) ⟨sub_nonneg.mpr hb.2.le, sub_le_self _ hb.1.le⟩).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hYlim
        (Eventually.of_forall fun n => Ioo_subset_Icc_self (hYb (hz n))))
  have hUtail := tendsto_finsetSum (Finset.range q) fun i _ =>
    hUlim.comp (tendsto_add_atTop_nat i)
  have hVtail := tendsto_finsetSum (Finset.range p) fun i _ =>
    hVlim.comp (tendsto_add_atTop_nat i)
  have hS_nonneg (n : ℕ) : 0 ≤ S n := rogersDilog_nonneg (hmul (hXa (hz n)) (hYb (hz n)))
  have hsum : HasSum S ((∑ n ∈ Finset.range q, U n) +
      (∑ n ∈ Finset.range p, V n) - p * rogersDilog (1 - b)) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg hS_nonneg _).2
    simp only [hpartial]
    simpa only [Function.comp_apply, Finset.sum_const_zero, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, sub_zero, add_sub_assoc] using
      ((hUtail.const_sub (∑ n ∈ Finset.range q, U n)).add
        (hVtail.const_sub (∑ n ∈ Finset.range p, V n)))
  have hX (n : ℕ) : X (z n) = β * (1 - θ ^ p) * θ ^ n / (1 - β * θ ^ (n + p)) := by
    change z n * (1 - a) / (1 - z n * a) = _
    rw [hza]
    simp only [z, a]
    ring
  have hY (n : ℕ) : Y (z n) = (1 - θ ^ q) / (1 - β * θ ^ (n + q)) := by
    change (1 - b) / (1 - z n * b) = _
    rw [hzb]
  have hXY (n : ℕ) : X (z n) * Y (z n) = β * (1 - θ ^ p) * (1 - θ ^ q) * θ ^ n /
      ((1 - β * θ ^ (n + p)) * (1 - β * θ ^ (n + q))) := by
    rw [hX, hY, div_mul_div_comm]
    ring
  have h := hsum.tsum_eq
  simp only [S, hXY] at h
  simpa only [U, V, hX, hY, b, R, rogersDilog_eq_tsum_add_log_mul_log] using h

end MetaMathlibExt
