/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`PartitionsJensen/Target.lean`
(ChironTheCentaur/rh-lab-partitions-jensen, commit 57beb8dbff7b84e125931fe2e53080f325f4f108):
Copyright (c) 2026 Sky (GitHub: ChironTheCentaur). All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Sky (GitHub: ChironTheCentaur)
-/

module

public import MathlibExt.Combinatorics.Enumerative.ColoredPartitionsJensen.Count
public import MathlibExt.Combinatorics.Enumerative.ColoredPartitionsJensen.Assembly

/-!
# Eventual hyperbolicity of Jensen polynomials for colored partitions

`MetaMathlibExt.eventually_jensen_hyperbolic_coloredPartitions`: for `r ≥ 1` and every `d`, the
Jensen polynomials of degree `d` of the number `C_r(n)` of `r`-colored partitions are hyperbolic for
all large shifts `n` (Bal, Haraldson, Males and Thompson, *Jensen Polynomials Associated with
Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025), Article A36,
Theorem 3, part 1).

Proof:

* `ColoredPartitionsJensen.coef_eq_cnt`: the `n`-th Taylor coefficient of `F(q)^r`,
  `F(q) = ∏ (1 − qᵏ)⁻¹`, is the count `C_r(n)` of the statement;
* `ColoredPartitionsJensen.coef_re_asymp` (circle method):
  `C_r(n) = c'_r · I((r+1)/2, κ_r √(n − r/24)) · (1 + ρ(n))`, `|ρ(n)| ≤ e^{−c√n}` eventually, where
  `I(a, z) = ∫_{−1}^{1} (1 − t²)^a e^{zt} dt`;
* hence `log C_r(n) = log c'_r + coloredModel r n + O(e^{−c√n})` (`log_cnt_bound`), and
  `e^{−c√n} = o(n^{(1/2 − 2)d/2})` (`exp_neg_sqrt_isLittleO`);
* `ColoredPartitionsJensen.eventually_card_roots_of_coloredModel`: the model is in the smooth class
  `S_{1/2}` and strictly concave, so forward differences give the log-ratio expansion of Griffin,
  Ono, Rolen and Zagier, and `eventually_jensen_hyperbolic_of_log_ratio_expansion` concludes.
-/

open Filter Asymptotics Polynomial Topology

namespace MetaMathlibExt

namespace ColoredPartitionsJensen

@[expose] public section

/- For `r ≥ 1` there is `c > 0` such that, eventually,
`C_r(n) = c'_r · I((r + 1)/2, κ_r √(n − r/24)) · (1 + ρ)` for some `|ρ| ≤ e^{−c√n}`. -/
private theorem cnt_asymp (r : ℕ) (hr : 1 ≤ r) : ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ ρ : ℝ,
    |ρ| ≤ Real.exp (-(c * √n)) ∧
      (cnt r n : ℝ) = cPrime r * besselInt (((r : ℝ) + 1) / 2)
        (coloredKappa r * √((n : ℝ) - r / 24)) * (1 + ρ) := by
  obtain ⟨c, hc, h⟩ := coef_re_asymp r hr
  refine ⟨c, hc, h.mono fun n ⟨ρ, h1, h2⟩ => ⟨ρ, h1, ?_⟩⟩
  rw [← h2, coef_eq_cnt]
  simp

lemma tendsto_mul_sqrt_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => c * √(n : ℝ)) atTop atTop :=
  (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc

/- For `r ≥ 1` there is `c > 0` such that, eventually, `C_r(n) > 0` and
`|log C_r(n) − (log c'_r + coloredModel r n)| ≤ 2 e^{−c√n}`. -/
private theorem log_cnt_bound {r : ℕ} (hr : 1 ≤ r) : ∃ c > 0, ∀ᶠ n : ℕ in atTop, 0 < (cnt r n : ℝ) ∧
    |Real.log (cnt r n : ℝ) - (Real.log (cPrime r) + coloredModel r n)| ≤
      2 * Real.exp (-(c * √n)) := by
  obtain ⟨c, hc, h⟩ := cnt_asymp r hr
  have hsmall : ∀ᶠ n : ℕ in atTop, Real.exp (-(c * √n)) < 1 / 2 := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_mul_sqrt_atTop hc)
    exact (tendsto_order.1 this).2 (1 / 2) (by norm_num)
  refine ⟨c, hc, ?_⟩
  filter_upwards [h, hsmall] with n ⟨ρ, hρ, hn⟩ hs
  have hρ' : 1 / 2 ≤ 1 + ρ := by linarith [neg_abs_le ρ]
  have hP := cPrime_pos hr
  have hB := besselInt_pos (a := ((r : ℝ) + 1) / 2) (by positivity)
    (coloredKappa r * √((n : ℝ) - r / 24))
  have h1 : 0 < 1 + ρ := by linarith
  refine ⟨hn ▸ by positivity, ?_⟩
  have hM : coloredModel r n = Real.log (besselInt (((r : ℝ) + 1) / 2)
      (coloredKappa r * √((n : ℝ) - r / 24))) := rfl
  rw [hn, hM, Real.log_mul (by positivity) h1.ne', Real.log_mul hP.ne' hB.ne']
  have := abs_log_le_two_mul hρ'
  rw [add_sub_cancel_left] at this
  calc |Real.log (cPrime r) + Real.log (besselInt (((r : ℝ) + 1) / 2)
          (coloredKappa r * √((n : ℝ) - r / 24))) + Real.log (1 + ρ) -
        (Real.log (cPrime r) + Real.log (besselInt (((r : ℝ) + 1) / 2)
          (coloredKappa r * √((n : ℝ) - r / 24))))| = |Real.log (1 + ρ)| := by ring_nf
    _ ≤ 2 * |ρ| := this
    _ ≤ 2 * Real.exp (-(c * √n)) := by linarith

/- For `c > 0`: `e^{−c√n} = o(n^e)` for every real `e`. -/
private theorem exp_neg_sqrt_isLittleO {c : ℝ} (hc : 0 < c) (e : ℝ) :
    (fun n : ℕ => Real.exp (-(c * √(n : ℝ)))) =o[atTop] fun n : ℕ => (n : ℝ) ^ e := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hc (2 * e)).comp_tendsto
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine h.congr' (Eventually.of_forall fun n => by simp [Function.comp_def, neg_mul])
    (Eventually.of_forall fun n => ?_)
  simp only [Function.comp_apply]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
  ring_nf

end

end ColoredPartitionsJensen

open ColoredPartitionsJensen in
/-- **Eventual hyperbolicity for colored partitions.** Let $r \ge 1$ and $d \ge 1$ be integers. For
$m \in \mathbb{N}$ let
$$
C_r(m) = \sum_{m_1 + \dots + m_r = m} p(m_1) \cdots p(m_r)
$$
be the number of $r$-colored partitions of $m$, where the sum runs over all $r$-tuples of natural
numbers with sum $m$ and $p$ is the partition function. Then for all sufficiently large $n$ the
Jensen polynomial $J^{d,n}(X) = \sum_{j=0}^{d} \binom{d}{j} C_r(n + j) X^j$ is hyperbolic: the
number of its real roots, counted with multiplicity, equals its degree.

In the source, $C_r(n)$ is the coefficient of $q^{tn}$ in $1/(q^t; q^t)_\infty^r$ for any
$t \ge 1$; the source also proves a Hermite-limit statement and higher order Turán inequalities,
which are not part of this statement.

Source: Jashan Bal, Fern Haraldson, Joshua Males and Ian Thompson, *Jensen Polynomials Associated
with Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025),
Article A36, Theorem 3, part 1 (`integers-2025-A36-thm-3`). -/
public theorem eventually_jensen_hyperbolic_coloredPartitions {r : ℕ} (hr : 1 ≤ r)
    {d : ℕ} (hd : 1 ≤ d) :
    ∀ᶠ n in atTop,
      (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) *
          ((∑ x ∈ Finset.Nat.antidiagonalTuple r (n + j),
            ∏ i, Fintype.card (Nat.Partition (x i)) : ℕ) : ℝ)) * X ^ j).roots.card =
        (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) *
          ((∑ x ∈ Finset.Nat.antidiagonalTuple r (n + j),
            ∏ i, Fintype.card (Nat.Partition (x i)) : ℕ) : ℝ)) * X ^ j).natDegree := by
  obtain ⟨c, hc, h⟩ := log_cnt_bound hr
  have hε : (fun n : ℕ => Real.log (cnt r n : ℝ) - (Real.log (cPrime r) + coloredModel r n))
      =o[atTop] fun n : ℕ => (n : ℝ) ^ ((1 / 2 - 2 : ℝ) * d / 2) := by
    refine IsBigO.trans_isLittleO (g := fun n : ℕ => Real.exp (-(c * √(n : ℝ)))) ?_
      (exp_neg_sqrt_isLittleO hc _)
    refine IsBigO.of_bound 2 (h.mono fun n hn => ?_)
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hn.2
  exact eventually_card_roots_of_coloredModel hr (α := fun n => (cnt r n : ℝ)) (d := d) hd
    (h.mono fun n hn => hn.1) hε

end MetaMathlibExt
