/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

@[expose] public section

/-!
# Lambert series from the Journal of Integer Sequences

Sources:

* Ž. Tomovski and S. Gerhold, *Mathieu-Fibonacci Series*, Journal of Integer Sequences 25
  (2022),
  [`gerhold6.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL25/Gerhold/gerhold6.tex).
* C. Vignat and M. Milgram, *Curious Multisection Identities by Index Factorization*,
  Journal of Integer Sequences 27 (2024),
  [`milgram5.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL27/Milgram/milgram5.tex).

All series are indexed by `k : ℕ`, with the papers' index `n = k + 1`.

For the power-weighted series with integer $\mu\ge1$, a polynomial times a geometric sequence
bounds the summands uniformly on each closed disk of radius $0<r<1$. The relation between
$g_\mu(q)$, $f_\mu(q)$, and $f_\mu(q^2)$ for $|q|<1$ comes from decomposing the denominator
$1-q^{2n}=(1-q^n)(1+q^n)$.

## References

* Živorad Tomovski and Stefan Gerhold, *Mathieu-Fibonacci Series*, Journal of Integer
  Sequences 25 (2022), Article 22.6.3, pp. 1–15, Example 1 and equation (9).
* Christophe Vignat and Michael Milgram, *Curious Multisection Identities by Index Factorization*,
  Journal of Integer Sequences 27 (2024), Article 24.5.5, pp. 1–37, Corollaries 16 and 17,
  equations (108) and (119), for the definitions of the weighted Lambert series.
-/

/-- **Lambert series summand.** For a complex number $q$ with $|q| < 1$ and a natural number $k$,
the $k$-th summand of the basic Lambert series is $q^{k+1} / (1 - q^{k+1})$, that is, the term
$q^n / (1 - q^n)$ with $n = k + 1$. -/
public noncomputable def lambertSeriesSummand (q : {q : ℂ // ‖q‖ < 1}) (k : ℕ) : ℂ :=
  (q : ℂ) ^ (k + 1) / (1 - (q : ℂ) ^ (k + 1))

/-- **Lambert series.** For a complex number $q$ with $|q| < 1$, the basic Lambert series is
$L(q) = \sum_{n \ge 1} q^n / (1 - q^n)$. -/
public noncomputable def lambertSeries (q : {q : ℂ // ‖q‖ < 1}) : ℂ :=
  ∑' k, lambertSeriesSummand q k

/-- **Terms of the weighted Lambert series $f$.** For a complex number $q$ with $|q| < 1$ and a
natural number $k$, the term of index $k$ is $n q^n / (1 - q^n)$ with $n = k + 1$. These are the
terms of the weighted Lambert series $f(q) = \sum_{n \ge 1} n q^n / (1 - q^n)$. -/
public noncomputable def lambertFSummand (q : {q : ℂ // ‖q‖ < 1}) (k : ℕ) : ℂ :=
  (k + 1 : ℂ) * (q : ℂ) ^ (k + 1) / (1 - (q : ℂ) ^ (k + 1))

/-- **The weighted Lambert series $f$.** For a complex number $q$ with $|q| < 1$, the weighted
Lambert series is $f(q) = \sum_{n \ge 1} n q^n / (1 - q^n)$. -/
public noncomputable def lambertF (q : {q : ℂ // ‖q‖ < 1}) : ℂ :=
  ∑' k, lambertFSummand q k

/-- **Terms of the weighted Lambert series $g$.** For a complex number $q$ with $|q| < 1$ and a
natural number $k$, the term of index $k$ is $n q^n / (1 + q^n)$ with $n = k + 1$. These are the
terms of the weighted Lambert series $g(q) = \sum_{n \ge 1} n q^n / (1 + q^n)$. -/
public noncomputable def lambertGSummand (q : {q : ℂ // ‖q‖ < 1}) (k : ℕ) : ℂ :=
  (k + 1 : ℂ) * (q : ℂ) ^ (k + 1) / (1 + (q : ℂ) ^ (k + 1))

/-- **The weighted Lambert series $g$.** For a complex number $q$ with $|q| < 1$, the weighted
Lambert series is $g(q) = \sum_{n \ge 1} n q^n / (1 + q^n)$. -/
public noncomputable def lambertG (q : {q : ℂ // ‖q‖ < 1}) : ℂ :=
  ∑' k, lambertGSummand q k

/-- **Terms of the power-weighted Lambert series $f_\mu$.** For a complex number $q$ with
$|q| < 1$, an integer $\mu \ge 1$ and a natural number $k$, the term of index $k$ is
$n^\mu q^n / (1 - q^n)$ with $n = k + 1$. These are the terms of the power-weighted Lambert series
$f_\mu(q) = \sum_{n \ge 1} n^\mu q^n / (1 - q^n)$. -/
public noncomputable def lambertFMuSummand (q : {q : ℂ // ‖q‖ < 1})
    (μ : {μ : ℕ // 1 ≤ μ}) (k : ℕ) : ℂ :=
  (k + 1 : ℂ) ^ (μ : ℕ) * (q : ℂ) ^ (k + 1) / (1 - (q : ℂ) ^ (k + 1))

/-- **The power-weighted Lambert series $f_\mu$.** For a complex number $q$ with $|q| < 1$ and an
integer $\mu \ge 1$, the power-weighted Lambert series is
$f_\mu(q) = \sum_{n \ge 1} n^\mu q^n / (1 - q^n)$. -/
public noncomputable def lambertFMu (q : {q : ℂ // ‖q‖ < 1})
    (μ : {μ : ℕ // 1 ≤ μ}) : ℂ :=
  ∑' k, lambertFMuSummand q μ k

/-- **Terms of the power-weighted Lambert series $g_\mu$.** For a complex number $q$ with
$|q| < 1$, an integer $\mu \ge 1$ and a natural number $k$, the term of index $k$ is
$n^\mu q^n / (1 + q^n)$ with $n = k + 1$. These are the terms of the power-weighted Lambert series
$g_\mu(q) = \sum_{n \ge 1} n^\mu q^n / (1 + q^n)$. -/
public noncomputable def lambertGMuSummand (q : {q : ℂ // ‖q‖ < 1})
    (μ : {μ : ℕ // 1 ≤ μ}) (k : ℕ) : ℂ :=
  (k + 1 : ℂ) ^ (μ : ℕ) * (q : ℂ) ^ (k + 1) / (1 + (q : ℂ) ^ (k + 1))

/-- **The power-weighted Lambert series $g_\mu$.** For a complex number $q$ with $|q| < 1$ and an
integer $\mu \ge 1$, the power-weighted Lambert series is
$g_\mu(q) = \sum_{n \ge 1} n^\mu q^n / (1 + q^n)$. -/
public noncomputable def lambertGMu (q : {q : ℂ // ‖q‖ < 1})
    (μ : {μ : ℕ // 1 ≤ μ}) : ℂ :=
  ∑' k, lambertGMuSummand q μ k

private theorem exists_lambertFMu_majorant (μ : {μ : ℕ // 1 ≤ μ}) {r : ℝ}
    (hr₀ : 0 < r) (hr₁ : r < 1) :
    ∃ a : ℕ → ℝ, Summable a ∧ (∀ n, 0 ≤ a n) ∧
      ∀ (q : {q : ℂ // ‖q‖ < 1}), ‖(q : ℂ)‖ ≤ r →
        ∀ n, ‖lambertFMuSummand q μ n‖ ≤ a n * ‖(q : ℂ)‖ := by
  let a (n : ℕ) : ℝ := (n + 1 : ℝ) ^ (μ : ℕ) * r ^ (n + 1) / (r * (1 - r))
  have hs := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (μ : ℕ)
    (show ‖r‖ < 1 by rwa [Real.norm_eq_abs, abs_of_pos hr₀])
  have hshift := (summable_nat_add_iff 1).2 hs
  have ha : Summable a := by
    simpa only [a, Nat.cast_add, Nat.cast_one] using hshift.div_const (r * (1 - r))
  refine ⟨a, ha, fun n => by dsimp [a]; positivity, ?_⟩
  intro q hq n
  have hpow : ‖(q : ℂ) ^ (n + 1)‖ ≤ r := by
    rw [norm_pow, pow_succ]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) q.2.le)).trans hq
  have hden : 1 - r ≤ ‖1 - (q : ℂ) ^ (n + 1)‖ :=
    (sub_le_sub_left hpow 1).trans (by
      simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) ((q : ℂ) ^ (n + 1)))
  have hnum : ‖(n + 1 : ℂ) ^ (μ : ℕ) * (q : ℂ) ^ (n + 1)‖ ≤
      (n + 1 : ℝ) ^ (μ : ℕ) * r ^ n * ‖(q : ℂ)‖ := by
    rw [norm_mul, norm_pow, norm_pow, ← Nat.cast_succ, Complex.norm_natCast, Nat.cast_succ,
      pow_succ, ← mul_assoc]
    gcongr
  rw [lambertFMuSummand, norm_div]
  calc
    _ ≤ ((n + 1 : ℝ) ^ (μ : ℕ) * r ^ n * ‖(q : ℂ)‖) / (1 - r) :=
      div_le_div₀ (by positivity) hnum (sub_pos.mpr hr₁) hden
    _ = a n * ‖(q : ℂ)‖ := by
      dsimp [a]
      rw [pow_succ]
      field_simp

private theorem summable_lambertFMuSummand (q : {q : ℂ // ‖q‖ < 1})
    (μ : {μ : ℕ // 1 ≤ μ}) : Summable (lambertFMuSummand q μ) := by
  obtain ⟨a, ha, _, hbound⟩ := exists_lambertFMu_majorant μ
    (r := (‖(q : ℂ)‖ + 1) / 2) (by positivity) (by linarith [q.2])
  exact (ha.mul_right ‖(q : ℂ)‖).of_norm_bounded (hbound q (by linarith [q.2]))

/-- **Uniform linear bound for the power-weighted Lambert series.** For each integer
$\mu\ge 1$ and each real radius $0<r<1$, there exists a real $C\ge 0$ such that
$|f_\mu(q)|\le C|q|$ for every complex $q$ with $|q|\le r$, where
$f_\mu(q)=\sum_{n\ge 1} n^\mu q^n/(1-q^n)$. -/
public theorem exists_norm_lambertFMu_le (μ : {μ : ℕ // 1 ≤ μ}) {r : ℝ}
    (hr₀ : 0 < r) (hr₁ : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : {q : ℂ // ‖q‖ < 1}), ‖(q : ℂ)‖ ≤ r →
      ‖lambertFMu q μ‖ ≤ C * ‖(q : ℂ)‖ := by
  obtain ⟨a, ha, ha₀, hbound⟩ := exists_lambertFMu_majorant μ hr₀ hr₁
  refine ⟨∑' n, a n, tsum_nonneg ha₀, ?_⟩
  intro q hq
  have hs := ha.mul_right ‖(q : ℂ)‖
  have hnorm := Summable.of_nonneg_of_le (fun n => norm_nonneg (lambertFMuSummand q μ n))
    (hbound q hq) hs
  rw [lambertFMu, ← ha.tsum_mul_right]
  exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum (hbound q hq) hs)

/-- **Dyadic difference of the power-weighted Lambert series.** For every integer $\mu\ge1$
and every complex $q$ with $|q|<1$, the series $f_\mu(q)=\sum_{n\ge1} n^\mu q^n/(1-q^n)$
and $g_\mu(q)=\sum_{n\ge1} n^\mu q^n/(1+q^n)$ satisfy
$g_\mu(q)=f_\mu(q)-2f_\mu(q^2)$. -/
public theorem lambertGMu_eq_sub_lambertFMu_sq (q : {q : ℂ // ‖q‖ < 1}) (μ : {μ : ℕ // 1 ≤ μ}) :
    lambertGMu q μ = lambertFMu q μ -
      2 * lambertFMu ⟨(q : ℂ) ^ 2, by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) q.2 (by decide)⟩ μ := by
  let q₂ : {q : ℂ // ‖q‖ < 1} := ⟨(q : ℂ) ^ 2, by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) q.2 (by decide)⟩
  change lambertGMu q μ = lambertFMu q μ - 2 * lambertFMu q₂ μ
  simp only [lambertGMu, lambertFMu]
  rw [← tsum_mul_left, ← (summable_lambertFMuSummand q μ).tsum_sub
    ((summable_lambertFMuSummand q₂ μ).mul_left 2)]
  refine tsum_congr fun n => ?_
  have hpow : ((q₂ : ℂ) ^ (n + 1)) = ((q : ℂ) ^ (n + 1)) ^ 2 := by
    change ((q : ℂ) ^ 2) ^ (n + 1) = _
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  simp only [lambertGMuSummand, lambertFMuSummand, hpow]
  let x := (q : ℂ) ^ (n + 1)
  change _ * x / (1 + x) = _ * x / (1 - x) - 2 * (_ * x ^ 2 / (1 - x ^ 2))
  have hx : ‖x‖ < 1 := by
    rw [show ‖x‖ = ‖(q : ℂ)‖ ^ (n + 1) by exact norm_pow _ _]
    exact pow_lt_one₀ (norm_nonneg _) q.2 (Nat.succ_ne_zero n)
  have hn : 1 - x ≠ 0 := sub_ne_zero.mpr fun h => by simp [← h] at hx
  have hp : 1 + x ≠ 0 := fun h => by
    have hx' : x = -1 := eq_neg_of_add_eq_zero_right (by simpa only [add_comm] using h)
    simp [hx'] at hx
  rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
  field_simp
  ring

/-- **Terms of the Lambert family $L_m$.** For a complex number $q$ with $|q| < 1$, an integer
$m \ge 1$ and a natural number $k$, the term of index $k$ is $q^{mn} / (1 - q^{2n})^m$ with
$n = k + 1$. These are the terms of $L_m(q) = \sum_{n \ge 1} q^{mn} / (1 - q^{2n})^m$. -/
public noncomputable def lambertLmSummand (q : {q : ℂ // ‖q‖ < 1})
    (m : {m : ℕ // 1 ≤ m}) (k : ℕ) : ℂ :=
  (q : ℂ) ^ ((m : ℕ) * (k + 1)) /
    (1 - (q : ℂ) ^ (2 * (k + 1))) ^ (m : ℕ)

/-- **The Lambert family $L_m$.** For a complex number $q$ with $|q| < 1$ and an integer $m \ge 1$,
the Lambert family is $L_m(q) = \sum_{n \ge 1} q^{mn} / (1 - q^{2n})^m$. -/
public noncomputable def lambertLm (q : {q : ℂ // ‖q‖ < 1})
    (m : {m : ℕ // 1 ≤ m}) : ℂ :=
  ∑' k, lambertLmSummand q m k

end

end MetaMathlibExt
