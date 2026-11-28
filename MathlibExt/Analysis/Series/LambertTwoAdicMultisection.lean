/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.LambertSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Two-adic multisection of the power-weighted Lambert series

For integers $\mu\ge 1$ and complex $q$ with $|q|<1$, the Lambert series $f_\mu(q)$ with
minus denominators is a double sum of weighted differences of the series $g_\mu$ with plus
denominators, evaluated at successive dyadic powers of $q$.

The weight $2^{(\mu+1)j+k}$ agrees with the printed $2^{2j+k}$ at $\mu=1$. At $\mu=2$ the
printed weight gives coefficient $1$ for $q^2$ on the right of equation (120), whereas the
coefficient on the left is $5$. The corrected weight is the one obtained by accounting for
the factor $2^{\mu j}$ from $( (2n-1)2^j)^\mu$ in the proof of Corollary 16.

The proof uses the relation $g_\mu(z)=f_\mu(z)-2f_\mu(z^2)$ to turn the sum into two telescoping
differences. A bound by products of summable polynomial-geometric subsequences justifies
iterating the unconditional double sum.

## References

* Christophe Vignat and Michael Milgram, *Curious Multisection Identities by Index Factorization*,
  Journal of Integer Sequences 27 (2024), Article 24.5.5, pp. 1–37, Corollary 16 and Corollary 17,
  equations (109) and (119)–(120), with the weight in (120) corrected as above.
-/

namespace MetaMathlibExt

private def dyadicPower (q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) : {z : ℂ // ‖z‖ < 1} :=
  ⟨q ^ 2 ^ n, by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity)⟩

private theorem summable_dyadic (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r < 1) (m : ℕ) :
    Summable fun n : ℕ => (2 : ℝ) ^ (m * n) * r ^ ((2 : ℕ) ^ n) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) m
    (show ‖r‖ < 1 by rwa [Real.norm_eq_abs, abs_of_nonneg hr₀])
  convert h.comp_injective (Nat.pow_right_injective (a := 2) (by decide)) using 1
  funext n
  simp only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, Nat.mul_comm m n]

private theorem summable_weighted_lambertFMu (μ : {μ : ℕ // 1 ≤ μ}) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun p : ℕ × ℕ => ((2 : ℂ) ^ ((μ : ℕ) + 1)) ^ p.1 * (2 : ℂ) ^ p.2 *
      lambertFMu (dyadicPower q hq (p.1 + p.2)) μ := by
  let r := (‖q‖ + 1) / 2
  have hr₀ : 0 < r := by dsimp [r]; positivity
  have hr₁ : r < 1 := by dsimp [r]; linarith
  have hqr : ‖q‖ ≤ r := by dsimp [r]; linarith
  have hqr₂ : ‖q‖ ≤ r ^ 2 := by dsimp [r]; nlinarith [sq_nonneg (‖q‖ - 1)]
  obtain ⟨C, hC, hF⟩ := exists_norm_lambertFMu_le μ hr₀ hr₁
  let a (j : ℕ) := (2 : ℝ) ^ (((μ : ℕ) + 1) * j) * r ^ ((2 : ℕ) ^ j)
  let b (k : ℕ) := (2 : ℝ) ^ k * r ^ ((2 : ℕ) ^ k)
  have ha : Summable a := summable_dyadic r hr₀.le hr₁ _
  have hb : Summable b := by simpa only [b, one_mul] using summable_dyadic r hr₀.le hr₁ 1
  refine ((ha.mul_of_nonneg hb (fun j => by dsimp [a]; positivity)
    (fun k => by dsimp [b]; positivity)).mul_left C).of_norm_bounded ?_
  rintro ⟨j, k⟩
  let z := dyadicPower q hq (j + k)
  have hz : ‖(z : ℂ)‖ ≤ r := by
    change ‖q ^ ((2 : ℕ) ^ (j + k))‖ ≤ r
    rw [norm_pow]
    have hpow : ‖q‖ ^ ((2 : ℕ) ^ (j + k)) ≤ ‖q‖ ^ 1 :=
      pow_le_pow_of_le_one (norm_nonneg q) hq.le (Nat.one_le_iff_ne_zero.mpr (by positivity))
    exact (hpow.trans_eq (pow_one _)).trans hqr
  have hexp : (2 : ℕ) ^ j + 2 ^ k ≤ 2 * 2 ^ (j + k) := by
    have h₁ : (2 : ℕ) ^ j ≤ 2 ^ (j + k) := pow_le_pow_right₀ (by decide) (by omega)
    have h₂ : (2 : ℕ) ^ k ≤ 2 ^ (j + k) := pow_le_pow_right₀ (by decide) (by omega)
    omega
  have hdyadic : ‖(z : ℂ)‖ ≤ r ^ ((2 : ℕ) ^ j) * r ^ ((2 : ℕ) ^ k) := by
    change ‖q ^ ((2 : ℕ) ^ (j + k))‖ ≤ _
    rw [norm_pow, ← pow_add]
    calc
      _ ≤ (r ^ 2) ^ ((2 : ℕ) ^ (j + k)) := pow_le_pow_left₀ (norm_nonneg _) hqr₂ _
      _ = r ^ (2 * (2 : ℕ) ^ (j + k)) := (pow_mul r 2 _).symm
      _ ≤ _ := pow_le_pow_of_le_one hr₀.le hr₁.le hexp
  change ‖((2 : ℂ) ^ ((μ : ℕ) + 1)) ^ j * (2 : ℂ) ^ k * lambertFMu z μ‖ ≤ C * (a j * b k)
  simp only [norm_mul, norm_pow, Complex.norm_ofNat, ← pow_mul]
  calc
    _ ≤ (2 : ℝ) ^ (((μ : ℕ) + 1) * j) * 2 ^ k *
        (C * (r ^ ((2 : ℕ) ^ j) * r ^ ((2 : ℕ) ^ k))) := by
      gcongr
      exact (hF z hz).trans (mul_le_mul_of_nonneg_left hdyadic hC)
    _ = _ := by dsimp [a, b]; ring

private theorem tsum_sub_succ {f : ℕ → ℂ} (h : Summable f) :
    (∑' n, (f n - f (n + 1))) = f 0 := by
  rw [h.tsum_sub ((summable_nat_add_iff 1).2 h)]
  exact sub_eq_of_eq_add (h.tsum_eq_zero_add)

private theorem tsum_double_difference {f : ℕ × ℕ → ℂ} (hf : Summable f) :
    (∑' p : ℕ × ℕ, ((f p - f (p.1, p.2 + 1)) -
      (f (p.1 + 1, p.2) - f (p.1 + 1, p.2 + 1)))) = f (0, 0) := by
  let d (p : ℕ × ℕ) := f p - f (p.1, p.2 + 1)
  have hd : Summable d := hf.sub (hf.comp_injective
    (Function.injective_id.prodMap Nat.succ_injective))
  have hds : Summable fun p : ℕ × ℕ => d (p.1 + 1, p.2) :=
    hd.comp_injective (Nat.succ_injective.prodMap Function.injective_id)
  change (∑' p : ℕ × ℕ, (d p - d (p.1 + 1, p.2))) = f (0, 0)
  rw [(hd.sub hds).tsum_prod]
  have hrow (j : ℕ) : (∑' k, d (j, k)) = f (j, 0) := tsum_sub_succ (hf.prod_factor j)
  calc
    _ = ∑' j, (f (j, 0) - f (j + 1, 0)) := by
      refine tsum_congr fun j => ?_
      rw [(hd.prod_factor j).tsum_sub (hd.prod_factor (j + 1)), hrow, hrow]
    _ = _ := tsum_sub_succ (hf.comp_injective fun _ _ h => congrArg Prod.fst h)

/-- **Two-adic multisection of the power-weighted Lambert series.** For every integer $\mu \ge 1$
and every complex number $q$ with $|q| < 1$, the power-weighted Lambert series
$f_\mu(q) = \sum_{n \ge 1} n^\mu q^n / (1 - q^n)$ and
$g_\mu(q) = \sum_{n \ge 1} n^\mu q^n / (1 + q^n)$ satisfy
$$
f_\mu(q) = \sum_{j, k \ge 0} 2^{(\mu+1)j+k}
\left(g_\mu\left(q^{2^{j+k}}\right) - 2^{\mu+1} g_\mu\left(q^{2^{j+k+1}}\right)\right),
$$
the sum running over all pairs $(j, k)$ of natural numbers.

The paper prints the weight $2^{2j+k}$, its value for $\mu = 1$ (Corollary 16), which is false
for $\mu \ge 2$: for $\mu = 2$ the coefficient of $q^2$ is $\sigma_2(2) = 1^2 + 2^2 = 5$ on the
left and $1$ on the right. The weight $2^{(\mu+1)j+k}$ is what the paper's proof of Corollary 16
gives with $n^\mu$ in place of $n$: there $2^{2j+k} = 2^{j+k} \cdot 2^j$, where $2^j$ is the
factor of the index $(2n-1) 2^j$ in the summand $n$, which becomes $2^{\mu j}$ for $n^\mu$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5, Corollary 17
(`jis-2024-24.5.5-cor-17`). -/
public theorem lambertMu_sigma_eq_tsum_twoAdic (μ : {μ : ℕ // 1 ≤ μ}) (q : ℂ)
    (hq : ‖q‖ < 1) :
    lambertFMu ⟨q, hq⟩ μ
      = ∑' x : ℕ × ℕ, (2 : ℂ) ^ (((μ : ℕ) + 1) * x.1 + x.2)
          * (lambertGMu ⟨q ^ 2 ^ (x.1 + x.2),
              (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))⟩ μ
            - 2 ^ ((μ : ℕ) + 1) * lambertGMu ⟨q ^ 2 ^ (x.1 + x.2 + 1),
              (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))⟩ μ) := by
  let F (n : ℕ) := lambertFMu (dyadicPower q hq n) μ
  let G (n : ℕ) := lambertGMu (dyadicPower q hq n) μ
  let A := (2 : ℂ) ^ ((μ : ℕ) + 1)
  let f (p : ℕ × ℕ) := A ^ p.1 * (2 : ℂ) ^ p.2 * F (p.1 + p.2)
  have hG (n : ℕ) : G n = F n - 2 * F (n + 1) := by
    unfold G F
    rw [lambertGMu_eq_sub_lambertFMu_sq]
    congr 2
    apply congrArg (fun z => lambertFMu z μ)
    apply Subtype.ext
    change (q ^ ((2 : ℕ) ^ n)) ^ (2 : ℕ) = q ^ ((2 : ℕ) ^ (n + 1))
    rw [← pow_mul, pow_succ]
  change _ = ∑' p : ℕ × ℕ, (2 : ℂ) ^ (((μ : ℕ) + 1) * p.1 + p.2) *
    (G (p.1 + p.2) - A * G (p.1 + p.2 + 1))
  symm
  calc
    _ = ∑' p : ℕ × ℕ, ((f p - f (p.1, p.2 + 1)) -
        (f (p.1 + 1, p.2) - f (p.1 + 1, p.2 + 1))) := by
      refine tsum_congr fun ⟨j, k⟩ => ?_
      have hw : (2 : ℂ) ^ (((μ : ℕ) + 1) * j + k) = A ^ j * (2 : ℂ) ^ k := by
        rw [pow_add, pow_mul]
      simp only [hw, hG, f, pow_succ, Nat.add_succ, Nat.succ_add, Nat.add_zero]
      ring
    _ = f (0, 0) := tsum_double_difference (summable_weighted_lambertFMu μ q hq)
    _ = _ := by
      simp only [f, pow_zero, one_mul, Nat.zero_add, F]
      congr 1
      exact Subtype.ext (by simp [dyadicPower])

end MetaMathlibExt
