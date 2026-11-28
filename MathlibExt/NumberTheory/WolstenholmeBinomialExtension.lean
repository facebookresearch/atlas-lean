/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Binomial

/-!
# Binomial extensions of Wolstenholme's theorem

This module gives binomial product and coefficient identities and a coefficient bound for divided
derivatives. For prime `p`, an offset `a : ℕ` and `0 < k`, `choose_mul_prod_ascFactorial` clears
the denominator of the block quotient for `((a + k) * p).choose (k * p)`.

## References

* Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS
  26 (2026), Article A32, pp. 1–28, Lemmas 1, 2, 5 and 6.
-/

namespace MetaMathlibExt

/-- Count successive choices of blocks of size `p`, with `d * p` elements left over. -/
private theorem choose_blocks_eq_quotient (d m p : ℕ) :
    (((d + m) * p).choose (m * p) : ℚ) =
      (∏ j ∈ Finset.range m, (((d + j + 1) * p).choose p : ℚ)) /
        ∏ j ∈ Finset.range m, (((j + 1) * p).choose p : ℚ) := by
  apply (eq_div_iff ?_).2
  · norm_cast
    induction m with
    | zero => simp
    | succ m ih =>
      have step : ((d + m + 1) * p).choose ((m + 1) * p) * ((m + 1) * p).choose p =
          ((d + m + 1) * p).choose p * ((d + m) * p).choose (m * p) := by
        simpa [Nat.succ_mul] using
          (Nat.choose_mul (n := (d + m + 1) * p) (k := (m + 1) * p) (s := p)
            (by simp [Nat.succ_mul]))
      simp only [Finset.prod_range_succ]
      rw [← Nat.add_assoc, mul_left_comm, step, ← ih]
      ac_rfl
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact_mod_cast Nat.choose_ne_zero (show p ≤ (j + 1) * p by simp [Nat.succ_mul])

set_option linter.unusedVariables false in
/-- For prime `p` and `1 ≤ m ≤ n`, the binomial coefficient at `(n * p, m * p)` is a
quotient of products of binomial coefficients with lower index `p - 1` or `p`.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 6
(`integers-2026-A32-lem-6`). -/
public theorem choose_mul_prime_eq_prod_div_prod (p m n : ℕ) (hp : p.Prime) (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    ((n * p).choose (m * p) : ℚ) =
        (n.choose m : ℚ) * (∏ j ∈ Finset.range m, (((n - m + j + 1) * p - 1).choose (p - 1) : ℚ)) /
          ∏ j ∈ Finset.range m, (((j + 1) * p - 1).choose (p - 1) : ℚ) ∧
      ((n * p).choose (m * p) : ℚ) =
        (∏ j ∈ Finset.range m, (((n - m + j + 1) * p).choose p : ℚ)) /
          ∏ j ∈ Finset.range m, (((j + 1) * p).choose p : ℚ) := by
  have block (q : ℕ) := choose_blocks_eq_quotient (n - m) m q
  simp only [Nat.sub_add_cancel hmn] at block
  refine ⟨(block p).trans ?_, block p⟩
  -- The case of blocks of size one collects the linear factors into `n.choose m`.
  have linearFactors := block 1
  simp only [Nat.mul_one, Nat.choose_one_right] at linearFactors
  simp_rw [Nat.choose_mul_right hp.ne_zero, Nat.cast_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, mul_div_mul_comm, ← linearFactors,
    mul_div_assoc]

/-- **Block form of Kehila's quotient formula.** Let $p$ be a prime and let $a$ and $k$ be
natural numbers with $k \ge 1$. For $c \in \mathbb{N}$ let
$B(c) = (cp + 1)(cp + 2) \cdots (cp + p - 1)$ be the product of the $p - 1$ integers strictly
between $cp$ and $(c + 1)p$. Then

$$\binom{(a + k)p}{kp} \prod_{j=0}^{k-1} B(j) = \binom{a + k}{k} \prod_{j=0}^{k-1} B(a + j).$$

The proof of Lemma 6 gives the quotient of these block products. Since
$B(c) = (p - 1)! \binom{(c + 1)p - 1}{p - 1}$, the identity also follows by clearing the
first formula's denominator and multiplying both sides by $((p - 1)!)^k$.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*,
INTEGERS 26 (2026), Article A32, Lemma 6 and its proof. -/
public theorem choose_mul_prod_ascFactorial (p a k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    ((a + k) * p).choose (k * p) * ∏ j ∈ Finset.range k, (j * p + 1).ascFactorial (p - 1) =
      (a + k).choose k * ∏ j ∈ Finset.range k, ((a + j) * p + 1).ascFactorial (p - 1) := by
  have h := (choose_mul_prime_eq_prod_div_prod p k (a + k) hp hk (Nat.le_add_left k a)).1
  simp only [Nat.add_sub_cancel] at h
  have hd : (∏ j ∈ Finset.range k, (((j + 1) * p - 1).choose (p - 1) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by
      have hle : p ≤ (j + 1) * p := Nat.le_mul_of_pos_left p (Nat.succ_pos j)
      exact_mod_cast (Nat.choose_pos (Nat.sub_le_sub_right hle 1)).ne'
  rw [eq_div_iff hd] at h
  have hnat : ((a + k) * p).choose (k * p) *
      ∏ j ∈ Finset.range k, ((j + 1) * p - 1).choose (p - 1) =
        (a + k).choose k * ∏ j ∈ Finset.range k, ((a + j + 1) * p - 1).choose (p - 1) := by
    exact_mod_cast h
  have index (j : ℕ) : j * p + (p - 1) = (j + 1) * p - 1 := by
    rw [Nat.add_mul, one_mul, Nat.add_sub_assoc hp.pos]
  simp only [Nat.ascFactorial_eq_factorial_mul_choose, index, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_range]
  rw [mul_left_comm, hnat, mul_left_comm]

/-- **Coefficient bound for the divided derivatives $D^n/n!$.** Let $p$ be a prime and $B$ a
normed vector space over $\mathbb{Q}_p$ whose norm is ultrametric. Let $(a_k)_{k \ge 0}$ be a
sequence in $B$ and $C$ a real number with $\|a_k\| \le C$ for every $k$. Then for all natural
numbers $n$ and $k$,
$$\Big\| \binom{k+n}{n} a_{k+n} \Big\| \le C.$$

The vectors $\binom{k+n}{n} a_{k+n}$ are the coefficients of $D^n f / n!$ for
$f = \sum_k a_k t^k$, so this is the coefficientwise form of the bound $\|D^n / n!\| \le 1$ on
the Tate algebra $B\{t\}$ with the sup norm.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 1
(`integers-2026-A32-lem-1`). -/
public theorem norm_choose_nsmul_coeff_le {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] [IsUltrametricDist B] (a : ℕ → B) (C : ℝ)
    (hC : ∀ k, ‖a k‖ ≤ C) (n k : ℕ) :
    ‖(k + n).choose n • a (k + n)‖ ≤ C :=
  (IsUltrametricDist.norm_nsmul_le (a (k + n)) _).trans (hC (k + n))

/-- **Binomial coefficients with upper index $-np$.** Let $p$, $n$ and $k$ be natural numbers
with $p \ge 1$ and $k \ge 1$. For an integer $x$ and a natural number $r$ write
$\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$. Then
$$
\binom{-np}{kp} = (-1)^{kp} \, \frac{n}{k} \binom{(n+k)p - 1}{kp - 1} =
(-1)^{kp} \, \frac{n}{n+k} \binom{(n+k)p}{kp}.
$$

The paper takes $p$ prime.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 5
(`integers-2026-A32-lem-5`). -/
public theorem ringChoose_neg_mul_mul_eq (p n k : ℕ) (hp : 0 < p) (hk : 1 ≤ k) :
    ((Ring.choose (-((n * p : ℕ) : ℤ)) (k * p) : ℤ) : ℚ) =
        (-1) ^ (k * p) * ((n : ℚ) / k) * (((n + k) * p - 1).choose (k * p - 1) : ℚ) ∧
      ((Ring.choose (-((n * p : ℕ) : ℤ)) (k * p) : ℤ) : ℚ) =
        (-1) ^ (k * p) * ((n : ℚ) / (n + k)) * (((n + k) * p).choose (k * p) : ℚ) := by
  have hkp : 0 < k * p := Nat.mul_pos hk hp
  have htop : 0 < (n + k) * p := Nat.mul_pos (by omega) hp
  let t := (n + k) * p - 1
  have hindex : ((n * p : ℕ) : ℤ) + (k * p : ℕ) - 1 = (t : ℤ) := by
    unfold t
    rw [Nat.cast_sub htop, Nat.cast_one, Nat.add_mul, Nat.cast_add]
  have hneg : ((Ring.choose (-((n * p : ℕ) : ℤ)) (k * p) : ℤ) : ℚ) =
      (-1) ^ (k * p) * (t.choose (k * p) : ℚ) := by
    rw [Ring.choose_neg, hindex, Ring.choose_natCast, Units.smul_def, zsmul_eq_mul,
      Int.cast_id, Int.coe_negOnePow_natCast]
    push_cast
    rfl
  have ht : t + 1 = (n + k) * p := Nat.sub_add_cancel htop
  have hdiff : t - (k * p - 1) = n * p := by
    dsimp [t]
    rw [Nat.add_mul]
    omega
  -- Shift the lower index for the first ratio and the upper index for the second.
  have lower := Nat.choose_succ_right_eq t (k * p - 1)
  rw [Nat.sub_add_cancel hkp, hdiff, ← Nat.mul_assoc, ← Nat.mul_assoc] at lower
  have upper := Nat.choose_mul_succ_eq t (k * p)
  rw [ht, show (n + k) * p - k * p = n * p by rw [Nat.add_mul, Nat.add_sub_cancel],
    ← Nat.mul_assoc, ← Nat.mul_assoc] at upper
  constructor <;> rw [hneg, mul_assoc] <;> congr 1
  · rw [div_mul_eq_mul_div, eq_div_iff (by positivity), mul_comm (n : ℚ)]
    exact_mod_cast Nat.mul_right_cancel hp lower
  · rw [div_mul_eq_mul_div, eq_div_iff (by positivity), mul_comm (n : ℚ)]
    exact_mod_cast Nat.mul_right_cancel hp upper

open Polynomial in
/-- **Coefficients of $(x + 1)^{jp} (x^p + 1)^{n-j}$.** Let $n$, $j$ and $k$ be natural numbers and
$p$ a positive integer, and let $d = \max(n - j, 0)$. Then the coefficient of $x^{kp}$ in the
polynomial $(x + 1)^{jp} (x^p + 1)^{d}$ is
$$\sum_{s=0}^{\min(j, k)} \binom{jp}{sp} \binom{d}{k - s}.$$

The source takes $p$ prime; here $p$ is any positive integer.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 2
(`integers-2026-A32-lem-2`). -/
public theorem coeff_add_one_pow_mul_X_pow_add_one_pow (p n j k : ℕ) (hp : 0 < p) :
    ((X + 1 : ℕ[X]) ^ (j * p) * (X ^ p + 1) ^ (n - j)).coeff (k * p) =
      ∑ s ∈ Finset.range (j + 1),
        if s ≤ k then (j * p).choose (s * p) * (n - j).choose (k - s) else 0 := by
  rw [add_pow (X ^ p : ℕ[X]) 1]
  simp only [one_pow, mul_one, ← pow_mul', Finset.mul_sum, finsetSum_coeff, ← mul_assoc,
    coeff_mul_natCast, coeff_mul_X_pow', Nat.mul_le_mul_right_iff hp, ← Nat.sub_mul,
    coeff_X_add_one_pow, Nat.cast_id, ite_mul, zero_mul]
  -- The two exponents are `(k - r) * p` and `r * p`; zero terms need not be reindexed.
  refine Finset.sum_bij_ne_zero (fun r _ _ => k - r) ?_ ?_ ?_ ?_
  · intro r _ hr
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    by_contra! h
    exact hr (by simp [Nat.choose_eq_zero_of_lt ((Nat.mul_lt_mul_right hp).2 h)])
  · intro r₁ _ h₁ r₂ _ h₂ heq
    have hr₁ : r₁ ≤ k := by by_contra h; exact h₁ (ite_eq_right h)
    have hr₂ : r₂ ≤ k := by by_contra h; exact h₂ (ite_eq_right h)
    omega
  · intro s _ hs
    have hsk : s ≤ k := by by_contra h; exact hs (ite_eq_right h)
    have hr : k - s ≤ n - j := by
      by_contra! h
      exact hs (by simp [Nat.choose_eq_zero_of_lt h])
    refine ⟨k - s, Finset.mem_range.mpr (Nat.lt_succ_of_le hr), ?_, Nat.sub_sub_self hsk⟩
    simpa only [ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self hsk, ite_eq_left hsk] using hs
  · intro r _ hr
    have hrk : r ≤ k := by by_contra h; exact hr (ite_eq_right h)
    simp only [ite_eq_left hrk, ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self hrk]

end MetaMathlibExt
