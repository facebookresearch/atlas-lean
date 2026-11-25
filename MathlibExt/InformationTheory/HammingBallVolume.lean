/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Data.Nat.Choose.Sum
import all Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Lean.Elab.Tactic.Omega

/-!
# Volume of a Hamming ball and the `q`-ary entropy

The volume of a `q`-ary Hamming ball of radius `e ≤ p n` is at most `q ^ {H_q(p) n}` when
`0 ≤ p ≤ 1 - 1/q` (`sum_choose_mul_pow_le_exp`), and the ball of radius `⌊pn⌋` has volume at
least `q ^ {H_q(p) n - o(n)}` (`sum_choose_mul_pow_ge_exp`, through the central binomial term
`central_term_ge` and `choose_mul_pow_ge`). Mathlib's `Real.qaryEntropy q p` is the `q`-ary
entropy measured in nats, so `q ^ {H_q(p) n} = exp (n · Real.qaryEntropy q p)`.

## References

* V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025,
  Definition 3.3.1, Definition 3.3.2 and Proposition 3.3.3.
-/

@[expose] public section

namespace MathlibExt.InformationTheory.HammingBallVolume

open Finset Real

/-- The unfolding of Mathlib's `Real.qaryEntropy`, whose body is not exposed: the only use of
`import all Mathlib.Analysis.SpecialFunctions.BinaryEntropy` in this file. -/
private theorem qaryEntropy_eq (q : ℕ) (p : ℝ) :
    qaryEntropy q p = p * log ((q : ℝ) - 1) + (-(p * log p) - (1 - p) * log (1 - p)) := by
  rw [qaryEntropy, binEntropy, log_inv, log_inv]
  push_cast
  ring

/-- **Volume of a Hamming ball, entropy upper bound.** Let `q ≥ 2`, `0 ≤ p ≤ 1 - 1/q` and let
`e ≤ p n` be a natural number. Then
`∑_{i=0}^{e} C(n, i) (q - 1) ^ i ≤ exp (n · Real.qaryEntropy q p) = q ^ {H_q(p) n}`,
where `H_q(p) = p log_q (q - 1) - p log_q p - (1 - p) log_q (1 - p)` (Guruswami, Rudra and
Sudan, *Essential Coding Theory*, draft of August 26, 2025, Proposition 3.3.3 (i); there the
radius is `pn`, here any integer radius at most `pn`). The proof compares each term with the
binomial expansion of `(p + (1 - p)) ^ n = 1`, using `p / ((q - 1)(1 - p)) ≤ 1`. -/
theorem sum_choose_mul_pow_le_exp {q n e : ℕ} {p : ℝ} (hq : 2 ≤ q) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1 - 1 / q) (he : (e : ℝ) ≤ p * n) :
    ((∑ i ∈ range (e + 1), n.choose i * (q - 1) ^ i : ℕ) : ℝ) ≤
      exp (n * qaryEntropy q p) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rcases eq_or_lt_of_le hp0 with rfl | hp
  · have : e = 0 := by
      have : (e : ℝ) ≤ 0 := by simpa using he
      exact_mod_cast le_antisymm this (Nat.cast_nonneg e)
    subst this
    simp [qaryEntropy_eq]
  have hp1' : p < 1 := by
    have : 0 < 1 / (q : ℝ) := by positivity
    linarith
  have hqpos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  -- `p ≤ (q - 1) (1 - p)`.
  have hratio : p ≤ ((q : ℝ) - 1) * (1 - p) := by
    have h1 : 1 / (q : ℝ) * q = 1 := by field_simp
    nlinarith
  have hlog : log p ≤ log ((q : ℝ) - 1) + log (1 - p) := by
    rw [← log_mul hqpos.ne' (by linarith)]
    exact log_le_log hp hratio
  have hen : e ≤ n := by
    have : (e : ℝ) ≤ n := he.trans (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    exact_mod_cast this
  set H := qaryEntropy q p with hH
  have hHdef : H = p * log ((q : ℝ) - 1) - p * log p - (1 - p) * log (1 - p) := by
    rw [hH, qaryEntropy_eq]
    ring
  -- Termwise comparison with the binomial expansion.
  have hterm : ∀ i ∈ range (e + 1),
      ((n.choose i * (q - 1) ^ i : ℕ) : ℝ) * exp (-(n * H)) ≤
        p ^ i * (1 - p) ^ (n - i) * n.choose i := by
    intro i hi
    have hie : i ≤ e := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hin : i ≤ n := hie.trans hen
    have hi' : (i : ℝ) ≤ p * n := (Nat.cast_le.mpr hie).trans he
    have hexp1 : ((q : ℝ) - 1) ^ i * exp (-(n * H)) =
        exp (i * log ((q : ℝ) - 1) - n * H) := by
      rw [sub_eq_add_neg _ (n * H), exp_add, exp_nat_mul, exp_log hqpos]
    have hexp2 : p ^ i * (1 - p) ^ (n - i) =
        exp (i * log p + ((n - i : ℕ) : ℝ) * log (1 - p)) := by
      rw [exp_add, exp_nat_mul, exp_nat_mul, exp_log hp, exp_log (by linarith)]
    have hle : i * log ((q : ℝ) - 1) - n * H ≤
        i * log p + ((n - i : ℕ) : ℝ) * log (1 - p) := by
      rw [hHdef, Nat.cast_sub hin]
      have hk : 0 ≤ p * n - i := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hlog hk]
    push_cast
    rw [hq1]
    calc (n.choose i : ℝ) * ((q : ℝ) - 1) ^ i * exp (-(n * H))
        = n.choose i * (((q : ℝ) - 1) ^ i * exp (-(n * H))) := by ring
      _ ≤ n.choose i * (p ^ i * (1 - p) ^ (n - i)) := by
          rw [hexp1, hexp2]
          exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr hle) (Nat.cast_nonneg _)
      _ = p ^ i * (1 - p) ^ (n - i) * n.choose i := by ring
  have hsum : ((∑ i ∈ range (e + 1), n.choose i * (q - 1) ^ i : ℕ) : ℝ) * exp (-(n * H)) ≤ 1 :=
    calc ((∑ i ∈ range (e + 1), n.choose i * (q - 1) ^ i : ℕ) : ℝ) * exp (-(n * H))
        = ∑ i ∈ range (e + 1), ((n.choose i * (q - 1) ^ i : ℕ) : ℝ) * exp (-(n * H)) := by
          rw [Nat.cast_sum, sum_mul]
      _ ≤ ∑ i ∈ range (e + 1), p ^ i * (1 - p) ^ (n - i) * n.choose i := sum_le_sum hterm
      _ ≤ ∑ i ∈ range (n + 1), p ^ i * (1 - p) ^ (n - i) * n.choose i := by
          refine sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) ?_
          intro i _ _
          have : 0 ≤ 1 - p := by linarith
          positivity
      _ = (p + (1 - p)) ^ n := (add_pow p (1 - p) n).symm
      _ = 1 := by simp
  have hpos : 0 < exp (-(n * H)) := exp_pos _
  calc ((∑ i ∈ range (e + 1), n.choose i * (q - 1) ^ i : ℕ) : ℝ)
      = ((∑ i ∈ range (e + 1), n.choose i * (q - 1) ^ i : ℕ) : ℝ) * exp (-(n * H)) *
          exp (n * H) := by rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    _ ≤ 1 * exp (n * H) := mul_le_mul_of_nonneg_right hsum (exp_pos _).le
    _ = exp (n * H) := one_mul _

/-- **The central binomial term.** For `0 < n` and `m ≤ n`, the term of index `m` of the
binomial distribution with `n` trials and success probability `x = m / n` is at least
`1 / (n + 1)`: it is the largest of the `n + 1` terms, which sum to `1`. -/
theorem central_term_ge {n m : ℕ} (hn : 0 < n) (hm : m ≤ n) :
    1 / ((n : ℝ) + 1) ≤ n.choose m * ((m : ℝ) / n) ^ m * (1 - (m : ℝ) / n) ^ (n - m) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set x : ℝ := m / n with hx
  set t : ℕ → ℝ := fun k => n.choose k * x ^ k * (1 - x) ^ (n - k) with ht
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hn']; exact_mod_cast hm
  have hsum : ∑ k ∈ range (n + 1), t k = 1 := by
    have := (add_pow x (1 - x) n).symm
    rw [add_sub_cancel, one_pow] at this
    rw [← this]
    refine sum_congr rfl fun k _ => ?_
    simp only [ht]; ring
  -- Ratio comparisons, from `C(n, k+1) (k+1) = C(n, k) (n - k)`.
  have hdown : ∀ k, m ≤ k → k + 1 ≤ n → t (k + 1) ≤ t k := by
    intro k hk hkn
    have hnat : n.choose (k + 1) * m ≤ n.choose k * (n - m) := by
      have h1 := Nat.choose_succ_right_eq n k
      have h2 : (n - k) * m ≤ (n - m) * (k + 1) :=
        calc (n - k) * m ≤ (n - m) * m := Nat.mul_le_mul_right _ (by omega)
          _ ≤ (n - m) * (k + 1) := Nat.mul_le_mul_left _ (by omega)
      refine Nat.le_of_mul_le_mul_right (c := k + 1) ?_ (by omega)
      calc n.choose (k + 1) * m * (k + 1) = n.choose k * ((n - k) * m) := by
            rw [mul_right_comm, h1, mul_assoc]
        _ ≤ n.choose k * ((n - m) * (k + 1)) := Nat.mul_le_mul_left _ h2
        _ = n.choose k * (n - m) * (k + 1) := by ring
    have hreal : (n.choose (k + 1) : ℝ) * x ≤ n.choose k * (1 - x) := by
      have : ((n.choose (k + 1) * m : ℕ) : ℝ) ≤ ((n.choose k * (n - m) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast [Nat.cast_sub hm] at this
      rw [hx, mul_div_assoc', one_sub_div hn'.ne', mul_div_assoc']
      exact div_le_div_of_nonneg_right this hn'.le
    have hP : 0 ≤ x ^ k * (1 - x) ^ (n - (k + 1)) := by
      have : 0 ≤ 1 - x := by linarith
      positivity
    have e1 : t (k + 1) = (n.choose (k + 1) * x) * (x ^ k * (1 - x) ^ (n - (k + 1))) := by
      simp only [ht]; ring
    have e2 : t k = (n.choose k * (1 - x)) * (x ^ k * (1 - x) ^ (n - (k + 1))) := by
      simp only [ht]
      rw [show n - k = n - (k + 1) + 1 by omega, pow_succ]; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hreal hP
  have hup : ∀ k, k + 1 ≤ m → t k ≤ t (k + 1) := by
    intro k hk
    have hnat : n.choose k * (n - m) ≤ n.choose (k + 1) * m := by
      have h1 := Nat.choose_succ_right_eq n k
      have h2 : (n - m) * (k + 1) ≤ (n - k) * m :=
        Nat.mul_le_mul (by omega) hk
      refine Nat.le_of_mul_le_mul_right (c := k + 1) ?_ (by omega)
      calc n.choose k * (n - m) * (k + 1) = n.choose k * ((n - m) * (k + 1)) := by ring
        _ ≤ n.choose k * ((n - k) * m) := Nat.mul_le_mul_left _ h2
        _ = n.choose (k + 1) * m * (k + 1) := by
            rw [mul_right_comm (n.choose (k + 1)), h1, mul_assoc]
    have hreal : (n.choose k : ℝ) * (1 - x) ≤ n.choose (k + 1) * x := by
      have : ((n.choose k * (n - m) : ℕ) : ℝ) ≤ ((n.choose (k + 1) * m : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast [Nat.cast_sub hm] at this
      rw [hx, mul_div_assoc', one_sub_div hn'.ne', mul_div_assoc']
      exact div_le_div_of_nonneg_right this hn'.le
    have hP : 0 ≤ x ^ k * (1 - x) ^ (n - (k + 1)) := by
      have : 0 ≤ 1 - x := by linarith
      positivity
    have e1 : t (k + 1) = (n.choose (k + 1) * x) * (x ^ k * (1 - x) ^ (n - (k + 1))) := by
      simp only [ht]; ring
    have e2 : t k = (n.choose k * (1 - x)) * (x ^ k * (1 - x) ^ (n - (k + 1))) := by
      simp only [ht]
      rw [show n - k = n - (k + 1) + 1 by omega, pow_succ]; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hreal hP
  have hmax : ∀ k ≤ n, t k ≤ t m := by
    have hge : ∀ j, m + j ≤ n → t (m + j) ≤ t m := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih => intro h; exact (hdown (m + j) (by omega) (by omega)).trans (ih (by omega))
    have hle : ∀ j, j ≤ m → t (m - j) ≤ t m := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro h
        have := hup (m - (j + 1)) (by omega)
        rw [show m - (j + 1) + 1 = m - j by omega] at this
        exact this.trans (ih (by omega))
    intro k hk
    rcases le_total m k with h | h
    · have := hge (k - m) (by omega); rwa [Nat.add_sub_cancel' h] at this
    · have := hle (m - k) (by omega); rwa [Nat.sub_sub_self h] at this
  have h1 : (1 : ℝ) ≤ (n + 1) * t m := by
    calc (1 : ℝ) = ∑ k ∈ range (n + 1), t k := hsum.symm
      _ ≤ ∑ _k ∈ range (n + 1), t m := sum_le_sum fun k hk => hmax k (by
            have := mem_range.mp hk; omega)
      _ = (n + 1) * t m := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  rw [div_le_iff₀ (by positivity)]
  simpa [ht, mul_comm] using h1

/-- **The largest term of a Hamming-ball volume.** For `0 < n`, `m ≤ n` and `q ≥ 2`, with
`x = m / n`, `C(n, m) (q - 1) ^ m ≥ exp (n · Real.qaryEntropy q x) / (n + 1)`. -/
theorem choose_mul_pow_ge {q n m : ℕ} (hq : 2 ≤ q) (hn : 0 < n) (hm : m ≤ n) :
    exp (n * qaryEntropy q ((m : ℝ) / n)) / ((n : ℝ) + 1) ≤ n.choose m * (((q : ℝ) - 1) ^ m) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  set x : ℝ := m / n with hx
  have hxm : (n : ℝ) * x = m := by rw [hx]; field_simp
  have hcentral := central_term_ge hn hm
  -- With `B = -x log x - (1 - x) log (1 - x)` (the binary entropy of `x`):
  -- `x ^ m (1 - x) ^ (n - m) = exp (-n B)` and
  -- `exp (n · Real.qaryEntropy q x) = (q - 1) ^ m exp (n B)`.
  set B : ℝ := -(x * log x) - (1 - x) * log (1 - x) with hB
  have hpow : x ^ m * (1 - x) ^ (n - m) = exp (-(n * B)) := by
    rcases Nat.eq_zero_or_pos m with h0 | hm0
    · subst h0; simp [hx, hB]
    rcases eq_or_lt_of_le hm with hmn | hmn
    · subst hmn
      have : x = 1 := by rw [hx]; field_simp
      simp [this, hB]
    have hx0 : 0 < x := by rw [hx]; exact div_pos (by exact_mod_cast hm0) hn'
    have hx1 : x < 1 := by rw [hx, div_lt_one hn']; exact_mod_cast hmn
    rw [← exp_log (mul_pos (pow_pos hx0 m)
      (pow_pos (by linarith : (0 : ℝ) < 1 - x) (n - m))), log_mul (pow_pos hx0 m).ne'
      (pow_pos (by linarith : (0 : ℝ) < 1 - x) (n - m)).ne', log_pow, log_pow,
      Nat.cast_sub hm]
    congr 1
    rw [hB, ← hxm]
    ring
  have hH : exp (n * qaryEntropy q x) = ((q : ℝ) - 1) ^ m * exp (n * B) := by
    rw [qaryEntropy_eq, mul_add, exp_add, ← mul_assoc, hxm, exp_nat_mul, exp_log hq1]
  have hone : exp (n * B) * exp (-(n * B)) = 1 := by
    rw [← exp_add, add_neg_cancel, exp_zero]
  have hA : 0 ≤ ((q : ℝ) - 1) ^ m * exp (n * B) := by positivity
  rw [hH]
  calc ((q : ℝ) - 1) ^ m * exp (n * B) / ((n : ℝ) + 1)
      = ((q : ℝ) - 1) ^ m * exp (n * B) * (1 / ((n : ℝ) + 1)) := by ring
    _ ≤ ((q : ℝ) - 1) ^ m * exp (n * B) *
          (n.choose m * x ^ m * (1 - x) ^ (n - m)) := mul_le_mul_of_nonneg_left hcentral hA
    _ = ((q : ℝ) - 1) ^ m * n.choose m *
          (exp (n * B) * (x ^ m * (1 - x) ^ (n - m))) := by ring
    _ = n.choose m * ((q : ℝ) - 1) ^ m := by rw [hpow, hone]; ring

/-- **Volume of a Hamming ball, entropy lower bound.** Let `q ≥ 2` and `0 ≤ p ≤ 1`. For every
`η > 0`, for all large enough `n`,
`∑_{i=0}^{⌊pn⌋} C(n, i) (q - 1) ^ i ≥ exp (n · Real.qaryEntropy q p - η n)`, that is
`Vol_q(n, pn) ≥ q ^ {H_q(p) n - o(n)}` (Guruswami, Rudra and Sudan, *Essential Coding Theory*,
draft of August 26, 2025, Proposition 3.3.3 (ii), stated there for `0 ≤ p ≤ 1 - 1/q`; the `o(n)`
term is written `η n` for an arbitrary `η > 0`, in nats). The proof keeps the single term
`i = ⌊pn⌋ = m`, bounds it below by `exp (n · Real.qaryEntropy q (m / n)) / (n + 1)` through the
central binomial term, and uses the uniform continuity of the entropy and `log (n + 1) = o(n)`. -/
theorem sum_choose_mul_pow_ge_exp {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N,
      exp (n * qaryEntropy q p - η * n) ≤
        ((∑ i ∈ range (⌊p * n⌋₊ + 1), n.choose i * (q - 1) ^ i : ℕ) : ℝ) := by
  -- Uniform continuity of the entropy on `[0, 1]`.
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous (qaryEntropy_continuous (q := q)).continuousOn)
    (η / 2) (by positivity)
  -- `log (n + 1) ≤ η n / 2` eventually.
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp
    (isLittleO_log_id_atTop.bound (c := η / 4) (by positivity))
  refine ⟨max (⌈1 / δ⌉₊ + 1) (⌈X⌉₊ + 1), fun n hn => ?_⟩
  have hn1 : ⌈1 / δ⌉₊ + 1 ≤ n := le_of_max_le_left hn
  have hn2 : ⌈X⌉₊ + 1 ≤ n := le_of_max_le_right hn
  have hnpos : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnδ : 1 / δ < n := by
    have := Nat.le_ceil (1 / δ)
    have h2 : ((⌈1 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn1
    push_cast at h2
    linarith
  set m := ⌊p * n⌋₊ with hm
  have hpn : 0 ≤ p * n := by positivity
  have hmle : (m : ℝ) ≤ p * n := Nat.floor_le hpn
  have hmgt : p * n - 1 < m := by have := Nat.lt_floor_add_one (p * n); linarith
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := hmle.trans (by nlinarith)
    exact_mod_cast this
  set x : ℝ := m / n with hx
  -- `|x - p| < δ`.
  have hxp : dist x p < δ := by
    rw [Real.dist_eq, abs_lt]
    have h1 : x ≤ p := by rw [hx, div_le_iff₀ hn']; linarith
    have h2 : p - 1 / n < x := by
      rw [hx, lt_div_iff₀ hn', sub_mul, one_div_mul_cancel hn'.ne']; linarith
    have h3 : 1 / (n : ℝ) < δ := by
      rw [div_lt_iff₀ hn']; rw [div_lt_iff₀ hδ] at hnδ; linarith
    constructor <;> linarith
  have hx01 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, by
    rw [hx, div_le_one hn']; exact_mod_cast hmn⟩
  have hH := hδc x hx01 p ⟨hp0, hp1⟩ hxp
  rw [Real.dist_eq, abs_lt] at hH
  -- `log (n + 1) ≤ η n / 2`.
  have hlog : log ((n : ℝ) + 1) ≤ η / 2 * n := by
    have hXn : X ≤ (n : ℝ) + 1 := by
      have := Nat.le_ceil X
      have h2 : ((⌈X⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn2
      push_cast at h2
      linarith
    have := hX _ hXn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id,
      abs_of_pos (by positivity : (0 : ℝ) < n + 1)] at this
    have h1 : 1 ≤ (n : ℝ) := by exact_mod_cast hnpos
    exact (le_abs_self _).trans (this.trans (by nlinarith))
  -- Keep the term `i = m`.
  have hterm := choose_mul_pow_ge hq hnpos hmn
  have hsum : ((n.choose m * (q - 1) ^ m : ℕ) : ℝ) ≤
      ((∑ i ∈ range (m + 1), n.choose i * (q - 1) ^ i : ℕ) : ℝ) := by
    exact_mod_cast single_le_sum (f := fun i => n.choose i * (q - 1) ^ i)
      (fun i _ => Nat.zero_le _) (self_mem_range_succ m)
  have hcast : ((n.choose m * (q - 1) ^ m : ℕ) : ℝ) = n.choose m * (((q : ℝ) - 1) ^ m) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)]; ring
  refine le_trans ?_ (hcast ▸ hsum |>.trans' hterm)
  rw [le_div_iff₀ (by positivity), ← exp_log (by positivity : (0 : ℝ) < n + 1), ← exp_add]
  refine exp_le_exp.mpr ?_
  change _ ≤ (n : ℝ) * qaryEntropy q x
  have h5 : (n : ℝ) * (qaryEntropy q p - η / 2) ≤ n * qaryEntropy q x :=
    mul_le_mul_of_nonneg_left (by linarith [hH.1]) hn'.le
  linarith

end MathlibExt.InformationTheory.HammingBallVolume
