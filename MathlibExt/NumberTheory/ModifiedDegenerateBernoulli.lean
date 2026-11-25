/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Modified degenerate Bernoulli polynomials

Statements from Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4.

The modified degenerate Bernoulli polynomial of Dolgy, Kim, Kwon and Seo is defined in the paper by
`∑ 𝔅_{n,λ}(x) tⁿ / n! = t (1+λ)^{xt/λ} / ((1+λ)^{t/λ} - 1)`. With the principal branch
`(1+λ)^w = exp (w log (1+λ))` and `c = log (1+λ) / λ` this generating function is
`t e^{cxt} / (e^{ct} - 1)`, whence `𝔅_{n,λ}(x) = c^{n-1} B_n(x)`; this closed form is the definition
below, and `modifiedDegenerateBernoulli_generating_function` proves the paper's generating function
from it. The generating function needs `λ ≠ 0` and `λ ≠ -1` (exactly the condition `c ≠ 0`), which
the statements assume. The Matiyasevich-type identity follows by scaling a convolution of
Bernoulli numbers.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- **Modified degenerate Bernoulli polynomials.** For a complex number $\lambda$, a natural number
$n$ and a complex number $x$, the modified degenerate Bernoulli polynomial is
$\mathfrak{B}_{n,\lambda}(x) = c^{n-1} B_n(x)$, where $c = \log(1+\lambda)/\lambda$ with the
principal branch of the logarithm, $B_n$ is the $n$-th Bernoulli polynomial (with
$B_1(x) = x - 1/2$), and the exponent $n - 1$ is an integer, so that
$\mathfrak{B}_{0,\lambda}(x) = c^{-1}$. At $\lambda = 0$ and $\lambda = -1$, where this quotient is
undefined, $c$ is taken to be $0$, with $0^{-1} = 0$ and $0^0 = 1$.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Section 1 (generating
function of Dolgy, Kim, Kwon and Seo). -/
noncomputable def modifiedDegenerateBernoulli (lam : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  (Complex.log (1 + lam) / lam) ^ ((n : ℤ) - 1) * Polynomial.aeval x (Polynomial.bernoulli n)

/-- **Generating function of the modified degenerate Bernoulli polynomials.** Let $\lambda$ and $x$
be complex numbers such that $c = \log(1+\lambda)/\lambda$ (principal branch) is nonzero, and write
$\mathfrak{B}_{n,\lambda}(x)$ for the modified degenerate Bernoulli polynomials. Then, as formal
power series in $t$ over $\mathbb{C}$,

$$
\Bigl(\sum_{n \ge 0} \mathfrak{B}_{n,\lambda}(x) \frac{t^n}{n!}\Bigr) \bigl(e^{ct} - 1\bigr) =
t\, e^{cxt}.
$$

With $(1+\lambda)^w = e^{w \log(1+\lambda)}$, this says that the series times
$(1+\lambda)^{t/\lambda} - 1$ equals $t\,(1+\lambda)^{xt/\lambda}$.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Section 1. -/
theorem modifiedDegenerateBernoulli_generating_function (lam x : ℂ)
    (h : Complex.log (1 + lam) / lam ≠ 0) :
    PowerSeries.mk (fun n => modifiedDegenerateBernoulli lam n x / n.factorial) *
        (PowerSeries.rescale (Complex.log (1 + lam) / lam) (PowerSeries.exp ℂ) - 1) =
      PowerSeries.X *
        PowerSeries.rescale (Complex.log (1 + lam) / lam * x) (PowerSeries.exp ℂ) := by
  set c := Complex.log (1 + lam) / lam with hc
  have key := congrArg (PowerSeries.rescale c)
    (Polynomial.bernoulli_generating_function (A := ℂ) x)
  rw [map_mul, map_sub, map_one, map_mul, PowerSeries.rescale_X, PowerSeries.rescale_rescale] at key
  have hmk : PowerSeries.mk (fun n => modifiedDegenerateBernoulli lam n x / n.factorial) =
      PowerSeries.C c⁻¹ * PowerSeries.rescale c (PowerSeries.mk fun n =>
        Polynomial.aeval x ((1 / n.factorial : ℚ) • Polynomial.bernoulli n)) := by
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
      PowerSeries.coeff_mk, map_smul, modifiedDegenerateBernoulli, zpow_sub₀ h, zpow_one,
      zpow_natCast, Rat.smul_def]
    push_cast
    field_simp
  rw [hmk, mul_assoc, key, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h, map_one,
    one_mul, mul_comm x c]

/-- **The first modified degenerate Bernoulli polynomial.** For all complex numbers $\lambda$ and
$x$, the modified degenerate Bernoulli polynomial $\mathfrak{B}_{1,\lambda}$ of index $1$ satisfies
$\mathfrak{B}_{1,\lambda}(x) = x - 1/2$.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Section 1. -/
theorem modifiedDegenerateBernoulli_one (lam x : ℂ) :
    modifiedDegenerateBernoulli lam 1 x = x - 1 / 2 := by
  simp [modifiedDegenerateBernoulli, Polynomial.bernoulli_one]

namespace modifiedDegenerateBernoulli_matiyasevich

open Polynomial hiding bernoulli
local notation "B" => Polynomial.bernoulli

-- The functional sending X^i to the ith Bernoulli number.
private noncomputable def moment : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun i => LinearMap.mulRight ℚ (bernoulli i)

private theorem moment_monomial (i : ℕ) (a : ℚ) :
    moment (monomial i a) = a * bernoulli i := by
  simp [moment, lsum_apply, sum_monomial_index, LinearMap.mulRight_apply]

private theorem moment_X_pow (i : ℕ) : moment (X ^ i) = bernoulli i := by
  simpa [← C_mul_X_pow_eq_monomial] using moment_monomial i 1

-- Bernoulli's recurrence identifies the moment of a finite difference.
private theorem moment_difference (p : ℚ[X]) :
    moment (p.comp (1 + X) - p) = p.derivative.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_comp, add_sub_add_comm, map_add, hp, hq, derivative_add, eval_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, ← mul_sub,
      one_add_X_pow_sub_X_pow, C_mul', map_smul, map_sum]
    simp_rw [map_nsmul, moment_X_pow]
    simp only [nsmul_eq_mul, _root_.sum_bernoulli, smul_eq_mul]
    rw [derivative_C_mul, derivative_X_pow]
    cases n with
    | zero => simp
    | succ n => cases n <;> simp

-- Two applications of the hockey-stick identity account for the binomial weight.
private theorem weighted_choose (n l : ℕ) :
    ∑ j ∈ Ico l (n + 1), (n + 1 - j) * j.choose l = (n + 2).choose (l + 2) := by
  calc
    _ = ∑ j ∈ Ico l (n + 1), ∑ _m ∈ Ico j (n + 1), j.choose l := by simp
    _ = ∑ m ∈ Ico l (n + 1), (m + 1).choose (l + 1) := by
      rw [sum_Ico_Ico_comm]
      simp [Ico_add_one_right_eq_Icc, Nat.sum_Icc_choose]
    _ = _ := by
      rw [← Nat.sum_Icc_choose, ← Ico_add_one_right_eq_Icc, ← sum_Ico_add' _ _ _ 1]

private theorem moment_mixed (a b : ℕ) :
    moment (X ^ a * B b) =
      ∑ j ∈ range (b + 1), (b.choose j : ℚ) * bernoulli j * bernoulli (a + (b - j)) := by
  rw [Polynomial.bernoulli, mul_sum, map_sum]
  apply sum_congr rfl
  intro j _
  rw [← C_mul_X_pow_eq_monomial, mul_left_comm, ← pow_add, C_mul', map_smul, moment_X_pow]
  simp [mul_comm]

-- Sum the mixed moments with weight a + 1 along a + b = n.
private theorem sum_mixed (n : ℕ) :
    ∑ p ∈ antidiagonal n, (p.1 + 1 : ℚ) * moment (X ^ p.1 * B p.2) =
      ∑ k ∈ range (n + 1), ((n + 2).choose k : ℚ) * bernoulli k * bernoulli (n - k) := by
  rw [← Finset.Nat.sum_antidiagonal_swap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Prod.swap, moment_mixed, mul_sum]
  let f (j b : ℕ) : ℚ := ((n + 1 - b : ℕ) * b.choose j : ℕ) * (bernoulli j * bernoulli (n - j))
  trans ∑ b ∈ Ico 0 (n + 1), ∑ j ∈ Ico 0 (b + 1), f j b
  · simp only [← range_eq_Ico]
    refine sum_congr rfl fun b hb => sum_congr rfl fun j hj => ?_
    have hb' := mem_range_succ_iff.mp hb
    have hj' := mem_range_succ_iff.mp hj
    simp only [f, Nat.cast_mul, show n + 1 - b = n - b + 1 by omega, Nat.cast_add,
      Nat.cast_one, show n - b + (b - j) = n - j by omega]
    ring
  rw [← sum_Ico_Ico_comm, ← range_eq_Ico, ← sum_range_reflect
    (fun k => ((n + 2).choose k : ℚ) * bernoulli k * bernoulli (n - k)) (n + 1)]
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range_succ_iff.mp hj
  simp only [f, ← sum_mul, ← Nat.cast_sum, weighted_choose, Nat.add_sub_cancel,
    Nat.sub_sub_self hj']
  rw [← Nat.choose_symm (show j + 2 ≤ n + 2 by omega), show n + 2 - (j + 2) = n - j by omega]
  ring

-- Apply the finite-difference formula to one product. The product of the two
-- increments has moment zero when B_(n-1) vanishes.
private theorem product_difference (a b n : ℕ) (hab : a + b = n + 1)
    (hz : bernoulli (n - 1) = 0) :
    (a : ℚ) * (bernoulli (a - 1) * bernoulli b) +
      (b : ℚ) * (bernoulli (b - 1) * bernoulli a) =
      (a : ℚ) * moment (X ^ (a - 1) * B b) + (b : ℚ) * moment (X ^ (b - 1) * B a) := by
  have h := moment_difference (B a * B b)
  rw [mul_comp, bernoulli_comp_one_add_X, bernoulli_comp_one_add_X] at h
  have inc :
      (B a + a • X ^ (a - 1)) * (B b + b • X ^ (b - 1)) - B a * B b =
        a • (X ^ (a - 1) * B b) + b • (X ^ (b - 1) * B a) +
          (a * b) • X ^ ((a - 1) + (b - 1)) := by
    simp only [nsmul_eq_mul, Nat.cast_mul, pow_add]
    ring
  rw [inc] at h
  simp only [map_add, map_nsmul, moment_X_pow] at h
  simp only [nsmul_eq_mul, Nat.cast_mul, derivative_mul,
    derivative_bernoulli, eval_add, eval_mul, eval_natCast, bernoulli_eval_zero] at h
  have cross : (a : ℚ) * b * bernoulli (a - 1 + (b - 1)) = 0 := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    rw [show a - 1 + (b - 1) = n - 1 by omega, hz, mul_zero]
  linear_combination -h + cross

private theorem full_convolution (n : ℕ) (hz : bernoulli (n - 1) = 0) :
    ((n : ℚ) + 2) * ∑ k ∈ range (n + 1), bernoulli k * bernoulli (n - k) =
      2 * ∑ k ∈ range (n + 1), ((n + 2).choose k : ℚ) * bernoulli k * bernoulli (n - k) := by
  have h := sum_congr (s₁ := antidiagonal (n + 1)) rfl fun p hp =>
    product_difference p.1 p.2 n (mem_antidiagonal.mp hp) hz
  simp only [sum_add_distrib] at h
  rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ',
    Finset.Nat.sum_antidiagonal_succ (f := fun p => (p.1 : ℚ) * moment (X ^ (p.1 - 1) * B p.2)),
    Finset.Nat.sum_antidiagonal_succ' (f := fun p => (p.2 : ℚ) * moment (X ^ (p.2 - 1) * B p.1))]
    at h
  simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_add_one, Nat.add_sub_cancel] at h
  rw [← sum_add_distrib, ← Finset.Nat.sum_antidiagonal_swap
    (f := fun p => (p.2 + 1 : ℚ) * moment (X ^ p.2 * B p.1))] at h
  rw [← sum_mixed, two_mul, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => bernoulli i * bernoulli j) n, mul_sum]
  refine Eq.trans (sum_congr rfl fun p hp => ?_) h
  have hp' : (p.1 : ℚ) + p.2 = n := by exact_mod_cast mem_antidiagonal.mp hp
  rw [← hp']
  ring

private theorem split_endpoints (n : ℕ) (hn : 4 ≤ n) (f : ℕ → ℚ) :
    ∑ k ∈ range (n + 1), f k =
      f 0 + f 1 + ∑ k ∈ Icc 2 (n - 2), f k + f (n - 1) + f n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [sum_range_succ, sum_range_succ _ (m + 3),
    ← sum_range_add_sum_Ico f (show 2 ≤ m + 3 by omega)]
  simp [sum_range_succ, show Ico 2 (m + 3) = Icc 2 (m + 2) from Ico_add_one_right_eq_Icc 2 (m + 2)]

private theorem rational_identity (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℚ) + 2) * ∑ k ∈ Icc 2 (n - 2), bernoulli k * bernoulli (n - k) =
      2 * ∑ k ∈ Icc 2 (n - 2), ((n + 2).choose k : ℚ) * bernoulli k * bernoulli (n - k) +
        n * (n + 1) * bernoulli n := by
  rcases n.even_or_odd with ⟨m, hm⟩ | ho
  · have hz : bernoulli (n - 1) = 0 :=
      bernoulli_eq_zero_of_odd ⟨m - 1, by omega⟩ (by omega)
    have h := full_convolution n hz
    rw [split_endpoints n hn, split_endpoints n hn] at h
    simp only [_root_.bernoulli_zero, Nat.sub_zero, Nat.sub_self, hz, mul_zero, zero_mul,
      Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one, add_zero] at h
    rw [show (n + 2).choose n = (n + 2).choose 2 by
      simpa using (Nat.choose_symm (show 2 ≤ n + 2 by omega)), Nat.cast_choose_two] at h
    push_cast at h
    linear_combination h
  · have hz := bernoulli_eq_zero_of_odd ho (by omega)
    have term (k : ℕ) (hk : k ∈ Icc 2 (n - 2)) : bernoulli k * bernoulli (n - k) = 0 := by
      obtain ⟨hk₁, hk₂⟩ := mem_Icc.mp hk
      rcases k.even_or_odd with ⟨i, hi⟩ | hk'
      · obtain ⟨m, hm⟩ := ho
        rw [bernoulli_eq_zero_of_odd (n := n - k) ⟨m - i, by omega⟩ (by omega), mul_zero]
      · rw [bernoulli_eq_zero_of_odd hk' (by omega), zero_mul]
    rw [sum_eq_zero term, sum_eq_zero (fun k hk => by rw [mul_assoc, term k hk, mul_zero]), hz]
    ring

end modifiedDegenerateBernoulli_matiyasevich

/-- **Matiyasevich-type identity for modified degenerate Bernoulli numbers.** Let $n \ge 4$, let
$\lambda$ be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$, and write
$\mathfrak{B}_{k,\lambda} = \mathfrak{B}_{k,\lambda}(0)$ for the value at $0$ of the modified
degenerate Bernoulli polynomial $\mathfrak{B}_{k,\lambda}(x)$. Then

$$
(n+2) \sum_{k=2}^{n-2} \mathfrak{B}_{k,\lambda} \mathfrak{B}_{n-k,\lambda} =
2 \sum_{k=2}^{n-2} \binom{n+2}{k} \mathfrak{B}_{k,\lambda} \mathfrak{B}_{n-k,\lambda} +
\frac{\lambda}{\log(1+\lambda)}\, n(n+1)\, \mathfrak{B}_{n,\lambda},
$$

where $\log$ is the principal branch.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Corollary 2, equation
(matiyasevichD) (`jis-2024-24.5.4-cor-2`). -/
theorem modifiedDegenerateBernoulli_matiyasevich (n : ℕ) (hn : 4 ≤ n) (lam : ℂ)
    (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ((n : ℂ) + 2) * ∑ k ∈ Icc 2 (n - 2),
        modifiedDegenerateBernoulli lam k 0 * modifiedDegenerateBernoulli lam (n - k) 0 =
      2 * ∑ k ∈ Icc 2 (n - 2), ((n + 2).choose k : ℂ) *
          modifiedDegenerateBernoulli lam k 0 * modifiedDegenerateBernoulli lam (n - k) 0 +
        lam / Complex.log (1 + lam) * (n * (n + 1)) * modifiedDegenerateBernoulli lam n 0 := by
  let c := Complex.log (1 + lam) / lam
  have hc : c ≠ 0 := by
    apply div_ne_zero _ hlam
    intro hz
    have h := Complex.exp_log (x := 1 + lam) (by intro h; apply hlam1; linear_combination h)
    rw [hz, Complex.exp_zero] at h
    exact hlam (by linear_combination -h)
  have at_zero (k : ℕ) :
      modifiedDegenerateBernoulli lam k 0 = c ^ ((k : ℤ) - 1) * (bernoulli k : ℂ) := by
    simp [c, modifiedDegenerateBernoulli, Polynomial.aeval_def, Polynomial.eval₂_at_zero,
      Polynomial.coeff_bernoulli]
  have product (k : ℕ) (hk : k ∈ Icc 2 (n - 2)) :
      modifiedDegenerateBernoulli lam k 0 * modifiedDegenerateBernoulli lam (n - k) 0 =
        c ^ ((n : ℤ) - 2) * ((bernoulli k : ℂ) * (bernoulli (n - k) : ℂ)) := by
    have hkn := (mem_Icc.mp hk).2.trans (Nat.sub_le n 2)
    rw [at_zero, at_zero, mul_mul_mul_comm, ← zpow_add₀ hc, Nat.cast_sub hkn]
    congr 2
    ring
  have scaled_sum (w : ℕ → ℂ) :
      ∑ k ∈ Icc 2 (n - 2), w k * modifiedDegenerateBernoulli lam k 0 *
          modifiedDegenerateBernoulli lam (n - k) 0 =
        c ^ ((n : ℤ) - 2) * ∑ k ∈ Icc 2 (n - 2),
          w k * (bernoulli k : ℂ) * (bernoulli (n - k) : ℂ) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [mul_assoc, product k hk]
    ring
  have last : lam / Complex.log (1 + lam) * (n * (n + 1)) * modifiedDegenerateBernoulli lam n 0 =
      c ^ ((n : ℤ) - 2) * (n * (n + 1) * (bernoulli n : ℂ)) := by
    rw [at_zero, show lam / Complex.log (1 + lam) = c ^ (-1 : ℤ) by simp [c]]
    rw [mul_mul_mul_comm, ← zpow_add₀ hc]
    congr 2
    ring
  have h : ((n : ℂ) + 2) * ∑ k ∈ Icc 2 (n - 2), (bernoulli k : ℂ) * (bernoulli (n - k) : ℂ) =
      2 * ∑ k ∈ Icc 2 (n - 2), ((n + 2).choose k : ℂ) * (bernoulli k : ℂ) *
        (bernoulli (n - k) : ℂ) + n * (n + 1) * (bernoulli n : ℂ) := by
    exact_mod_cast modifiedDegenerateBernoulli_matiyasevich.rational_identity n hn
  rw [show ∑ k ∈ Icc 2 (n - 2), modifiedDegenerateBernoulli lam k 0 *
      modifiedDegenerateBernoulli lam (n - k) 0 = _ by simpa using scaled_sum (fun _ => 1),
    scaled_sum (fun k => ((n + 2).choose k : ℂ)), last]
  linear_combination c ^ ((n : ℤ) - 2) * h

end

end MetaMathlibExt
