/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring

/-!
# Trinomial coefficients

The trinomial coefficient in row `n` and column `k` is the coefficient of `X ^ k` in
`(1 + X + X ^ 2) ^ n`. Consequently it is zero when `k > 2 * n`. Sun's generalized central
trinomial coefficient `T_n(b, c)` is the coefficient of `X ^ n` in `(X ^ 2 + b X + c) ^ n`.

Sources:

* Emanuele Munarini, *Shifting Property for Riordan, Sheffer and Connection Constants
  Matrices*, <https://cs.uwaterloo.ca/journals/JIS/VOL20/Munarini/muna4.tex>.
* Wen-jin Woan, *The Lagrange Inversion Formula and Divisibility Properties*,
  <https://cs.uwaterloo.ca/journals/JIS/VOL10/Woan/woan655.tex>.
* Chahinaze Djadi and Hacène Belbachir, *Congruence Properties for the Delannoy Triangle
  Coefficients*, Journal of Integer Sequences 29 (2026), Article 26.5.2, Section 4.

JIS concept: `jis_sem_ad18425839072c449c4e8a69`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Trinomial coefficient.** For natural numbers $n$ and $k$, the trinomial coefficient in row
$n$ and column $k$ is the coefficient of $X^k$ in the polynomial $(1 + X + X^2)^n$. -/
noncomputable def trinomialCoefficient (n k : ℕ) : ℕ :=
  ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) ^ n).coeff k

/-- The trinomial coefficient `T(0, 0)` is `1`. -/
theorem trinomialCoefficient_zero_zero : trinomialCoefficient 0 0 = 1 := by
  simp [trinomialCoefficient]

/-- The trinomial coefficient `T(1, 1)` is `1`. -/
theorem trinomialCoefficient_one_one : trinomialCoefficient 1 1 = 1 := by
  unfold trinomialCoefficient
  simp [pow_one, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
    Polynomial.coeff_X_pow]

/-- **Absorption identity for trinomial coefficients.** Write $\binom{n}{k}_2$ for the
trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$. For natural numbers $n \ge 1$
and $k$, $\frac{k}{n} \binom{n}{k}_2 = \binom{n-1}{k-1}_2 + 2 \binom{n-1}{k-2}_2$, where a term
whose lower index is negative is read as $0$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Lemma 31 (`jis-2025-25.3.5-lem-31`). -/
public theorem trinomialCoefficient_absorption (n k : ℕ) (hn : 0 < n) :
    (k : ℚ) / n * trinomialCoefficient n k =
      (if 1 ≤ k then (trinomialCoefficient (n - 1) (k - 1) : ℚ) else 0) +
        2 * (if 2 ≤ k then (trinomialCoefficient (n - 1) (k - 2) : ℚ) else 0) :=
  open Polynomial in
  by
    let p : Polynomial ℕ := 1 + X + X ^ 2
    -- Multiplying the derivative by `X` lets us compare coefficients at `k`.
    have hderiv : X * derivative (p ^ n) =
        C n * (X * p ^ (n - 1) + C 2 * (X ^ 2 * p ^ (n - 1))) := by
      rw [derivative_pow, Nat.cast_id, show derivative p = 1 + C 2 * X by
        simp only [p, derivative_add, derivative_one, derivative_X, zero_add, derivative_X_sq]]
      ring
    have hcoeff : (X * derivative (p ^ n)).coeff k = k * (p ^ n).coeff k := by
      cases k with
      | zero => simp
      | succ k => simp [coeff_derivative, mul_comm]
    have hshift : (X * p ^ (n - 1)).coeff k =
        if 1 ≤ k then (p ^ (n - 1)).coeff (k - 1) else 0 := by
      simpa only [pow_one] using coeff_X_pow_mul' (p ^ (n - 1)) 1 k
    have hnat : k * trinomialCoefficient n k =
        n * ((if 1 ≤ k then trinomialCoefficient (n - 1) (k - 1) else 0) +
          2 * (if 2 ≤ k then trinomialCoefficient (n - 1) (k - 2) else 0)) := by
      change k * (p ^ n).coeff k = _
      rw [← hcoeff, hderiv, coeff_C_mul, coeff_add, coeff_C_mul, hshift, coeff_X_pow_mul']
      rfl
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [div_mul_eq_mul_div₀, div_eq_iff hnq, mul_comm _ (n : ℚ)]
    exact_mod_cast hnat

/-- Sun's generalized central trinomial coefficient
`T_n(b, c) = [xⁿ] (x² + b x + c)ⁿ`.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Journal of Integer Sequences 29 (2026),
Article 26.5.2, Section 4 (definition quoted from
Z.-W. Sun, Sci. China Math. 57 (2014)). -/
noncomputable def generalizedCentralTrinomial (b c : ℤ) (n : ℕ) : ℤ :=
  ((Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) ^ n).coeff n

/-- `T_0(b, c) = 1`.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Section 4. -/
theorem generalizedCentralTrinomial_zero (b c : ℤ) :
    generalizedCentralTrinomial b c 0 = 1 := by
  simp [generalizedCentralTrinomial]

/-- `T_1(b, c) = b`.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Section 4. -/
theorem generalizedCentralTrinomial_one (b c : ℤ) :
    generalizedCentralTrinomial b c 1 = b := by
  rw [generalizedCentralTrinomial, pow_one, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  simp

/-- Binomial-sum form of Sun's generalized central trinomial coefficient, before
folding the two binomials: `T_n(b, c) = ∑_{k ≤ n} C(n, k) C(n - k, k) b^(n - 2k) cᵏ`.

Source: Z.-W. Sun, *Congruences involving generalized central trinomial coefficients*,
Sci. China Math. 57 (2014), introduction; quoted in Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle Coefficients", Journal of Integer
Sequences 29 (2026), Article 26.5.2, Section 4. -/
theorem generalizedCentralTrinomial_eq_sum_choose_choose_sub (b c : ℤ) (n : ℕ) :
    generalizedCentralTrinomial b c n =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k * (n - k).choose k : ℤ) * b ^ (n - 2 * k) * c ^ k := by
  have hbase : (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c : Polynomial ℤ) =
      Polynomial.C c + Polynomial.X * (Polynomial.X + Polynomial.C b) := by
    ring
  rw [generalizedCentralTrinomial, hbase, add_pow, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Polynomial.coeff_mul_natCast, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul']
  simp only [Nat.sub_le, ite_true]
  rw [Polynomial.coeff_X_add_C_pow, Nat.sub_sub_self hkn,
    show n - k - k = n - 2 * k by omega]
  ring

/-- Sun's binomial-sum formula for the generalized central trinomial coefficient:
`T_n(b, c) = ∑_{k=0}^{⌊n/2⌋} C(n, 2k) C(2k, k) b^(n - 2k) cᵏ`.

Source: Z.-W. Sun, *Congruences involving generalized central trinomial coefficients*,
Sci. China Math. 57 (2014), introduction; quoted in Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle Coefficients", Journal of Integer
Sequences 29 (2026), Article 26.5.2, Section 4. -/
theorem generalizedCentralTrinomial_eq_sum (b c : ℤ) (n : ℕ) :
    generalizedCentralTrinomial b c n =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * k) * (2 * k).choose k : ℤ) * b ^ (n - 2 * k) * c ^ k := by
  rw [generalizedCentralTrinomial_eq_sum_choose_choose_sub]
  calc
    (∑ k ∈ Finset.range (n + 1),
        (n.choose k * (n - k).choose k : ℤ) * b ^ (n - 2 * k) * c ^ k) =
        ∑ k ∈ Finset.range (n / 2 + 1),
          (n.choose k * (n - k).choose k : ℤ) * b ^ (n - 2 * k) * c ^ k := by
      refine (Finset.sum_subset (fun k hk => ?_) fun k hk hnot => ?_).symm
      · simp only [Finset.mem_range] at hk ⊢
        omega
      · simp only [Finset.mem_range] at hk hnot
        rw [Nat.choose_eq_zero_of_lt (by omega : n - k < k)]
        simp
    _ = ∑ k ∈ Finset.range (n / 2 + 1),
          (n.choose (2 * k) * (2 * k).choose k : ℤ) * b ^ (n - 2 * k) * c ^ k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hchoose := Nat.choose_mul (n := n) (k := 2 * k) (s := k) (by omega)
      rw [show 2 * k - k = k by omega] at hchoose
      rw [← Nat.cast_mul, ← Nat.cast_mul, hchoose]

end

end MetaMathlibExt
