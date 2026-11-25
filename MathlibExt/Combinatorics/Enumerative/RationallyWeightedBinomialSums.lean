/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.NumberTheory.Harmonic.Defs
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import MathlibExt.NumberTheory.BinomialFibonacciConvolution
import MathlibExt.NumberTheory.DilcherFiniteMultipleHarmonic

/-!
# Rationally weighted binomial sums

For every natural number `n`, `∑_{k=0}^n binom(n, k) / (k + 1) = (2^{n+1} - 1) / (n + 1)` in `ℚ`
(`MetaMathlibExt.sum_choose_div_succ`).

The alternating binomial sum with reciprocal weights equals the harmonic number
(Finkel's identity). The inverse-square sum equals the sum of the harmonic
numbers divided by their indices, by Dilcher's identity at exponent two and
grouping by the second entry.

Expanding a power in falling factorials gives a formula for the power-weighted binomial sum
of Fibonacci numbers at every exponent. The first four powers give explicit closed forms.

## Proof of Epsteen's identity

The absorption identity `(n + 1) binom(n, k) = binom(n + 1, k + 1) (k + 1)`
(`Nat.add_one_mul_choose_eq`) turns each term into `binom(n + 1, k + 1) / (n + 1)`. The remaining
sum `∑_{k=0}^n binom(n + 1, k + 1)` is the row sum `∑_{j=0}^{n+1} binom(n + 1, j) = 2^{n+1}`
(`Nat.sum_range_choose`) without its term `binom(n + 1, 0) = 1`.

## Implementation notes

`sum_choose_div_succ` keeps the full name and the statement it had as a wanted theorem in
`WantedExt.Combinatorics.Enumerative.RationallyWeightedBinomialSumsWanted`.
-/

namespace MetaMathlibExt

/-- **Epsteen's identity.** For every natural number $n$,

$$\sum_{k=0}^{n} \frac{1}{k+1} \binom{n}{k} = \frac{2^{n+1} - 1}{n+1}.$$

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem sum_choose_div_succ (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) / (k + 1) = (2 ^ (n + 1) - 1) / (n + 1) := by
  -- Absorption: each term is `binom(n + 1, k + 1) / (n + 1)`.
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (n.choose k : ℚ) / (k + 1) = ((n + 1).choose (k + 1) : ℚ) / (n + 1) := by
    intro k _
    rw [div_eq_div_iff (by positivity) (by positivity)]
    have h : ((n : ℚ) + 1) * n.choose k = (n + 1).choose (k + 1) * ((k : ℚ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n k
    linarith
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  congr 1
  -- Row `n + 1` of Pascal's triangle sums to `2 ^ (n + 1)`; drop its first entry `1`.
  have hrow := Nat.sum_range_choose (n + 1)
  rw [Finset.sum_range_succ', Nat.choose_zero_right] at hrow
  have hrow' : (∑ k ∈ Finset.range (n + 1), ((n + 1).choose (k + 1) : ℚ)) + 1 = 2 ^ (n + 1) := by
    exact_mod_cast hrow
  linarith

/-- **Greenstreet's identity.** For every natural number $N$,

$$\sum_{k=1}^{N} (-1)^k \binom{N}{k} 2^{N-k} k^2 = N^2 - 2N.$$

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.3. -/
public theorem sum_neg_one_pow_choose_two_pow_mul_sq (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (-1 : ℤ) ^ k * (N.choose k : ℤ) * 2 ^ (N - k) * (k : ℤ) ^ 2 =
      (N : ℤ) ^ 2 - 2 * N := by
  have sq (k : ℕ) : k * (k - 1) + k = k ^ 2 := by
    cases k <;> simp [pow_two, Nat.mul_succ]
  -- Combine the first two factorial moments of the Bernstein polynomials.
  have moment :
      (∑ k ∈ Finset.range (N + 1), (k ^ 2) • bernsteinPolynomial ℤ N k) =
        (N * (N - 1)) • (Polynomial.X : Polynomial ℤ) ^ 2 + N • Polynomial.X := by
    simp_rw [← sq, add_nsmul, Finset.sum_add_distrib, bernsteinPolynomial.sum_mul_smul,
      bernsteinPolynomial.sum_smul]
  -- At X = -1, the Bernstein weights have factors (-1)^k and 2^(N-k).
  have h := congrArg (Polynomial.evalRingHom (-1 : ℤ)) moment
  simp only [map_sum, map_add, map_nsmul, map_pow] at h
  simp only [Polynomial.coe_evalRingHom, bernsteinPolynomial, Polynomial.eval_mul,
    Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_one, show (1 : ℤ) - (-1) = 2 by decide, nsmul_eq_mul, Nat.cast_pow] at h
  -- The k = 0 term vanishes, including when N = 0.
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)] at h
  simp only [Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, zero_add,
    Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc] at h
  have hN : ((N * (N - 1) : ℕ) : ℤ) + (N : ℤ) = (N : ℤ) ^ 2 := by
    exact_mod_cast sq N
  calc
    _ = _ := (Finset.sum_congr rfl fun k _ => by ac_rfl).trans h
    _ = ((N * (N - 1) : ℕ) : ℤ) - N := by ring
    _ = _ := by rw [← hN]; ring

-- The shifted row that Pascal's identity adds in the harmonic recurrence.
private theorem sum_neg_one_pow_choose_div_succ (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * n.choose j / (j + 1) =
      ((n : ℚ) + 1)⁻¹ := by
  -- The full alternating row vanishes by the binomial theorem at -1 and 1.
  have hrow :
      ∑ j ∈ Finset.range (n + 2), (-1 : ℚ) ^ j * (n + 1).choose j = 0 := by
    simpa [zero_pow (Nat.succ_ne_zero n)] using (add_pow (-1 : ℚ) 1 (n + 1)).symm
  have htail :
      ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * (n + 1).choose (j + 1) = 1 := by
    rw [Finset.sum_range_succ'] at hrow
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, pow_succ,
      mul_neg_one, neg_mul, Finset.sum_neg_distrib] at hrow
    linarith
  calc
    _ = ∑ j ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ j * (n + 1).choose (j + 1) / (n + 1) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hchoose :
          (n.choose j : ℚ) / (j + 1) = ((n + 1).choose (j + 1) : ℚ) / (n + 1) := by
        rw [div_eq_div_iff (by positivity) (by positivity)]
        have h : ((n : ℚ) + 1) * n.choose j =
            (n + 1).choose (j + 1) * ((j : ℚ) + 1) := by
          exact_mod_cast Nat.add_one_mul_choose_eq n j
        simpa only [mul_comm] using h
      rw [mul_div_assoc, hchoose, ← mul_div_assoc]
    _ = _ := by rw [← Finset.sum_div, htail, one_div]

/-- **Finkel's identity.** For every natural number $n$, with $H_n = \sum_{j=1}^{n} 1/j$ the
$n$-th harmonic number,

$$\sum_{k=1}^{n} (-1)^{k-1} \frac{1}{k} \binom{n}{k} = H_n.$$

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem sum_neg_one_pow_choose_div_eq_harmonic (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (k - 1) * n.choose k / k = harmonic n := by
  -- Reindex by `k = j + 1` so Pascal's identity applies to each coefficient.
  simp only [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Nat.add_comm 1]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ, ← ih]
    calc
      _ = (∑ j ∈ Finset.range (n + 1),
            (-1 : ℚ) ^ j * n.choose (j + 1) / (j + 1)) +
          ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * n.choose j / (j + 1) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.choose_succ_succ', Nat.cast_add, mul_add, add_div, add_comm]
      _ = _ := by
        rw [Finset.sum_range_succ, sum_neg_one_pow_choose_div_succ]
        simp [Nat.cast_add, Nat.cast_one]

/-- **Alternating binomial sum with inverse-square weights.** For every natural number $n$, with
$H_k = \sum_{j=1}^{k} 1/j$ the $k$-th harmonic number,

$$\sum_{k=1}^{n} (-1)^{k-1} \frac{1}{k^2} \binom{n}{k} = \sum_{k=1}^{n} \frac{H_k}{k}.$$

This is the case $x = -1$ of identity (3.6) of the source.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem sum_neg_one_pow_choose_div_sq_eq_sum_harmonic (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2 =
      ∑ k ∈ Finset.Icc 1 n, harmonic k / k := by
  classical
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp
  let pairWeight (i j : ℕ) : ℚ := if i ≤ j then (↑(i + 1) : ℚ)⁻¹ / ↑(j + 1) else 0
  have inner (j : Fin n) :
      (∑ i : Fin n, pairWeight i j) = harmonic (j.val + 1) / ↑(j.val + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => pairWeight i j), harmonic, Finset.sum_div]
    simp only [pairWeight, ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    _ = ∑ js ∈ Finset.univ.filter (fun js : Fin 2 → Fin n => Monotone (fun i => (js i).val)),
          (∏ i, ((js i).val + 1 : ℚ))⁻¹ := by
      simpa only [mul_comm] using dilcher_finite_multiple_harmonic_identity_general 2 n hn
    _ = ∑ p : Fin n × Fin n, pairWeight p.1 p.2 := by
      rw [Finset.sum_filter]
      refine Fintype.sum_equiv (finTwoArrowEquiv (Fin n)) _ _ fun js => ?_
      simp [pairWeight, Fin.monotone_iff_le_succ, Fin.forall_fin_one, Fin.prod_univ_two,
        finTwoArrowEquiv_apply, div_eq_mul_inv, mul_comm]
    _ = ∑ j : Fin n, harmonic (j.val + 1) / ↑(j.val + 1) := by
      rw [Fintype.sum_prod_type_right]
      exact Finset.sum_congr rfl fun j _ => inner j
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun j => harmonic (j + 1) / ↑(j + 1)),
        ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp [Nat.add_comm]

private noncomputable def weightedBinomialSum (x : ℝ) (p n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (n.choose k : ℝ) * x ^ k / (k : ℝ) ^ p

private theorem weightedBinomialSum_zero_pow (x : ℝ) (n : ℕ) :
    weightedBinomialSum x 0 n = (1 + x) ^ n - 1 := by
  have h := add_pow x (1 : ℝ) n
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n),
    Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc] at h
  rw [weightedBinomialSum, eq_sub_iff_add_eq]
  simpa only [one_pow, mul_one, pow_zero, div_one, Nat.choose_zero_right, Nat.cast_one,
    mul_comm, add_comm] using h.symm

-- Pascal's identity and absorption lower the denominator exponent by one.
private theorem weightedBinomialSum_succ (x : ℝ) (p n : ℕ) :
    weightedBinomialSum x (p + 1) (n + 1) =
      weightedBinomialSum x (p + 1) n + weightedBinomialSum x p (n + 1) / (n + 1 : ℕ) := by
  -- Extend the old row by its zero coefficient at `n + 1`.
  have hext : (∑ k ∈ Finset.Icc 1 (n + 1), (n.choose k : ℝ) * x ^ k / (k : ℝ) ^ (p + 1)) =
      weightedBinomialSum x (p + 1) n := by
    rw [Finset.sum_Icc_succ_top (Nat.succ_pos n)]
    simp [weightedBinomialSum]
  rw [← hext, weightedBinomialSum, weightedBinomialSum, Finset.sum_div,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : 0 < k := (Finset.mem_Icc.mp hk).1
  nth_rw 1 [Nat.choose_succ_left n k hk']
  rw [Nat.cast_add, add_mul, add_div, add_comm]
  congr 1
  have habsorb : (n.choose (k - 1) : ℝ) / k = ((n + 1).choose k : ℝ) / (n + 1 : ℕ) := by
    rw [div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk'))
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))]
    have h := Nat.add_one_mul_choose_eq n (k - 1)
    rw [Nat.sub_add_cancel hk'] at h
    exact_mod_cast (Nat.mul_comm _ _).trans h
  calc
    _ = (n.choose (k - 1) : ℝ) / k * (x ^ k / (k : ℝ) ^ p) := by
      simp only [pow_succ, div_eq_mul_inv, mul_inv_rev]
      ac_rfl
    _ = _ := by
      rw [habsorb]
      simp only [div_eq_mul_inv]
      ac_rfl

private theorem weightedBinomialSum_succ_pow (x : ℝ) (p n : ℕ) :
    weightedBinomialSum x (p + 1) n =
      ∑ k ∈ Finset.Icc 1 n, weightedBinomialSum x p k / k := by
  induction n with
  | zero => simp [weightedBinomialSum]
  | succ n ih =>
    rw [weightedBinomialSum_succ, ih, Finset.sum_Icc_succ_top (Nat.succ_pos n)]

/-- **Binomial sums weighted by $x^k/k^2$.** For every natural number $n$ and every real number
$x$,

$$\sum_{k=1}^{n} \binom{n}{k} \frac{x^k}{k^2} =
\sum_{k=1}^{n} \frac{1}{k} \sum_{j=1}^{k} \frac{(1+x)^j}{j} -
\sum_{k=1}^{n} \frac{1}{k} \sum_{j=1}^{k} \frac{1}{j}.$$

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem sum_choose_mul_pow_div_sq (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.Icc 1 n, (n.choose k : ℝ) * x ^ k / (k : ℝ) ^ 2 =
      ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) * ∑ j ∈ Finset.Icc 1 k, (1 + x) ^ j / j -
        ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) * ∑ j ∈ Finset.Icc 1 k, 1 / (j : ℝ) := by
  change weightedBinomialSum x 2 n = _
  rw [weightedBinomialSum_succ_pow x 1 n]
  simp_rw [weightedBinomialSum_succ_pow x 0, weightedBinomialSum_zero_pow]
  simp only [Finset.sum_sub_distrib, div_eq_inv_mul, mul_one, mul_sub]

-- Absorbing one falling-factorial factor lowers the binomial row and shifts the Fibonacci index.
private theorem sum_descFactorial_mul_choose_mul_fib_add (n i m : ℕ) :
    ∑ k ∈ Finset.range (n + 1), k.descFactorial i * n.choose k * Nat.fib (k + m) =
      n.descFactorial i * Nat.fib (2 * n + m - i) := by
  induction i generalizing n m with
  | zero => simpa using Nat.sum_range_choose_mul_fib_add n m
  | succ i ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [Finset.sum_range_succ', Nat.zero_descFactorial_succ, zero_mul, zero_mul, add_zero,
        Nat.succ_descFactorial_succ, mul_assoc,
        show 2 * (n + 1) + m - (i + 1) = 2 * n + (m + 1) - i by omega,
        ← ih n (m + 1), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.succ_descFactorial_succ, show k + 1 + m = k + (m + 1) by omega]
      calc
        _ = ((n + 1).choose (k + 1) * (k + 1)) * k.descFactorial i *
            Nat.fib (k + (m + 1)) := by ac_rfl
        _ = _ := by
          rw [← Nat.add_one_mul_choose_eq]
          ac_rfl

/-- **Power-weighted binomial sums of Fibonacci numbers.** Let $F_n$ denote the Fibonacci numbers,
$S(r, i)$ the Stirling numbers of the second kind and $(N)_i = N(N-1) \cdots (N-i+1)$ the falling
factorial, with $(N)_0 = 1$. For all natural numbers $N$ and $r$,
$$\sum_{k=0}^{N} k^r \binom{N}{k} F_k = \sum_{i=0}^{r} S(r, i) \, (N)_i \, F_{2N-i},$$
where the terms with $i > N$ vanish because $(N)_i = 0$.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.5. -/
public theorem sum_pow_mul_choose_mul_fib (N r : ℕ) :
    ∑ k ∈ Finset.range (N + 1), k ^ r * N.choose k * Nat.fib k =
      ∑ i ∈ Finset.range (r + 1),
        Nat.stirlingSecond r i * N.descFactorial i * Nat.fib (2 * N - i) := by
  simp_rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa only [Finset.mul_sum, mul_assoc, Nat.add_zero] using
    congrArg (Nat.stirlingSecond r i * ·) (sum_descFactorial_mul_choose_mul_fib_add N i 0)

/-- **Weighted binomial Fibonacci sums for the powers one to four.** Let $F_n$ denote the Fibonacci
numbers. For every natural number $N$,
$$\sum_{k=1}^{N} k \binom{N}{k} F_k = N F_{2N-1},$$
$$\sum_{k=1}^{N} k^2 \binom{N}{k} F_k = N F_{2N-1} + N(N-1) F_{2N-2},$$
$$\sum_{k=1}^{N} k^3 \binom{N}{k} F_k = N F_{2N-1} + 3N(N-1) F_{2N-2} + N(N-1)(N-2) F_{2N-3},$$
$$\sum_{k=1}^{N} k^4 \binom{N}{k} F_k = N F_{2N-1} + 7N(N-1) F_{2N-2} +
6N(N-1)(N-2) F_{2N-3} + N(N-1)(N-2)(N-3) F_{2N-4}.$$

Every term with a negative Fibonacci index has coefficient zero.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.6. -/
public theorem sum_pow_mul_choose_mul_fib_small (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, k * N.choose k * Nat.fib k = N * Nat.fib (2 * N - 1)) ∧
    (∑ k ∈ Finset.Icc 1 N, k ^ 2 * N.choose k * Nat.fib k =
      N * Nat.fib (2 * N - 1) + N * (N - 1) * Nat.fib (2 * N - 2)) ∧
    (∑ k ∈ Finset.Icc 1 N, k ^ 3 * N.choose k * Nat.fib k =
      N * Nat.fib (2 * N - 1) + 3 * N * (N - 1) * Nat.fib (2 * N - 2) +
        N * (N - 1) * (N - 2) * Nat.fib (2 * N - 3)) ∧
    ∑ k ∈ Finset.Icc 1 N, k ^ 4 * N.choose k * Nat.fib k =
      N * Nat.fib (2 * N - 1) + 7 * N * (N - 1) * Nat.fib (2 * N - 2) +
        6 * N * (N - 1) * (N - 2) * Nat.fib (2 * N - 3) +
        N * (N - 1) * (N - 2) * (N - 3) * Nat.fib (2 * N - 4) := by
  have moment := sum_pow_mul_choose_mul_fib N
  -- Split off the zero-index term before evaluating the four Stirling sums.
  simp_rw [Finset.range_eq_Ico (N + 1), Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)] at moment
  simp only [Nat.fib_zero, mul_zero, zero_add, Nat.succ_eq_add_one,
    Finset.Ico_add_one_right_eq_Icc] at moment
  simpa [Finset.sum_range_succ, Nat.stirlingSecond, Nat.descFactorial, mul_assoc, mul_comm,
    mul_left_comm] using (show _ ∧ _ ∧ _ ∧ _ from ⟨moment 1, moment 2, moment 3, moment 4⟩)

namespace sum_pow_mul_choose_mul_secondOrder

-- One binomial step applies the recurrence once, advancing the sequence by two.
private theorem binomial_shift (a b : ℝ) (W : ℕ → ℝ)
    (hW : ∀ n, W (n + 2) = a * W (n + 1) + b * W n) (n m : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (a ^ k * b ^ (n - k) * W (k + m)) =
      W (2 * n + m) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_choose_succ_mul (fun k j ↦ a ^ k * b ^ j * W (k + m)) n,
      ← Finset.sum_add_distrib, show 2 * (n + 1) + m = 2 * n + (m + 2) by omega, ← ih]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ b, pow_succ a,
      show k + (m + 2) = (k + m) + 2 by omega, hW, show k + 1 + m = k + m + 1 by omega]
    ring

-- Each falling-factorial factor lowers the binomial row and contributes a factor of a.
private theorem factorial_moment (a b : ℝ) (W : ℕ → ℝ)
    (hW : ∀ n, W (n + 2) = a * W (n + 1) + b * W n) (n i m : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (k.descFactorial i : ℝ) * n.choose k * a ^ k * b ^ (n - k) * W (k + m) =
      (n.descFactorial i : ℝ) * a ^ i * W (2 * n + m - i) := by
  induction i generalizing n m with
  | zero => simpa [mul_assoc] using binomial_shift a b W hW n m
  | succ i ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [Finset.sum_range_succ']
      simp only [Nat.zero_descFactorial_succ, Nat.cast_zero, zero_mul, add_zero]
      calc
        _ = ((n : ℝ) + 1) * a * ∑ k ∈ Finset.range (n + 1),
            (k.descFactorial i : ℝ) * n.choose k * a ^ k * b ^ (n - k) * W (k + (m + 1)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          have h : ((n : ℝ) + 1) * n.choose k = ((n + 1).choose (k + 1) : ℝ) * (k + 1) := by
            exact_mod_cast Nat.add_one_mul_choose_eq n k
          rw [Nat.succ_descFactorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ,
            Nat.add_sub_add_right, show k + 1 + m = k + (m + 1) by omega]
          linear_combination
            -(k.descFactorial i : ℝ) * a ^ k * a * b ^ (n - k) * W (k + (m + 1)) * h
        _ = _ := by
          rw [ih, Nat.succ_descFactorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ,
            show 2 * (n + 1) + m - (i + 1) = 2 * n + (m + 1) - i by omega]
          ring

end sum_pow_mul_choose_mul_secondOrder

/-- **Power-weighted binomial sums of a second-order linear recurrence.** Let $a$ and $b$ be real
numbers and let $(W_n)_{n \ge 0}$ be a real sequence with $W_{n+2} = a W_{n+1} + b W_n$ for all
$n \ge 0$. Write $S(r, i)$ for the Stirling numbers of the second kind and
$(N)_i = N(N-1) \cdots (N-i+1)$ for the falling factorial, with $(N)_0 = 1$. Then for all natural
numbers $N$ and $r$, with the convention $0^0 = 1$,
$$\sum_{k=0}^{N} k^r \binom{N}{k} a^k b^{N-k} W_k = \sum_{i=0}^{r} S(r, i) (N)_i a^i W_{2N-i},$$
where the terms with $i > N$ vanish because $(N)_i = 0$.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.5. -/
public theorem sum_pow_mul_choose_mul_secondOrder (a b : ℝ) (W : ℕ → ℝ)
    (hW : ∀ n, W (n + 2) = a * W (n + 1) + b * W n) (N r : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (k : ℝ) ^ r * N.choose k * a ^ k * b ^ (N - k) * W k =
      ∑ i ∈ Finset.range (r + 1),
        (Nat.stirlingSecond r i : ℝ) * N.descFactorial i * a ^ i * W (2 * N - i) := by
  have hpow (k : ℕ) : (k : ℝ) ^ r =
      ∑ i ∈ Finset.range (r + 1), (Nat.stirlingSecond r i : ℝ) * k.descFactorial i := by
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial k r
  simp_rw [hpow, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa only [Finset.mul_sum, mul_assoc, Nat.add_zero] using
    congrArg ((Nat.stirlingSecond r i : ℝ) * ·)
      (sum_pow_mul_choose_mul_secondOrder.factorial_moment a b W hW N i 0)

/-- **Power-weighted binomial sums of Lucas numbers.** Let $L_n$ denote the Lucas numbers
($L_0 = 2$, $L_1 = 1$, $L_{n+2} = L_{n+1} + L_n$), $S(r, i)$ the Stirling numbers of the second
kind and $(N)_i = N(N-1) \cdots (N-i+1)$ the falling factorial, with $(N)_0 = 1$. For all natural
numbers $N$ and $r$, with the convention $0^0 = 1$,
$$\sum_{k=0}^{N} k^r \binom{N}{k} L_k = \sum_{i=0}^{r} S(r, i) \, (N)_i \, L_{2N-i},$$
where the terms with $i > N$ vanish because $(N)_i = 0$.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.5. -/
public theorem sum_pow_mul_choose_mul_lucasNumber (N r : ℕ) :
    ∑ k ∈ Finset.range (N + 1), k ^ r * N.choose k * lucasNumber k =
      ∑ i ∈ Finset.range (r + 1),
        Nat.stirlingSecond r i * N.descFactorial i * lucasNumber (2 * N - i) := by
  have hL (n : ℕ) :
      (lucasNumber (n + 2) : ℝ) = 1 * (lucasNumber (n + 1) : ℝ) + 1 * (lucasNumber n : ℝ) := by
    rw [one_mul, one_mul, ← Nat.cast_add]
    rfl
  have h := sum_pow_mul_choose_mul_secondOrder 1 1 (fun n ↦ (lucasNumber n : ℝ)) hL N r
  simp only [one_pow, mul_one] at h
  exact_mod_cast h

open Polynomial in
/-- **Scherk's identity.** Write $S(r, i)$ for the Stirling numbers of the second kind. Let $N$ and
$r$ be natural numbers, let $a_0, \dots, a_N$ be real numbers, and let $f$ be the polynomial
$f(y) = \sum_{k=0}^{N} a_k y^k$, with $i$-th derivative $f^{(i)}$. Then for every real number $x$,
with the convention $0^0 = 1$,
$$\sum_{k=0}^{N} k^r a_k x^k = \sum_{i=0}^{r} S(r, i) \, x^i f^{(i)}(x).$$

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.1, equation (2.1). -/
public theorem sum_pow_mul_coeff_eq_sum_stirlingSecond_derivative (a : ℕ → ℝ) (N r : ℕ)
    (x : ℝ) :
    ∑ k ∈ Finset.range (N + 1), (k : ℝ) ^ r * a k * x ^ k =
      ∑ i ∈ Finset.range (r + 1), (Nat.stirlingSecond r i : ℝ) * x ^ i *
        (derivative^[i] (∑ k ∈ Finset.range (N + 1), C (a k) * X ^ k)).eval x := by
  have hpow (k : ℕ) : (k : ℝ) ^ r =
      ∑ i ∈ Finset.range (r + 1), (Nat.stirlingSecond r i : ℝ) * k.descFactorial i := by
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial k r
  simp_rw [hpow, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iterate_derivative_sum, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul,
    eval_mul, eval_C, eval_pow, eval_X]
  by_cases hik : i ≤ k
  · have hx : x ^ i * x ^ (k - i) = x ^ k := by
      rw [← pow_add, Nat.add_comm i (k - i), Nat.sub_add_cancel hik]
    rw [← hx]
    ring
  · simp only [Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hik),
      Nat.cast_zero, mul_zero, zero_mul]

end MetaMathlibExt
