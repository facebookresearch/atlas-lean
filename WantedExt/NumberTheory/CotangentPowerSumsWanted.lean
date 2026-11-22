/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace MetaMathlibExt

@[expose] public section

/-- Girstmair's coefficients
`c_{r,j} = (-1)^{r-1} ∑_{k=j}^{r} (-2)^{k-j} / (k-1)! · C(r, k) · S(k, j)`, where `S(k, j)` is
the unsigned Stirling number of the first kind (`Nat.stirlingFirst`). They express `i^r cot^r` in
terms of the derivatives `i^j cot^{(j-1)}`.

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Equation (8). The equation is not in the journal record; it is read from the arXiv
version, arXiv:2504.08330, Section 3, where it also follows from the displayed derivation. -/
def cotangentPowerCoeff (r j : ℕ) : ℚ :=
  (-1) ^ (r - 1) * ∑ k ∈ Finset.Icc j r,
    (-2) ^ (k - j) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) * (Nat.stirlingFirst k j : ℚ)

/-- `c_{1,1} = 1`, matching `i cot = i cot`.

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, characteristic value of Equation (8). -/
theorem cotangentPowerCoeff_one_one : cotangentPowerCoeff 1 1 = 1 := by
  simp [cotangentPowerCoeff, Nat.stirlingFirst]

/-- `c_{2,2} = -1`, matching `(i cot)^2 = 1 - i^2 cot'` with `cot' = -1 - cot^2`.

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, characteristic value of Equation (8). -/
theorem cotangentPowerCoeff_two_two : cotangentPowerCoeff 2 2 = -1 := by
  simp [cotangentPowerCoeff, Nat.stirlingFirst]

/-- Cotangent powers through cotangent derivatives: for `r ≥ 1` and real `x` with `sin x ≠ 0`,
`(i cot x)^r = ((-1)^r + 1)/2 + ∑_{j=1}^{r} c_{r,j} i^j cot^{(j-1)}(x)`, where `cot^{(m)}` is the
`m`-th derivative of `cot` and `c_{r,j}` is `cotangentPowerCoeff r j`.

The record's consequences that follow are not part of this statement: equations (9) and (10)
follow from this identity and `cotangentPowerCoeff_eq_zero_of_mod_two_ne`. Equation (11) enters
Theorem 1, stated below as `sum_conj_dirichletCharacter_mul_I_mul_cot_pow_of_even`.

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Proposition 1 (`integers-2025-A63-prop-1`). -/
public theorem_wanted I_mul_cot_pow_eq_sum_iteratedDeriv_cot (r : ℕ) (hr : 1 ≤ r) (x : ℝ)
    (hx : Real.sin x ≠ 0) :
    (Complex.I * Real.cot x) ^ r = ((-1) ^ r + 1) / 2 +
      ∑ j ∈ Finset.Icc 1 r, (cotangentPowerCoeff r j : ℂ) * Complex.I ^ j *
        ((iteratedDeriv (j - 1) Real.cot x : ℝ) : ℂ)

/-- Parity of Girstmair's coefficients: `c_{r,j} = 0` when `1 ≤ j ≤ r` and `r ≢ j (mod 2)`.
The source deduces this from the `ℚ`-linear independence of the functions `i^j cot^{(j-1)}`.

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Proposition 1, the sentence that follows it (`integers-2025-A63-prop-1`). -/
public theorem_wanted cotangentPowerCoeff_eq_zero_of_mod_two_ne {r j : ℕ} (hj : 1 ≤ j)
    (hjr : j ≤ r) (hpar : r % 2 ≠ j % 2) : cotangentPowerCoeff r j = 0

/-- **Theorem 1, odd `r`.** For `n ≥ 2`, odd `r ≥ 1` and an odd Dirichlet character `χ` mod `n`
(`χ(-1) = -1`) with conductor `f` and attached primitive character `χ_f`,
`y(χ|i^r cot^r(π/n)) = -∑_{1 ≤ j ≤ r, j odd} c_{r,j} (2n)^j/(j f^j) ∏_{p ∣ n} (1 - χ̄_f(p)/p^j)
B_{j,χ_f}`, where `B_{j,χ_f} = f^{j-1} ∑_{k=1}^f B_j(k/f) χ_f(k)`.

The character coordinate is unfolded through its defining Equation (3),
`y(χ|a) τ(χ̄_f) = ∑_{1 ≤ k ≤ n, (k,n)=1} χ̄(k) σ_k(a)`, with `σ_k(i^r cot^r(π/n)) =
i^r cot^r(πk/n)` (Equation (4)) and the Gauss sum `τ(χ̄_f) = ∑_{k=1}^f χ̄_f(k) e^{2πik/f}`.

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Theorem 1, first case (`integers-2025-A63-thm-1`). -/
public theorem_wanted sum_conj_dirichletCharacter_mul_I_mul_cot_pow_of_odd {n : ℕ} (hn : 2 ≤ n)
    {r : ℕ} (hr : Odd r) (χ : DirichletCharacter ℂ n) (hχ : χ (-1) = -1) :
    ∑ k ∈ (Finset.Icc 1 n).filter (fun k => Nat.Coprime k n),
        starRingEnd ℂ (χ k) * (Complex.I * Real.cot (Real.pi * k / n)) ^ r =
      (∑ k ∈ Finset.Icc 1 χ.conductor, starRingEnd ℂ (χ.primitiveCharacter k) *
          Complex.exp (2 * Real.pi * Complex.I * k / χ.conductor)) *
        -∑ j ∈ (Finset.Icc 1 r).filter Odd,
          (cotangentPowerCoeff r j : ℂ) * (2 * n : ℂ) ^ j / (j * (χ.conductor : ℂ) ^ j) *
            (∏ p ∈ n.primeFactors,
              (1 - starRingEnd ℂ (χ.primitiveCharacter p) / (p : ℂ) ^ j)) *
            ((χ.conductor : ℂ) ^ (j - 1) * ∑ k ∈ Finset.Icc 1 χ.conductor,
              (((Polynomial.bernoulli j).eval ((k : ℚ) / χ.conductor) : ℚ) : ℂ) *
                χ.primitiveCharacter k)

open Classical in
/-- **Theorem 1, even `r`.** For `n ≥ 2`, even `r ≥ 2` and an even Dirichlet character `χ` mod
`n` (`χ(-1) = 1`) with conductor `f`,
`y(χ|i^r cot^r(π/n)) = y(χ|1) + ∑_{1 ≤ j ≤ r, j even} c_{r,j} (2n)^j/(j f^j)
∏_{p ∣ n} (1 - χ̄_f(p)/p^j) B_{j,χ_f}`, where `y(χ|1)` is `φ(n)` for the principal character and
`0` otherwise (Equation (11)).

The character coordinate is unfolded through Equation (3) as in the odd case.

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Theorem 1, second case (`integers-2025-A63-thm-1`). -/
public theorem_wanted sum_conj_dirichletCharacter_mul_I_mul_cot_pow_of_even {n : ℕ} (hn : 2 ≤ n)
    {r : ℕ} (hr0 : r ≠ 0) (hr : Even r) (χ : DirichletCharacter ℂ n) (hχ : χ (-1) = 1) :
    ∑ k ∈ (Finset.Icc 1 n).filter (fun k => Nat.Coprime k n),
        starRingEnd ℂ (χ k) * (Complex.I * Real.cot (Real.pi * k / n)) ^ r =
      (∑ k ∈ Finset.Icc 1 χ.conductor, starRingEnd ℂ (χ.primitiveCharacter k) *
          Complex.exp (2 * Real.pi * Complex.I * k / χ.conductor)) *
        ((if χ = 1 then (n.totient : ℂ) else 0) +
          ∑ j ∈ (Finset.Icc 1 r).filter Even,
            (cotangentPowerCoeff r j : ℂ) * (2 * n : ℂ) ^ j / (j * (χ.conductor : ℂ) ^ j) *
              (∏ p ∈ n.primeFactors,
                (1 - starRingEnd ℂ (χ.primitiveCharacter p) / (p : ℂ) ^ j)) *
              ((χ.conductor : ℂ) ^ (j - 1) * ∑ k ∈ Finset.Icc 1 χ.conductor,
                (((Polynomial.bernoulli j).eval ((k : ℚ) / χ.conductor) : ℚ) : ℂ) *
                  χ.primitiveCharacter k))

/-- **Theorem 2.** Girstmair's coefficients agree with the coefficients `d_{r,j}` of the
earlier literature (Equation (15)): for `1 ≤ j ≤ r` with `j ≡ r (mod 2)`,
`c_{r,j} = (-1)^{r+1} 2^{r-j}/(j-1)! · d_{r,j}`, where
`d_{r,j} = ∑_{j_1, …, j_r ≥ 0, j + 2 j_1 + ⋯ + 2 j_r = r} ∏_{t=1}^r B_{2 j_t}/(2 j_t)!`
(Equation (13); only even-index Bernoulli numbers occur).

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Theorem 2 with Equations (13) and (15) (`integers-2025-A63-thm-2`). -/
public theorem_wanted cotangentPowerCoeff_eq_bernoulli_tuple_sum {r j : ℕ} (hj : 1 ≤ j)
    (hjr : j ≤ r) (hpar : j % 2 = r % 2) :
    cotangentPowerCoeff r j =
      (-1) ^ (r + 1) * 2 ^ (r - j) / ((j - 1).factorial : ℚ) *
        ∑ a ∈ Finset.Nat.antidiagonalTuple r ((r - j) / 2),
          ∏ t, bernoulli (2 * a t) / ((2 * a t).factorial : ℚ)

end

end MetaMathlibExt
