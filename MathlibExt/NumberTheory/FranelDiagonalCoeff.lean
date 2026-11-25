/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import MathlibExt.NumberTheory.ArithmeticFunction.BinomialPowerRealizability
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Franel numbers as diagonal coefficients

The Franel number `f_m = ∑_{k=0}^{m} C(m, k)^3`, which is `MetaMathlibExt.binomialPowerSeq 3 0 m`,
is the coefficient of `x^m y^m z^m` in `((x + y)(y + z)(z + x))^m` over `ℚ`.

The proof expands `(x + y)^m (y + z)^m (z + x)^m` by the binomial theorem into a triple sum of
monomials `x^(i + m - k) y^(m - i + j) z^(m - j + k)` with `0 ≤ i, j, k ≤ m`. Such a monomial is
`x^m y^m z^m` exactly when `i = j = k`, so the coefficient is `∑_{k=0}^{m} C(m, k)^3`.
-/

public section

namespace MathlibExt.NumberTheory.OeisA265233Wanted

open MvPolynomial Finset

/-- The binomial theorem for `X a + X b`, written as a sum of monomials. -/
private theorem add_X_pow_eq_sum_monomial (a b : Fin 3) (m : ℕ) :
    ((X a + X b) ^ m : MvPolynomial (Fin 3) ℚ) =
      ∑ i ∈ range (m + 1),
        monomial (Finsupp.single a i + Finsupp.single b (m - i)) (m.choose i : ℚ) := by
  rw [add_pow]
  refine sum_congr rfl fun i _ => ?_
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial,
    ← map_natCast (C : ℚ →+* MvPolynomial (Fin 3) ℚ), mul_comm, C_mul_monomial, mul_one, mul_one]

/-- **Franel numbers as diagonal coefficients.** For every natural number $m$, the coefficient of
$x^m y^m z^m$ in the polynomial $\bigl((x + y)(y + z)(z + x)\bigr)^m \in \mathbb{Q}[x, y, z]$
is the Franel number $f_m = \sum_{k=0}^{m} \binom{m}{k}^3$.

Source: Juntao Jin, "An Explicit Formula and a
Recurrence for OEIS A265233", Lemma 3. -/
theorem coeff_pow_eq_franel (m : ℕ) :
    (((MvPolynomial.X 0 + MvPolynomial.X 1) *
        (MvPolynomial.X 1 + MvPolynomial.X 2) *
        (MvPolynomial.X 2 + MvPolynomial.X 0)) ^ m :
        MvPolynomial (Fin 3) ℚ).coeff
      (Finsupp.single (0 : Fin 3) m +
        Finsupp.single (1 : Fin 3) m +
        Finsupp.single (2 : Fin 3) m)
      = (MetaMathlibExt.binomialPowerSeq 3 0 m : ℚ) := by
  rw [mul_pow, mul_pow, add_X_pow_eq_sum_monomial, add_X_pow_eq_sum_monomial,
    add_X_pow_eq_sum_monomial]
  simp only [sum_mul, mul_sum, monomial_mul_monomial, coeff_sum, coeff_monomial]
  -- The exponent of `x`, `y`, `z` is `i + (m - k)`, `(m - i) + j`, `(m - j) + k`.
  have diag : ∀ i ∈ range (m + 1), ∀ j ∈ range (m + 1), ∀ k ∈ range (m + 1),
      (Finsupp.single (0 : Fin 3) i + Finsupp.single 1 (m - i) +
          (Finsupp.single 1 j + Finsupp.single 2 (m - j)) +
          (Finsupp.single 2 k + Finsupp.single 0 (m - k)) =
        Finsupp.single 0 m + Finsupp.single 1 m + Finsupp.single 2 m ↔ i = k ∧ j = k) := by
    intro i hi j hj k hk
    rw [mem_range] at hi hj hk
    constructor
    · intro h
      have h0 := DFunLike.congr_fun h 0
      have h1 := DFunLike.congr_fun h 1
      have h2 := DFunLike.congr_fun h 2
      simp at h0 h1 h2
      omega
    · rintro ⟨rfl, rfl⟩
      ext x
      fin_cases x <;> simp <;> omega
  calc _ = ∑ k ∈ range (m + 1), ∑ j ∈ range (m + 1), ∑ i ∈ range (m + 1),
          if i = k ∧ j = k then (m.choose i : ℚ) * m.choose j * m.choose k else 0 :=
        sum_congr rfl fun k hk => sum_congr rfl fun j hj => sum_congr rfl fun i hi =>
          if_congr (diag i hi j hj k hk) rfl rfl
    _ = ∑ k ∈ range (m + 1), (m.choose k : ℚ) ^ 3 := by
        refine sum_congr rfl fun k hk => ?_
        simp [ite_and, sum_ite_eq', hk]
        ring
    _ = _ := by simp [MetaMathlibExt.binomialPowerSeq]

end MathlibExt.NumberTheory.OeisA265233Wanted
