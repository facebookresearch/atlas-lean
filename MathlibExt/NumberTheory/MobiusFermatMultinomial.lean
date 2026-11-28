/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MobiusFermat
import all MathlibExt.NumberTheory.MobiusFermatReduction
import all MathlibExt.NumberTheory.VonMangoldtFermatMultinomial
import Mathlib.Data.Finsupp.Weight

/-!
# The multinomial formula for the Möbius–Fermat function

The bound on the exponents excludes the exceptional generator `63 = 3 ^ 2 * 7` from
contributing to the Dirichlet convolution. We use the factorial-normalized inverse recurrence
from `VonMangoldtFermatMultinomial`, then divide by the factorial product over `ℚ`.

## References

* Juan Luis Varona, *The Möbius and the von Mangoldt-type Functions of the Fermat Zeta Function*,
  INTEGERS **26** (2026), Article A106, pp. 1–25, Proposition 4 and its proof in §5.
* G. Mora, L. M. Navas, and J. L. Varona, *On the von Mangoldt-type function of the Fibonacci
  zeta function*, Rev. R. Acad. Cienc. Exactas Fís. Nat. Ser. A Mat. RACSAM **119** (2025),
  Article 126, pp. 1–19, Proposition 2, the predecessor of the recurrence argument.
* R. D. Carmichael, *On the numerical factors of the arithmetic forms αⁿ ± βⁿ*, Ann. of Math.
  (2) **15** (1913–1914), pp. 30–48 and 49–80. Varona cites this primitive-divisor result as
  Theorem 1. The Lean proof instead uses Bang–Zsigmondy for uniqueness of exponent vectors.
* G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of aⁿ − bⁿ*, Ann. of Math.
  (2) **5** (1904), pp. 173–180, Theorem V (the primitive-divisor result for indices above two).
-/

open ArithmeticFunction

namespace MetaMathlibExt

open mobiusFermat_mul_factorial_eq_squarefree_part vonMangoldtFermat_eq_multinomial in
/-- **Multinomial formula for the Möbius–Fermat function.** Let $u_M$ be the Fermat unit function
and let $\mu_M$ be an integer-valued arithmetic function with $\mu_M * u_M = \varepsilon$, where
$*$ is Dirichlet convolution and $\varepsilon$ is its identity, with $\varepsilon(1) = 1$ and
$\varepsilon(l) = 0$ for $l \ne 1$; thus $\mu_M$ is the Dirichlet inverse of $u_M$, the
Möbius–Fermat function.
Let $n_1, \dots, n_k$ be finitely many (possibly no) distinct integers with $n_i \ge 2$ and
$n_i \ne 6$, let $m_1, \dots, m_k \ge 1$ be integers, and put
$l = \prod_{i=1}^{k} (2^{n_i} - 1)^{m_i}$ and
$r = m_1 + \dots + m_k$. Suppose that $2$ is not among the $n_i$ or has exponent $1$, or that $3$
is not among the $n_i$; that is, the factor $3 = 2^2 - 1$ occurs at most to the first power or
the factor $7 = 2^3 - 1$ does not occur. Then, as rational numbers,
$\mu_M(l) = (-1)^r \, r! / (m_1! \cdots m_k!)$.

Source: J. L. Varona, *The Möbius and the von Mangoldt-type Functions of the Fermat Zeta
Function*, INTEGERS 26 (2026), Article A106, Proposition 4. -/
public theorem mobiusFermat_eq_multinomial (μ : ArithmeticFunction ℤ)
    (hμ : μ * fermatUnitFunction = 1) (f : ℕ →₀ ℕ) (hf : ∀ n ∈ f.support, 2 ≤ n ∧ n ≠ 6)
    (h37 : f 2 ≤ 1 ∨ f 3 = 0) :
    (μ (f.prod fun n m => (2 ^ n - 1) ^ m) : ℚ) =
      (-1) ^ (f.sum fun _ m => m) * ((f.sum fun _ m => m).factorial : ℚ) /
        (f.prod fun _ m => (m.factorial : ℚ)) := by
  let d := f.subtypeDomain fun n => 2 ≤ n ∧ n ≠ 6
  have hd : d two ≤ 1 ∨ d three = 0 := h37
  have hfac : (d.prod fun _ m => (m.factorial : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hc := congrArg (fun z : ℤ => (z : ℚ)) (inverse_mul_factorials μ hμ d hd)
  have hq : (μ (value d) : ℚ) = (-1) ^ d.degree * (d.degree.factorial : ℚ) /
      (d.prod fun _ m => (m.factorial : ℚ)) := by
    apply (eq_div_iff hfac).2
    simpa [factorials, Finsupp.prod] using hc
  have hdegree : d.degree = d.sum fun _ m => m := rfl
  simpa only [value, mersenne, hdegree, d,
    Finsupp.prod_subtypeDomain_index (h := fun (n m : ℕ) => (2 ^ n - 1) ^ m) hf,
    Finsupp.prod_subtypeDomain_index (h := fun (_ m : ℕ) => (m.factorial : ℚ)) hf,
    Finsupp.sum_subtypeDomain_index (h := fun (_ m : ℕ) => m) hf] using hq

end MetaMathlibExt
