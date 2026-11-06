/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Basic hypergeometric series `{}_r φ_s`

This file defines the coefficient

  `(a₁;q)ₙ ⋯ (aᵣ;q)ₙ / ((q;q)ₙ (b₁;q)ₙ ⋯ (bₛ;q)ₙ) * ((-1)ⁿ q^{n choose 2})^{1+s-r}`

of the general basic hypergeometric series `{}_rφ_s(a₁,…,aᵣ; b₁,…,bₛ; q, z)`
and packages the coefficients as a formal power series over `ℂ`.

Finite `q`-Pochhammer symbols are expanded as finite products:

* `(a;q)ₙ = ∏_{j=0}^{n-1} (1 - a q^j)`,
* `(q;q)ₙ = ∏_{j=0}^{n-1} (1 - q^{j+1})`.

The normalization exponent `1 + s - r` is computed in `ℤ`, so the definition also covers the
cases where this exponent is negative (when `r > s+1`), where the integer power is Mathlib's
totalized `zpow` on `ℂ`.

The definitions are formal and algebraic. Division and integer powers use Mathlib's totalized
operations on `ℂ`; analytic applications must separately establish that the denominator does not
vanish (in particular `b_j ∉ {q^{-k} : k ∈ ℕ}` and `q` not a root of unity) and convergence
conditions. No nonvanishing or convergence hypothesis is imposed here, so zero-denominator cases
are covered as totalized values.

## Main definitions

* `MetaMathlibExt.BasicHypergeometric.basicHypergeometricCoefficient`
* `MetaMathlibExt.BasicHypergeometric.basicHypergeometricSeries`

## Main results

* `basicHypergeometricCoefficient_zero`
* `coeff_basicHypergeometricSeries`
* `basicHypergeometricCoefficient_phi_succ`

## References

* [NIST Digital Library of Mathematical Functions, §17.4][dlmf17.4]

[dlmf17.4]: https://dlmf.nist.gov/17.4
-/

@[expose] public section

namespace MetaMathlibExt.BasicHypergeometric

open Finset

/-- **Coefficients of the basic hypergeometric series.** Let $r$ and $s$ be natural numbers, let
$a_1, \dots, a_r$, $b_1, \dots, b_s$ and $q$ be complex numbers, and write
$(x;q)_n = \prod_{j=0}^{n-1} (1 - x q^j)$ for the finite $q$-Pochhammer symbol, so that
$(q;q)_n = \prod_{j=0}^{n-1} (1 - q^{j+1})$. For a natural number $n$, the coefficient of $z^n$ in
the basic hypergeometric series ${}_r\phi_s(a_1, \dots, a_r; b_1, \dots, b_s; q, z)$ is

$$\frac{(a_1;q)_n \cdots (a_r;q)_n}{(q;q)_n\,(b_1;q)_n \cdots (b_s;q)_n}
\left((-1)^n q^{\binom{n}{2}}\right)^{1+s-r},$$

where the exponent $1 + s - r$ is an integer and may be negative. This is DLMF 17.4.1, which is
written for $r + 1$ upper parameters, restated for $r$ upper parameters.

No condition on the parameters is imposed: division by zero gives $0$, and so does every negative
power of $0$. Analytic applications must separately establish that the denominator does not
vanish.
-/
noncomputable def basicHypergeometricCoefficient {r s : ℕ} (a : Fin r → ℂ) (b : Fin s → ℂ)
    (q : ℂ) (n : ℕ) : ℂ :=
  (∏ i, ∏ j ∈ range n, (1 - a i * q ^ j)) /
      ((∏ j ∈ range n, (1 - q ^ (j + 1))) * ∏ i, ∏ j ∈ range n, (1 - b i * q ^ j)) *
    (((-1 : ℂ) ^ n * q ^ Nat.choose n 2) ^ ((1 : ℤ) + s - r))

/-- **Basic hypergeometric series.** Let $r$ and $s$ be natural numbers and let
$a_1, \dots, a_r$, $b_1, \dots, b_s$ and $q$ be complex numbers. The basic hypergeometric series
${}_r\phi_s(a_1, \dots, a_r; b_1, \dots, b_s; q, z)$ is the formal power series in $z$ over
$\mathbb{C}$ whose coefficient of $z^n$, for each natural number $n$, is the $n$-th basic
hypergeometric coefficient of these parameters. -/
noncomputable def basicHypergeometricSeries {r s : ℕ} (a : Fin r → ℂ) (b : Fin s → ℂ)
    (q : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => basicHypergeometricCoefficient a b q n

@[simp]
theorem basicHypergeometricCoefficient_zero {r s : ℕ} (a : Fin r → ℂ) (b : Fin s → ℂ)
    (q : ℂ) : basicHypergeometricCoefficient a b q 0 = 1 := by
  simp [basicHypergeometricCoefficient]

@[simp]
theorem coeff_basicHypergeometricSeries {r s : ℕ} (a : Fin r → ℂ) (b : Fin s → ℂ)
    (q : ℂ) (n : ℕ) :
    PowerSeries.coeff n (basicHypergeometricSeries a b q) =
      basicHypergeometricCoefficient a b q n := by
  simp [basicHypergeometricSeries]

/-- **Coefficients of the series ${}_{s+1}\phi_s$.** Let $s$ be a natural number, let
$a_1, \dots, a_{s+1}$, $b_1, \dots, b_s$ and $q$ be complex numbers, and write
$(x;q)_n = \prod_{j=0}^{n-1} (1 - x q^j)$ for the finite $q$-Pochhammer symbol, so that
$(q;q)_n = \prod_{j=0}^{n-1} (1 - q^{j+1})$. For every natural number $n$, the coefficient of $z^n$
in the basic hypergeometric series ${}_{s+1}\phi_s(a_1, \dots, a_{s+1}; b_1, \dots, b_s; q, z)$ is

$$\frac{(a_1;q)_n \cdots (a_{s+1};q)_n}{(q;q)_n\,(b_1;q)_n \cdots (b_s;q)_n}.$$

With $r = s + 1$ upper parameters, the exponent $1 + s - r$ of the normalization factor
$\left((-1)^n q^{\binom{n}{2}}\right)^{1+s-r}$ is $0$, so the factor disappears. As in the
definition of the coefficient, division by zero gives $0$. -/
theorem basicHypergeometricCoefficient_phi_succ (s : ℕ) (a : Fin (s + 1) → ℂ)
    (b : Fin s → ℂ) (q : ℂ) (n : ℕ) :
    basicHypergeometricCoefficient a b q n =
      (∏ i, ∏ j ∈ range n, (1 - a i * q ^ j)) /
        ((∏ j ∈ range n, (1 - q ^ (j + 1))) * ∏ i, ∏ j ∈ range n, (1 - b i * q ^ j)) := by
  simp [basicHypergeometricCoefficient, Nat.cast_add, add_comm]

end MetaMathlibExt.BasicHypergeometric
