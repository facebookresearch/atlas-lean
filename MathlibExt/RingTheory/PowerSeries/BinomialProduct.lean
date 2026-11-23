/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The binomial (Hurwitz) product of formal power series

`binomialProduct A B` is the power series whose `n`-th coefficient is the binomial convolution
`∑_{k ≤ n} binom(n, k) a_k b_{n-k}` of the coefficients of `A` and `B` (the product of the
corresponding exponential generating functions, read back as ordinary series).

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, equation (1).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Binomial (Hurwitz) product of power series.** Let $K$ be a commutative ring. The binomial
product of formal power series $A = \sum_n a_n X^n$ and $B = \sum_n b_n X^n$ in $K[[X]]$ is the
power series $\sum_n c_n X^n$ with $c_n = \sum_{k=0}^{n} \binom{n}{k} a_k b_{n-k}$.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, equation (1). -/
public noncomputable def binomialProduct {K : Type*} [CommRing K] (A B : PowerSeries K) :
    PowerSeries K :=
  PowerSeries.mk fun n => ∑ k ∈ Finset.range (n + 1),
    (n.choose k : K) * PowerSeries.coeff k A * PowerSeries.coeff (n - k) B

/-- **Coefficients of the binomial product.** Let $K$ be a commutative ring and let
$A = \sum_n a_n X^n$ and $B = \sum_n b_n X^n$ be formal power series over $K$. For every natural
number $n$, the coefficient of $X^n$ in the binomial product of $A$ and $B$ is
$\sum_{k=0}^{n} \binom{n}{k} a_k b_{n-k}$.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, equation (1). -/
public theorem coeff_binomialProduct {K : Type*} [CommRing K] (A B : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (binomialProduct A B) = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : K) * PowerSeries.coeff k A * PowerSeries.coeff (n - k) B := by
  simp [binomialProduct]

/-- **Constant coefficient of the binomial product.** Let $K$ be a commutative ring. For formal
power series $A$ and $B$ over $K$, the constant coefficient of the binomial product of $A$ and
$B$ is the product of the constant coefficients of $A$ and $B$.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, equation (1). -/
public theorem constantCoeff_binomialProduct {K : Type*} [CommRing K] (A B : PowerSeries K) :
    PowerSeries.coeff 0 (binomialProduct A B) = PowerSeries.coeff 0 A * PowerSeries.coeff 0 B := by
  simp [binomialProduct]

end

end MetaMathlibExt
