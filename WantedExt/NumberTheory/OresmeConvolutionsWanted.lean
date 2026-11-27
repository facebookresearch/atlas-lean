/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.JacobsthalLucasNumber
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.OresmeConvolutions
public import MathlibExt.NumberTheory.OresmeJacobsthalLucasCongruence
public import MathlibExt.NumberTheory.OresmeLucasModuloFive
public import MathlibExt.NumberTheory.OresmePellCongruence
public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence
public import MathlibExt.NumberTheory.OresmeConvolutionsPellLucasSequenceOresmeConvolution

/-!
# Cauchy convolutions with Oresme numbers

Statements from M. R. Bacon and C. K. Cook on the Cauchy convolutions
`∑_{k=0}^n a_k O_{n-k}` of the Oresme numbers `O_n = n/2^n` (the closed form of
Definition 1.1) with the Fibonacci, Lucas, Pell, Pell–Lucas, Jacobsthal and
Jacobsthal–Lucas numbers, and the congruences read off from them. The Pell–Lucas convolution
`pellLucasSequence_oresme_convolution` is proved in
`MathlibExt.NumberTheory.OresmeConvolutionsPellLucasSequenceOresmeConvolution`. The Oresme numbers
are
written inline as `n / 2^n` over `ℚ`. The paper's Pell–Lucas numbers are the odd sequence
`Q_0 = Q_1 = 1` (`pellLucasSequence`), its Jacobsthal numbers are `lucasU (1, -2)`, and its
Jacobsthal–Lucas numbers `j_0 = 2, j_1 = 1` are `jacobsthalLucasNumber`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Jacobsthal–Oresme convolution.** Let $J_m$ denote the Jacobsthal numbers, the terms of the
Lucas sequence $U(1, -2)$, and let $O_m = m/2^m$ denote the Oresme numbers. For every natural
number $n$,
$\sum_{k=0}^{n} J_k O_{n-k} = \frac{2}{9} J_{n+1} - \frac{2(n+1)}{9 \cdot 2^n}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 6.2 (`fq-2024-cookbacon061124-prop-6.2`). -/
public theorem_wanted jacobsthal_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (lucasU ⟨1, -2, by decide⟩ k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 9 * (lucasU ⟨1, -2, by decide⟩ (n + 1) : ℚ) - 2 * ((n : ℚ) + 1) / (9 * 2 ^ n)

/-- **Powers of two times Jacobsthal numbers modulo 9.** Let $J_m$ denote the Jacobsthal numbers,
the terms of the Lucas sequence $U(1, -2)$. For every natural number $n$,
$2^n J_{n+1} \equiv n + 1 \pmod{9}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 6.3 (`fq-2024-cookbacon061124-cor-6.3`). -/
public theorem_wanted two_pow_mul_jacobsthal_succ_modEq_nine (n : ℕ) :
    2 ^ n * lucasU ⟨1, -2, by decide⟩ (n + 1) ≡ n + 1 [ZMOD 9]

end

end MetaMathlibExt
