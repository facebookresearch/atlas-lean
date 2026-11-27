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
public import MathlibExt.NumberTheory.OresmeJacobsthalModuloNine
public import MathlibExt.NumberTheory.OresmePellCongruence
public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence
public import MathlibExt.NumberTheory.OresmeConvolutionsPellLucasSequenceOresmeConvolution
public import MathlibExt.NumberTheory.OresmeConvolutionsJacobsthalOresmeConvolution

/-!
# Cauchy convolutions with Oresme numbers

Statements from M. R. Bacon and C. K. Cook on the Cauchy convolutions
`∑_{k=0}^n a_k O_{n-k}` of the Oresme numbers `O_n = n/2^n` (the closed form of
Definition 1.1) with the Fibonacci, Lucas, Pell, Pell–Lucas, Jacobsthal and
Jacobsthal–Lucas numbers, and the congruences read off from them. The Pell–Lucas convolution
`pellLucasSequence_oresme_convolution` is proved in
`MathlibExt.NumberTheory.OresmeConvolutionsPellLucasSequenceOresmeConvolution`, and the
Jacobsthal convolution `jacobsthal_oresme_convolution` is proved in
`MathlibExt.NumberTheory.OresmeConvolutionsJacobsthalOresmeConvolution`. The Oresme numbers
are
written inline as `n / 2^n` over `ℚ`. The paper's Pell–Lucas numbers are the odd sequence
`Q_0 = Q_1 = 1` (`pellLucasSequence`), its Jacobsthal numbers are `lucasU (1, -2)`, and its
Jacobsthal–Lucas numbers `j_0 = 2, j_1 = 1` are `jacobsthalLucasNumber`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Powers of two times Lucas numbers modulo 5.** Let $L_m$ denote the Lucas numbers. For every
natural number $n$, $2^n L_{n+1} \equiv 1 \pmod{5}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 4.4 (`fq-2024-cookbacon061124-cor-4.4`). -/
public theorem_wanted two_pow_mul_lucasNumber_succ_modEq_five (n : ℕ) :
    2 ^ n * lucasNumber (n + 1) ≡ 1 [MOD 5]

end

end MetaMathlibExt
