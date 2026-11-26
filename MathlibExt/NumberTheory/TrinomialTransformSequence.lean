/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TrinomialCoefficient

/-!
# Trinomial transform sequence

This module defines the sequence transform whose weights are the trinomial
coefficients from the prerequisite API.
-/

namespace MetaMathlibExt

open scoped BigOperators

@[expose] public section

/-- **Trinomial transform.** Let $R$ be a semiring and $a \colon \mathbb{N} \to R$ a sequence. The
trinomial transform of $a$ is the sequence $b \colon \mathbb{N} \to R$ given by

$$b_n = \sum_{i=0}^{2n} T(n, i)\, a_i,$$

where $T(n, i)$ is the trinomial coefficient, the coefficient of $X^i$ in $(1 + X + X^2)^n$,
regarded as an element of $R$.

Source: László Németh, *The Trinomial Transform Triangle*, Journal of Integer Sequences 21
(2018), Article 18.7.3; JIS concept `jis_sem_ddbad39a52886299b21344a6`, source statement
`jis_1961e690ee22a57370a48a96`. -/
noncomputable def trinomialTransformSequence {R : Type*} [Semiring R]
    (a : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range (2 * n + 1), (trinomialCoefficient n i : R) * a i

/-- **Zeroth term of the trinomial transform.** For every semiring $R$ and every sequence
$a \colon \mathbb{N} \to R$, the zeroth term of the trinomial transform of $a$ equals $a_0$. -/
theorem trinomialTransformSequence_zero {R : Type*} [Semiring R] (a : ℕ → R) :
    trinomialTransformSequence a 0 = a 0 := by
  simp [trinomialTransformSequence, trinomialCoefficient, Polynomial.coeff_one]

/-- **Trinomial transform of the zero sequence.** For every semiring $R$ and every
$n \in \mathbb{N}$, the $n$th term of the trinomial transform of the zero sequence
$\mathbb{N} \to R$ is $0$. -/
theorem trinomialTransformSequence_zero_apply {R : Type*} [Semiring R] (n : ℕ) :
    trinomialTransformSequence (fun _ => (0 : R)) n = 0 := by
  simp [trinomialTransformSequence]

end

end MetaMathlibExt
