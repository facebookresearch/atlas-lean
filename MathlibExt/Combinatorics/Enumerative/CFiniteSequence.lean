/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# C-finite polynomial sequences

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL26/Makowsky/makowsky16.tex>.
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **C-finite polynomial sequences.** Let $\sigma$ be a type indexing variables, and write
$\mathbb{Z}[\sigma]$ for the multivariate polynomials with integer coefficients in the variables
$\sigma$. A sequence $a_0, a_1, a_2, \dots$ in $\mathbb{Z}[\sigma]$ is C-finite when there exist
natural numbers $k$ and $N$ and polynomials $p_1, \dots, p_k \in \mathbb{Z}[\sigma]$ such that
for every $n \ge N$
$$
a_{n+k+1} = \sum_{i=1}^{k} p_i \, a_{n+i}.
$$

Source: concept `jis_sem_35aa465b4e5a8b902eabc445`,
statement `jis_1ebc476d74ad111e89710ced`. -/
def IsCFiniteSequence {σ : Type*} (a : ℕ → MvPolynomial σ ℤ) : Prop :=
  ∃ (k N : ℕ) (c : Fin k → MvPolynomial σ ℤ),
    ∀ n ≥ N, a (n + k + 1) = ∑ i : Fin k, c i * a (n + i.val + 1)

end

end MetaMathlibExt
