/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Falling k-binomial transforms

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL10/French/french13.tex>.
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **Falling k-binomial transform.** For an integer $k$ and an integer sequence $(a_i)_{i \ge 0}$,
the falling $k$-binomial transform of $a$ is the integer sequence $(b_n)_{n \ge 0}$ given by
$$b_n = \sum_{i=0}^{n} \binom{n}{i} k^{n-i} a_i.$$

Source: statement `jis_f80f56d96d180cdfb88089a0`, concept
`jis_sem_435054dc88f9efa6e6529e6a`. -/
def fallingKBinomialTransform (k : ℤ) (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * k ^ (n - i) * a i

/-- **Binomial transform.** The binomial transform of an integer sequence $(a_i)_{i \ge 0}$ is the
falling k-binomial transform of $a$ with $k = 1$, the sequence whose $n$-th term is
$\sum_{i=0}^{n} \binom{n}{i} 1^{n-i} a_i$. -/
def binomialTransform (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  fallingKBinomialTransform 1 a n

/-- **Binomial transform as a binomial sum.** For every integer sequence $(a_i)_{i \ge 0}$ and
every $n \in \mathbb{N}$, the $n$-th term of the binomial transform of $a$ equals
$\sum_{i=0}^{n} \binom{n}{i} a_i$. -/
theorem binomialTransform_eq_sum (a : ℕ → ℤ) (n : ℕ) :
    binomialTransform a n =
      ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * a i := by
  simp [binomialTransform, fallingKBinomialTransform, one_pow, mul_one]

end

end MetaMathlibExt
