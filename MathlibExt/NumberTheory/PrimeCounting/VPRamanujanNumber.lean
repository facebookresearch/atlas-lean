/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card

/-!
# Generalized Ramanujan numbers

This file formalizes the `(v, P)`-Ramanujan-number definition of Shevelev:
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Moses/moses1.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Counting members of a set up to a real bound.** For a set $P$ of natural numbers and a
real number $x$, $\pi_P(x)$ is the number of members of $P$ that are at most $x$.

In the intended application $P$ is an infinite set of primes. -/
noncomputable def primeCountingWithin (P : Set ℕ) (x : ℝ) : ℕ :=
  Set.ncard {p : ℕ | p ∈ P ∧ (p : ℝ) ≤ x}

/-- **Generalized Ramanujan numbers.** Let $P$ be a set of natural numbers, $v$ a real number and
$m$, $R$ natural numbers, and write $\pi_P(x)$ for the number of members of $P$ that are at most
$x$. Then $R$ is the $(v, P)$-Ramanujan number of index $m$ when $P$ is an infinite set of
primes, $v > 1$, and $R$ is the least natural number such that $\pi_P(x) - \pi_P(x/v) \ge m$
for every real $x \ge R$, that is, every interval $(x/v, x]$ with $x \ge R$ contains at least
$m$ members of $P$.

Source: concept `jis_sem_15d6f90b779184192e0e80e3`. -/
def IsVPRamanujanNumber (P : Set ℕ) (v : ℝ) (m R : ℕ) : Prop :=
  P.Infinite ∧
    P ⊆ {p : ℕ | p.Prime} ∧
    1 < v ∧
    Minimal {R' : ℕ |
      ∀ x : ℝ, (R' : ℝ) ≤ x →
        (m : ℤ) ≤ (primeCountingWithin P x : ℤ) - (primeCountingWithin P (x / v) : ℤ)} R

end MetaMathlibExt
