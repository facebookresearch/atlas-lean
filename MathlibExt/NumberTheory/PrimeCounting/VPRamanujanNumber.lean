/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card

/-!
# Generalized Ramanujan numbers

This file formalizes the `(v, P)`-Ramanujan-number definition of Shevelev:
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Moses/moses1.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- The number of members of `P` not exceeding the real bound `x`.
On the source domain, `P` is an infinite set consisting only of primes. -/
noncomputable def primeCountingWithin (P : Set ℕ) (x : ℝ) : ℕ :=
  Set.ncard {p : ℕ | p ∈ P ∧ (p : ℝ) ≤ x}

/-- `R` is the `(v, P)`-Ramanujan number of index `m`: `P` is an infinite
set of primes, `v > 1`, and `R` is the least natural threshold after which
every interval `(x / v, x]` contains at least `m` members of `P`.

The source concept is `jis_sem_15d6f90b779184192e0e80e3`. -/
def IsVPRamanujanNumber (P : Set ℕ) (v : ℝ) (m R : ℕ) : Prop :=
  P.Infinite ∧
    P ⊆ {p : ℕ | p.Prime} ∧
    1 < v ∧
    Minimal {R' : ℕ |
      ∀ x : ℝ, (R' : ℝ) ≤ x →
        (m : ℤ) ≤ (primeCountingWithin P x : ℤ) - (primeCountingWithin P (x / v) : ℤ)} R

end MetaMathlibExt
