/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs

/-!
# Primitive divisors of integer sequences

For an integer-valued sequence `a`, a natural number `u ≥ 2` is a primitive divisor of
`a m` when it divides `a m` and no earlier positive-indexed term. A primitive prime divisor is
a primitive divisor that is prime.

## Main definitions

* `IntegerSequence.IsPrimitiveDivisor`
* `IntegerSequence.IsPrimitivePrimeDivisor`

## References

* M. Sadek, M. Wafik, and T. Yesin, *Arithmetic progressions in polynomial orbits*,
  [arXiv:2403.04397](https://arxiv.org/abs/2403.04397)
-/

@[expose] public section

namespace IntegerSequence

/-- **Primitive divisor of an integer sequence.** Let $(a_s)_{s \ge 0}$ be a sequence of integers
and let $m$ and $u$ be natural numbers. Then $u$ is a primitive divisor of $a_m$ when $m \ge 1$,
$u \ge 2$, $u$ divides $a_m$, and $u$ divides no $a_s$ with $1 \le s < m$. -/
def IsPrimitiveDivisor (a : ℕ → ℤ) (m u : ℕ) : Prop :=
  1 ≤ m ∧ 2 ≤ u ∧ (u : ℤ) ∣ a m ∧ ∀ s : ℕ, 1 ≤ s → s < m → ¬ (u : ℤ) ∣ a s

/-- **Primitive prime divisor of an integer sequence.** Let $(a_s)_{s \ge 0}$ be a sequence of
integers and let $m$ and $u$ be natural numbers. Then $u$ is a primitive prime divisor of $a_m$ when
$u$ is prime and $u$ is a primitive divisor of $a_m$. -/
def IsPrimitivePrimeDivisor (a : ℕ → ℤ) (m u : ℕ) : Prop :=
  Nat.Prime u ∧ IsPrimitiveDivisor a m u

theorem IsPrimitiveDivisor.one_le {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitiveDivisor a m u) : 1 ≤ m :=
  h.1

theorem IsPrimitiveDivisor.two_le {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitiveDivisor a m u) : 2 ≤ u :=
  h.2.1

theorem IsPrimitiveDivisor.dvd {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitiveDivisor a m u) : (u : ℤ) ∣ a m :=
  h.2.2.1

theorem IsPrimitiveDivisor.not_dvd_of_lt {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitiveDivisor a m u) {s : ℕ} (hs : 1 ≤ s) (hsm : s < m) :
    ¬ (u : ℤ) ∣ a s :=
  h.2.2.2 s hs hsm

theorem IsPrimitivePrimeDivisor.prime {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitivePrimeDivisor a m u) : Nat.Prime u :=
  h.1

theorem IsPrimitivePrimeDivisor.toIsPrimitiveDivisor {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitivePrimeDivisor a m u) : IsPrimitiveDivisor a m u :=
  h.2

theorem IsPrimitivePrimeDivisor.one_le {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitivePrimeDivisor a m u) : 1 ≤ m :=
  h.toIsPrimitiveDivisor.one_le

theorem IsPrimitivePrimeDivisor.two_le {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitivePrimeDivisor a m u) : 2 ≤ u :=
  h.toIsPrimitiveDivisor.two_le

theorem IsPrimitivePrimeDivisor.dvd {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitivePrimeDivisor a m u) : (u : ℤ) ∣ a m :=
  h.toIsPrimitiveDivisor.dvd

theorem IsPrimitivePrimeDivisor.not_dvd_of_lt {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitivePrimeDivisor a m u) {s : ℕ} (hs : 1 ≤ s) (hsm : s < m) :
    ¬ (u : ℤ) ∣ a s :=
  h.toIsPrimitiveDivisor.not_dvd_of_lt hs hsm

@[simp]
theorem isPrimitivePrimeDivisor_iff {a : ℕ → ℤ} {m u : ℕ} :
    IsPrimitivePrimeDivisor a m u ↔
      Nat.Prime u ∧ 1 ≤ m ∧ 2 ≤ u ∧ (u : ℤ) ∣ a m ∧
        ∀ s : ℕ, 1 ≤ s → s < m → ¬ (u : ℤ) ∣ a s :=
  Iff.rfl

/-- **A primitive divisor appears at the least positive index.** Let $(a_s)_{s \ge 0}$ be a sequence
of integers and let the natural number $u$ be a primitive divisor of $a_m$. If $n \ge 1$ and $u$
divides $a_n$, then $m \le n$. -/
theorem IsPrimitiveDivisor.le_of_dvd {a : ℕ → ℤ} {m u n : ℕ}
    (hm : IsPrimitiveDivisor a m u) (hn : 1 ≤ n) (hdvd : (u : ℤ) ∣ a n) :
    m ≤ n := by
  by_contra hmn
  exact hm.not_dvd_of_lt hn (by omega) hdvd

/-- **A primitive divisor occurs at only one index.** Let $(a_s)_{s \ge 0}$ be a sequence of
integers. If a natural number $u$ is a primitive divisor of both $a_m$ and $a_n$, then $m = n$. -/
theorem IsPrimitiveDivisor.unique {a : ℕ → ℤ} {m n u : ℕ}
    (hm : IsPrimitiveDivisor a m u) (hn : IsPrimitiveDivisor a n u) :
    m = n :=
  le_antisymm (hm.le_of_dvd hn.one_le hn.dvd) (hn.le_of_dvd hm.one_le hm.dvd)

/-- **A primitive prime divisor occurs at only one index.** Let $(a_s)_{s \ge 0}$ be a sequence of
integers. If a natural number $u$ is a primitive prime divisor of both $a_m$ and $a_n$, then
$m = n$. -/
theorem IsPrimitivePrimeDivisor.unique {a : ℕ → ℤ} {m n u : ℕ}
    (hm : IsPrimitivePrimeDivisor a m u) (hn : IsPrimitivePrimeDivisor a n u) :
    m = n :=
  hm.toIsPrimitiveDivisor.unique hn.toIsPrimitiveDivisor

end IntegerSequence
