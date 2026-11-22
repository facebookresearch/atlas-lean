/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Monotone.Basic

/-!
Complementary sequences determined by subsequence-sum equations.

Concept `jis_sem_c59328d30afb85fa4bde030d`
(canonical name: complementary sequence determined by subsequence-sum equation).
Source statements `jis_a728ee017c7adb1e5151b44f`, `jis_d5c85a6cd10b01207e0aa227`,
`jis_f769f4ddb64ff3cef3f34a43` are definition context only; the surrounding
conjecture/theorem conclusions (linear recurrences, closed forms) are excluded.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Complementary pair of sequences.** Two sequences $a, b : \mathbb{N} \to \mathbb{N}$, indexed
from $0$, form a complementary pair when all their terms are positive, both are strictly
increasing, no term of $a$ equals a term of $b$, and every positive integer is a term of $a$ or
a term of $b$. In particular, the ranges of $a$ and $b$ partition the positive integers.

Source: concept `jis_sem_c59328d30afb85fa4bde030d`; statements `jis_a728ee017c7adb1e5151b44f`,
`jis_d5c85a6cd10b01207e0aa227`, `jis_f769f4ddb64ff3cef3f34a43`. -/
public def IsComplementaryPair (a b : ℕ → ℕ) : Prop :=
  (∀ n, 0 < a n) ∧ (∀ n, 0 < b n) ∧
    StrictMono a ∧ StrictMono b ∧
    (∀ m n, a m ≠ b n) ∧
    ∀ n, 0 < n → (∃ m, a m = n) ∨ (∃ m, b m = n)

/-- **The subsequence-sum equation $a_n = b_{hn} + b_{khn}$.** Sequences
$a, b : \mathbb{N} \to \mathbb{N}$ and natural numbers $h$ and $k$ satisfy the parametrized
subsequence-sum equation when $h \ge 2$, $k \ge 2$, $b_0 = 1$, and $a_n = b_{hn} + b_{khn}$ for
every $n \in \mathbb{N}$.

Source: concept `jis_sem_c59328d30afb85fa4bde030d`;
statement `jis_a728ee017c7adb1e5151b44f`. -/
public def SatisfiesParametrizedSumEquation (a b : ℕ → ℕ) (h k : ℕ) : Prop :=
  2 ≤ h ∧ 2 ≤ k ∧ b 0 = 1 ∧ ∀ n, a n = b (h * n) + b (k * h * n)

/-- **The subsequence-sum equation $a_n = b_{2n} + b_{4n}$.** Sequences
$a, b : \mathbb{N} \to \mathbb{N}$ satisfy this equation when $b_0 = 1$ and
$a_n = b_{2n} + b_{4n}$ for every $n \in \mathbb{N}$.

Source: concept `jis_sem_c59328d30afb85fa4bde030d`;
statement `jis_d5c85a6cd10b01207e0aa227`. -/
public def SatisfiesBaseSumEquation (a b : ℕ → ℕ) : Prop :=
  b 0 = 1 ∧ ∀ n, a n = b (2 * n) + b (4 * n)

/-- **The subsequence-sum equation $a_n = b_{2n} + b_{4n} + 1$.** Sequences
$a, b : \mathbb{N} \to \mathbb{N}$ satisfy this equation when $b_0 = 1$ and
$a_n = b_{2n} + b_{4n} + 1$ for every $n \in \mathbb{N}$.

Source: concept `jis_sem_c59328d30afb85fa4bde030d`;
statement `jis_f769f4ddb64ff3cef3f34a43`. -/
public def SatisfiesShiftedSumEquation (a b : ℕ → ℕ) : Prop :=
  b 0 = 1 ∧ ∀ n, a n = b (2 * n) + b (4 * n) + 1

/-- **Complementary pair determined by $a_n = b_{hn} + b_{khn}$.** Sequences
$a, b : \mathbb{N} \to \mathbb{N}$ form a complementary pair determined by this equation with
natural-number parameters $h$ and $k$ when they form a complementary pair (both strictly
increasing with positive terms, and every positive integer is a term of exactly one of them),
$h \ge 2$, $k \ge 2$, $b_0 = 1$, and $a_n = b_{hn} + b_{khn}$ for every $n \in \mathbb{N}$.

Source: concept `jis_sem_c59328d30afb85fa4bde030d`;
statement `jis_a728ee017c7adb1e5151b44f`. -/
public def IsComplementaryDeterminedByParametrizedSumEquation
    (a b : ℕ → ℕ) (h k : ℕ) : Prop :=
  IsComplementaryPair a b ∧ SatisfiesParametrizedSumEquation a b h k

/-- **Complementary pair determined by $a_n = b_{2n} + b_{4n}$.** Sequences
$a, b : \mathbb{N} \to \mathbb{N}$ form a complementary pair determined by this equation when they
form a complementary pair (both strictly increasing with positive terms, and every positive
integer is a term of exactly one of them) and they satisfy $b_0 = 1$ and $a_n = b_{2n} + b_{4n}$
for every $n \in \mathbb{N}$.

Source: concept `jis_sem_c59328d30afb85fa4bde030d`;
statement `jis_d5c85a6cd10b01207e0aa227`. -/
public def IsComplementaryDeterminedByBaseSumEquation (a b : ℕ → ℕ) : Prop :=
  IsComplementaryPair a b ∧ SatisfiesBaseSumEquation a b

/-- **Complementary pair determined by $a_n = b_{2n} + b_{4n} + 1$.** Sequences
$a, b : \mathbb{N} \to \mathbb{N}$ form a complementary pair determined by this equation when they
form a complementary pair (both strictly increasing with positive terms, and every positive
integer is a term of exactly one of them) and they satisfy $b_0 = 1$ and
$a_n = b_{2n} + b_{4n} + 1$ for every $n \in \mathbb{N}$.

Source: concept `jis_sem_c59328d30afb85fa4bde030d`;
statement `jis_f769f4ddb64ff3cef3f34a43`. -/
public def IsComplementaryDeterminedByShiftedSumEquation (a b : ℕ → ℕ) : Prop :=
  IsComplementaryPair a b ∧ SatisfiesShiftedSumEquation a b

end

end MetaMathlibExt
