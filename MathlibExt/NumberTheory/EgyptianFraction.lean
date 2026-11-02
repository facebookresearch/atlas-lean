/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Egyptian underapproximations

This module records the two denominator-order conventions for finite Egyptian
underapproximations from Kovač–Tang: nondecreasing denominators
(repetitions allowed) and strictly increasing denominators (distinct
denominators), together with the strict-underapproximation condition
`∑ 1/a_i < λ`.

## Main definitions

* `EgyptianFraction.IsNondecreasingEgyptian` membership in `𝓔ₙ^≤`
* `EgyptianFraction.IsStrictEgyptian` membership in `𝓔ₙ^<`
* `EgyptianFraction.IsNondecreasingUnderapproximation`
* `EgyptianFraction.IsStrictUnderapproximation`

## References

* V. Kovač and Q. Tang, *Eventually greedy best Egyptian underapproximations of rational
  numbers via optimal control*, [arXiv:2607.28387v2](https://arxiv.org/abs/2607.28387v2),
  lines 103–120. The superscripts `≤` and `<` in the paper correspond to
  nondecreasing and strictly increasing denominator tuples respectively; for
  `λ > 0` and `σ ∈ {≤, <}`,
  `Rₙ^σ(λ) = max {∑ 1/aᵢ : (a₁,…,aₙ) ∈ 𝓔ₙ^σ, ∑ 1/aᵢ < λ}`.
-/

open scoped BigOperators

namespace EgyptianFraction

/-- **Nondecreasing Egyptian denominator tuples.** A tuple $(a_1, \dots, a_n)$ of natural
numbers lies in $\mathcal{E}_n^{\le}$ when $2 \le a_1 \le a_2 \le \dots \le a_n$, that is, every
$a_i$ is at least $2$ and the tuple is nondecreasing.

Source: Kovač–Tang, arXiv:2607.28387v2, lines 103–107. -/
def IsNondecreasingEgyptian {n : ℕ} (a : Fin n → ℕ) : Prop :=
  (∀ i, 2 ≤ a i) ∧ Monotone a

/-- **Strictly increasing Egyptian denominator tuples.** A tuple $(a_1, \dots, a_n)$ of natural
numbers lies in $\mathcal{E}_n^{<}$ when $2 \le a_1 < a_2 < \dots < a_n$, that is, every $a_i$ is
at least $2$ and the tuple is strictly increasing.

Source: Kovač–Tang, arXiv:2607.28387v2, lines 108–110. -/
def IsStrictEgyptian {n : ℕ} (a : Fin n → ℕ) : Prop :=
  (∀ i, 2 ≤ a i) ∧ StrictMono a

/-- **Egyptian underapproximations with nondecreasing denominators.** Let $\lambda$ be a real
number and $a = (a_1, \dots, a_n)$ a tuple of natural numbers. Then $a$ is a nondecreasing
underapproximation of $\lambda$ when $n \ge 1$, $\lambda > 0$, $a$ lies in
$\mathcal{E}_n^{\le}$ (that is, $2 \le a_1 \le \dots \le a_n$), and
$\sum_{i=1}^{n} 1/a_i < \lambda$, the sum taken in the real numbers.

Source: Kovač–Tang, arXiv:2607.28387v2, lines 113–120; $n \ge 1$ and $\lambda > 0$ follow the
paper's conventions. -/
def IsNondecreasingUnderapproximation {n : ℕ} (target : ℝ) (a : Fin n → ℕ) : Prop :=
  0 < n ∧
    0 < target ∧
    IsNondecreasingEgyptian a ∧
    ∑ i, ((a i : ℝ)⁻¹) < target

/-- **Egyptian underapproximations with strictly increasing denominators.** Let $\lambda$ be a
real number and $a = (a_1, \dots, a_n)$ a tuple of natural numbers. Then $a$ is a strict
underapproximation of $\lambda$ when $n \ge 1$, $\lambda > 0$, $a$ lies in $\mathcal{E}_n^{<}$
(that is, $2 \le a_1 < \dots < a_n$, so the unit fractions are distinct), and
$\sum_{i=1}^{n} 1/a_i < \lambda$, the sum taken in the real numbers.

Source: Kovač–Tang, arXiv:2607.28387v2, lines 113–120. -/
def IsStrictUnderapproximation {n : ℕ} (target : ℝ) (a : Fin n → ℕ) : Prop :=
  0 < n ∧
    0 < target ∧
    IsStrictEgyptian a ∧
    ∑ i, ((a i : ℝ)⁻¹) < target

namespace IsNondecreasingEgyptian

theorem denominator_ge_two {n : ℕ} {a : Fin n → ℕ}
    (h : IsNondecreasingEgyptian a) (i : Fin n) : 2 ≤ a i :=
  h.1 i

theorem monotone {n : ℕ} {a : Fin n → ℕ}
    (h : IsNondecreasingEgyptian a) : Monotone a :=
  h.2

end IsNondecreasingEgyptian

namespace IsStrictEgyptian

theorem denominator_ge_two {n : ℕ} {a : Fin n → ℕ}
    (h : IsStrictEgyptian a) (i : Fin n) : 2 ≤ a i :=
  h.1 i

theorem strictMono {n : ℕ} {a : Fin n → ℕ}
    (h : IsStrictEgyptian a) : StrictMono a :=
  h.2

theorem toIsNondecreasingEgyptian {n : ℕ} {a : Fin n → ℕ}
    (h : IsStrictEgyptian a) : IsNondecreasingEgyptian a :=
  ⟨h.1, h.strictMono.monotone⟩

end IsStrictEgyptian

namespace IsNondecreasingUnderapproximation

/-- **Nondecreasing underapproximations have at least one term.** Let $n$ be a natural number,
$\lambda$ a real number and $a_1, \dots, a_n$ natural numbers. If $(a_1, \dots, a_n)$ is a
nondecreasing underapproximation of $\lambda$, then $n \ge 1$. -/
theorem nonempty {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsNondecreasingUnderapproximation target a) : 0 < n :=
  h.1

/-- **The target of a nondecreasing underapproximation is positive.** Let $n$ be a natural
number, $\lambda$ a real number and $a_1, \dots, a_n$ natural numbers. If $(a_1, \dots, a_n)$
is a nondecreasing underapproximation of $\lambda$, then $\lambda > 0$. -/
theorem target_pos {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsNondecreasingUnderapproximation target a) : 0 < target :=
  h.2.1

/-- **Nondecreasing underapproximations have Egyptian denominator tuples.** If
$a = (a_1, \dots, a_n)$ is a nondecreasing underapproximation of a real number $\lambda$, then
$a$ lies in $\mathcal{E}_n^{\le}$, that is, $2 \le a_1 \le \dots \le a_n$. -/
theorem isNondecreasingEgyptian {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsNondecreasingUnderapproximation target a) : IsNondecreasingEgyptian a :=
  h.2.2.1

/-- **Denominators of a nondecreasing underapproximation are at least two.** Let $n$ be a
natural number, $\lambda$ a real number and $a_1, \dots, a_n$ natural numbers. If
$(a_1, \dots, a_n)$ is a nondecreasing underapproximation of $\lambda$, then $a_i \ge 2$ for
every $1 \le i \le n$. -/
theorem denominator_ge_two {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsNondecreasingUnderapproximation target a) (i : Fin n) : 2 ≤ a i :=
  h.isNondecreasingEgyptian.1 i

/-- **Denominators of a nondecreasing underapproximation are nondecreasing.** Let $n$ be a
natural number, $\lambda$ a real number and $a_1, \dots, a_n$ natural numbers. If
$(a_1, \dots, a_n)$ is a nondecreasing underapproximation of $\lambda$, then $a_i \le a_j$
whenever $1 \le i \le j \le n$. -/
theorem monotone {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsNondecreasingUnderapproximation target a) : Monotone a :=
  h.isNondecreasingEgyptian.2

/-- **A nondecreasing underapproximation stays below its target.** Let $n$ be a natural number,
$\lambda$ a real number and $a_1, \dots, a_n$ natural numbers. If $(a_1, \dots, a_n)$ is a
nondecreasing underapproximation of $\lambda$, then $\sum_{i=1}^{n} 1/a_i < \lambda$. -/
theorem sum_lt {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsNondecreasingUnderapproximation target a) :
    ∑ i, ((a i : ℝ)⁻¹) < target :=
  h.2.2.2

end IsNondecreasingUnderapproximation

namespace IsStrictUnderapproximation

/-- **Strict underapproximations have at least one term.** Let $n$ be a natural number,
$\lambda$ a real number and $a_1, \dots, a_n$ natural numbers. If $(a_1, \dots, a_n)$ is a
strict underapproximation of $\lambda$, then $n \ge 1$. -/
theorem nonempty {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsStrictUnderapproximation target a) : 0 < n :=
  h.1

/-- **The target of a strict underapproximation is positive.** Let $n$ be a natural number,
$\lambda$ a real number and $a_1, \dots, a_n$ natural numbers. If $(a_1, \dots, a_n)$ is a
strict underapproximation of $\lambda$, then $\lambda > 0$. -/
theorem target_pos {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsStrictUnderapproximation target a) : 0 < target :=
  h.2.1

/-- **Strict underapproximations have strictly increasing Egyptian denominators.** If
$a = (a_1, \dots, a_n)$ is a strict underapproximation of a real number $\lambda$, then $a$ lies
in $\mathcal{E}_n^{<}$, that is, $2 \le a_1 < \dots < a_n$. -/
theorem isStrictEgyptian {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsStrictUnderapproximation target a) : IsStrictEgyptian a :=
  h.2.2.1

/-- **Denominators of a strict underapproximation are at least two.** Let $n$ be a natural
number, $\lambda$ a real number and $a_1, \dots, a_n$ natural numbers. If $(a_1, \dots, a_n)$
is a strict underapproximation of $\lambda$, then $a_i \ge 2$ for every $1 \le i \le n$. -/
theorem denominator_ge_two {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsStrictUnderapproximation target a) (i : Fin n) : 2 ≤ a i :=
  h.isStrictEgyptian.1 i

/-- **Denominators of a strict underapproximation increase strictly.** Let $n$ be a natural
number, $\lambda$ a real number and $a_1, \dots, a_n$ natural numbers. If $(a_1, \dots, a_n)$
is a strict underapproximation of $\lambda$, then $a_i < a_j$ whenever $1 \le i < j \le n$. -/
theorem strictMono {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsStrictUnderapproximation target a) : StrictMono a :=
  h.isStrictEgyptian.2

/-- **A strict underapproximation stays below its target.** Let $n$ be a natural number,
$\lambda$ a real number and $a_1, \dots, a_n$ natural numbers. If $(a_1, \dots, a_n)$ is a
strict underapproximation of $\lambda$, then $\sum_{i=1}^{n} 1/a_i < \lambda$, the sum taken in
the real numbers. -/
theorem sum_lt {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsStrictUnderapproximation target a) :
    ∑ i, ((a i : ℝ)⁻¹) < target :=
  h.2.2.2

/-- **Strict underapproximations are nondecreasing underapproximations.** Let $n$ be a natural
number, $\lambda$ a real number and $a_1, \dots, a_n$ natural numbers. If $(a_1, \dots, a_n)$
is a strict underapproximation of $\lambda$, then it is also a nondecreasing
underapproximation of $\lambda$.

This is the inclusion of strictly increasing denominator tuples among nondecreasing ones,
together with the same bound on the sum of reciprocals. -/
theorem toIsNondecreasingUnderapproximation {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsStrictUnderapproximation target a) :
    IsNondecreasingUnderapproximation target a :=
  ⟨h.nonempty, h.target_pos, h.isStrictEgyptian.toIsNondecreasingEgyptian, h.sum_lt⟩

end IsStrictUnderapproximation

end EgyptianFraction
