/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic

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

/-- Membership in `𝓔ₙ^≤` from Kovač–Tang, lines 103–107:
a tuple of natural numbers with `2 ≤ a₁ ≤ ⋯ ≤ aₙ`. -/
def IsNondecreasingEgyptian {n : ℕ} (a : Fin n → ℕ) : Prop :=
  (∀ i, 2 ≤ a i) ∧ Monotone a

/-- Membership in `𝓔ₙ^<` from Kovač–Tang, lines 108–110:
a tuple of natural numbers with `2 ≤ a₁ < ⋯ < aₙ`. -/
def IsStrictEgyptian {n : ℕ} (a : Fin n → ℕ) : Prop :=
  (∀ i, 2 ≤ a i) ∧ StrictMono a

/-- A strict underapproximation by unit fractions whose denominators may repeat
and are presented in nondecreasing order. This is the condition
`(a₁,…,aₙ) ∈ 𝓔ₙ^≤` and `∑ 1/aᵢ < λ` from lines 113–120, together with
`n ≥ 1` and `λ > 0` as in the paper's `ℕ = {1,2,…}` and `λ > 0` setup. -/
def IsNondecreasingUnderapproximation {n : ℕ} (target : ℝ) (a : Fin n → ℕ) : Prop :=
  0 < n ∧
    0 < target ∧
    IsNondecreasingEgyptian a ∧
    ∑ i, ((a i : ℝ)⁻¹) < target

/-- A strict underapproximation by distinct unit fractions, presented with
strictly increasing denominators. This is the condition
`(a₁,…,aₙ) ∈ 𝓔ₙ^<` and `∑ 1/aᵢ < λ` from lines 113–120, with `n ≥ 1`
and `λ > 0`. -/
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

/-- A nondecreasing underapproximation has at least one term (`n ≥ 1`). -/
theorem nonempty {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsNondecreasingUnderapproximation target a) : 0 < n :=
  h.1

/-- The target of a nondecreasing underapproximation is positive. -/
theorem target_pos {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsNondecreasingUnderapproximation target a) : 0 < target :=
  h.2.1

/-- The denominator tuple lies in `𝓔ₙ^≤`. -/
theorem isNondecreasingEgyptian {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsNondecreasingUnderapproximation target a) : IsNondecreasingEgyptian a :=
  h.2.2.1

/-- Every denominator in a nondecreasing underapproximation is at least two. -/
theorem denominator_ge_two {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsNondecreasingUnderapproximation target a) (i : Fin n) : 2 ≤ a i :=
  h.isNondecreasingEgyptian.1 i

/-- The denominators of a nondecreasing underapproximation are monotone. -/
theorem monotone {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsNondecreasingUnderapproximation target a) : Monotone a :=
  h.isNondecreasingEgyptian.2

/-- The reciprocal sum of a nondecreasing underapproximation is below its target. -/
theorem sum_lt {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsNondecreasingUnderapproximation target a) :
    ∑ i, ((a i : ℝ)⁻¹) < target :=
  h.2.2.2

end IsNondecreasingUnderapproximation

namespace IsStrictUnderapproximation

/-- A strict underapproximation has at least one term (`n ≥ 1`). -/
theorem nonempty {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsStrictUnderapproximation target a) : 0 < n :=
  h.1

/-- The target of a strict underapproximation is positive. -/
theorem target_pos {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsStrictUnderapproximation target a) : 0 < target :=
  h.2.1

/-- The denominator tuple lies in `𝓔ₙ^<`. -/
theorem isStrictEgyptian {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsStrictUnderapproximation target a) : IsStrictEgyptian a :=
  h.2.2.1

/-- Every denominator in a strict underapproximation is at least two. -/
theorem denominator_ge_two {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsStrictUnderapproximation target a) (i : Fin n) : 2 ≤ a i :=
  h.isStrictEgyptian.1 i

/-- The denominators of a strict underapproximation are strictly monotone. -/
theorem strictMono {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsStrictUnderapproximation target a) : StrictMono a :=
  h.isStrictEgyptian.2

/-- The reciprocal sum of a strict underapproximation is below its target. -/
theorem sum_lt {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsStrictUnderapproximation target a) :
    ∑ i, ((a i : ℝ)⁻¹) < target :=
  h.2.2.2

/-- Every nondecreasing denominator tuple containing a strictly increasing one
is itself nondecreasing; hence a strict underapproximation is also a
nondecreasing underapproximation (paper's `𝓔ₙ^< ⊆ 𝓔ₙ^≤` together with the
same sum bound). -/
theorem toIsNondecreasingUnderapproximation {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : IsStrictUnderapproximation target a) :
    IsNondecreasingUnderapproximation target a :=
  ⟨h.nonempty, h.target_pos, h.isStrictEgyptian.toIsNondecreasingEgyptian, h.sum_lt⟩

end IsStrictUnderapproximation

end EgyptianFraction
