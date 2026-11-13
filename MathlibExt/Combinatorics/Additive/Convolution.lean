/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import MathlibExt.Algebra.Group.Indicator
public import MathlibExt.Combinatorics.Additive.RepresentationCount
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

/-!
# Convolution of Functions on ℕ

This file defines the sum convolution of functions `ℕ → R`.

## Main Definitions
* `AdditiveCombinatorics.sumConv`: The sum convolution of two functions.

## TODO

* `f ∘ g` for `diffConv f g`.
-/


namespace AdditiveCombinatorics

open Finset Set

variable {R : Type*} [Semiring R]

/-- **Sum convolution.** Let $R$ be a semiring. The sum convolution, or Cauchy product, of two
functions $f, g \colon \mathbb{N} \to R$ is the function $\mathbb{N} \to R$ whose value at
$n \in \mathbb{N}$ is
$$\sum_{a + b = n} f(a)\, g(b),$$
where the sum runs over all pairs $(a, b)$ of natural numbers with $a + b = n$. -/
def sumConv (f g : ℕ → R) (n : ℕ) : R := ∑ p ∈ antidiagonal n, f p.1 * g p.2

open PowerSeries

theorem orderedRepresentationCount_eq_powerSeries_coeff (A : Set ℕ) (n : ℕ) :
    (orderedRepresentationCount A n : ℕ) =
    ((PowerSeries.mk (𝟙_A)) * (PowerSeries.mk (𝟙_A)) : PowerSeries ℕ).coeff n := by
  classical
  unfold orderedRepresentationCount
  simp only [indicatorOne, indicator, PowerSeries.coeff_mul, PowerSeries.coeff_mk,
    mul_ite, mul_one, mul_zero]
  push_cast [← ite_and, card_filter, and_comm]
  congr!

end AdditiveCombinatorics
