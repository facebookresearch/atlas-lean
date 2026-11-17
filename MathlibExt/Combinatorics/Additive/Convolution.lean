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

/-- The sum convolution of two functions `f, g : ℕ → R`, also known as the Cauchy product.
`sumConv f g n = ∑_{a+b=n} f(a)g(b)`. -/
def sumConv (f g : ℕ → R) (n : ℕ) : R := ∑ p ∈ antidiagonal n, f p.1 * g p.2

/-- Total of the sum convolution over the padded horizon
 (one trailing zero step), for finitely
supported `f` and `g`: the sum of `sumConv f g` over `range (n + m)` is
the product of the totals. No commutativity is needed. -/
theorem sum_range_sumConv (f g : ℕ → R) {n m : ℕ}
    (hf : ∀ i : ℕ, n ≤ i → f i = 0) (hg : ∀ j : ℕ, m ≤ j → g j = 0) :
    ∑ k ∈ Finset.range (n + m), sumConv f g k
      = (∑ i ∈ Finset.range n, f i) * (∑ j ∈ Finset.range m, g j) := by
  simp only [sumConv]
  have hdisj : (↑(Finset.range (n + m)) : Set ℕ).PairwiseDisjoint Finset.antidiagonal := by
    intro x _ y _ hxy
    show Disjoint (Finset.antidiagonal x) (Finset.antidiagonal y)
    rw [Finset.disjoint_left]
    intro p hp hqp
    rw [Finset.mem_antidiagonal] at hp hqp
    exact hxy (hp.symm.trans hqp)
  have hbi : ∑ x ∈ (Finset.range (n + m)).biUnion Finset.antidiagonal, f x.1 * g x.2
      = ∑ k ∈ Finset.range (n + m), ∑ ij ∈ Finset.antidiagonal k, f ij.1 * g ij.2 :=
    Finset.sum_biUnion hdisj
  have hsub : (Finset.range n) ×ˢ (Finset.range m)
      ⊆ (Finset.range (n + m)).biUnion Finset.antidiagonal := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    obtain ⟨hi, hj⟩ := hp
    rw [Finset.mem_biUnion]
    exact ⟨p.1 + p.2, Finset.mem_range.mpr (by omega), Finset.mem_antidiagonal.mpr rfl⟩
  have hvan : ∀ x ∈ (Finset.range (n + m)).biUnion Finset.antidiagonal,
      x ∉ (Finset.range n) ×ˢ (Finset.range m) → f x.1 * g x.2 = 0 := by
    intro x _ hx
    simp only [Finset.mem_product, Finset.mem_range, not_and, not_lt] at hx
    by_cases h1 : x.1 < n
    · rw [hg x.2 (hx h1), mul_zero]
    · rw [hf x.1 (not_lt.mp h1), zero_mul]
  have hss : ∑ x ∈ (Finset.range n) ×ˢ (Finset.range m), f x.1 * g x.2
      = ∑ x ∈ (Finset.range (n + m)).biUnion Finset.antidiagonal, f x.1 * g x.2 :=
    Finset.sum_subset hsub hvan
  have hprod : ∑ x ∈ (Finset.range n) ×ˢ (Finset.range m), f x.1 * g x.2
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, f i * g j :=
    Finset.sum_product _ _ _
  have hmul : (∑ i ∈ Finset.range n, f i) * (∑ j ∈ Finset.range m, g j)
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, f i * g j :=
    Finset.sum_mul_sum _ _ _ _
  rw [← hbi, ← hss, hprod, ← hmul]

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
