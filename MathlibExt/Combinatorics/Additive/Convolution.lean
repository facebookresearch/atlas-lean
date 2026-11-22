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
public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal

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
def sumConv {R : Type*} [NonUnitalNonAssocSemiring R] (f g : ℕ → R) (n : ℕ) : R := ∑ p ∈ antidiagonal n, f p.1 * g p.2

/-- Total of the sum convolution over the padded horizon
`range (n + m)` (one trailing zero step), for finitely
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

/-- Agreement with Mathlib's generic discrete convolution
(`DiscreteConvolution.addRingConvolution`, the additive-index
ring convolution, specialized to `ℕ`): on `ℕ` the generic
`tsum`-based convolution is the finite sum convolution. -/
theorem sumConv_eq_addRingConvolution {R : Type*}
    [NonUnitalNonAssocSemiring R] [TopologicalSpace R] (f g : ℕ → R) :
    sumConv f g = DiscreteConvolution.addRingConvolution f g := by
  ext n
  simp only [DiscreteConvolution.addRingConvolution_eq_sum_antidiagonal]
  rfl

/-- The explicit finite range formula for the sum convolution. -/
@[simp]
theorem sumConv_apply {R : Type*} [NonUnitalNonAssocSemiring R]
    (f g : ℕ → R) (n : ℕ) :
    sumConv f g n = ∑ k ∈ Finset.range (n + 1), f k * g (n - k) := by
  have h : sumConv f g n =
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p.1 * g p.2 := rfl
  rw [h]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => f k * g l) n

@[simp]
theorem zero_sumConv {R : Type*} [NonUnitalNonAssocSemiring R]
    (g : ℕ → R) : sumConv 0 g = 0 := by
  ext n
  simp

@[simp]
theorem sumConv_zero {R : Type*} [NonUnitalNonAssocSemiring R]
    (f : ℕ → R) : sumConv f 0 = 0 := by
  ext n
  simp

/-- Unit-sample identity, left: convolution with the unit sample
`Pi.single 0 1` (the sequence that is `1` at time `0` and `0`
elsewhere) is the identity. -/
theorem single_zero_sumConv {R : Type*} [NonAssocSemiring R]
    (f : ℕ → R) : sumConv (Pi.single 0 1) f = f := by
  ext n
  simp only [sumConv_apply]
  rw [Finset.sum_eq_single_of_mem (a := 0) (Finset.mem_range.mpr (Nat.zero_lt_succ n))]
  · simp
  · intro b _ hb
    simp [hb]

/-- Unit-sample identity, right. -/
theorem sumConv_single_zero {R : Type*} [NonAssocSemiring R]
    (f : ℕ → R) : sumConv f (Pi.single 0 1) = f := by
  ext n
  simp only [sumConv_apply]
  rw [Finset.sum_eq_single_of_mem (a := n) (Finset.mem_range.mpr (Nat.lt_succ_self n))]
  · simp
  · intro b hb hbn
    have hle : b ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hne : n - b ≠ 0 := by omega
    simp [Pi.single_eq_of_ne hne]

/-- The sum convolution is commutative when the value multiplication
is. -/
theorem sumConv_comm {R : Type*} [NonUnitalNonAssocCommSemiring R]
    (f g : ℕ → R) : sumConv f g = sumConv g f := by
  ext n
  simp only [sumConv_apply]
  have h := Finset.sum_range_reflect (fun k => f k * g (n - k)) (n + 1)
  rw [← h]
  apply Finset.sum_congr rfl
  intro k hk
  have hle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have h1 : n + 1 - 1 - k = n - k := by omega
  rw [h1]
  have h2 : n - (n - k) = k := Nat.sub_sub_self hle
  rw [h2]
  exact mul_comm _ _

private theorem sumConv_triangular_sum (R : Type*) [AddCommMonoid R]
    (F : ℕ → ℕ → R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (k + 1), F i (k - i) =
    ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n - i + 1), F i j := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ (fun k => ∑ i ∈ Finset.range (k + 1), F i (k - i)) (n + 1)]
    rw [Finset.sum_range_succ (fun i => ∑ j ∈ Finset.range ((n + 1) - i + 1), F i j) (n + 1)]
    have hT : (∑ j ∈ Finset.range ((n + 1) - (n + 1) + 1), F (n + 1) j) = F (n + 1) 0 := by
      simp
    rw [hT]
    have hTinner : ∀ i ∈ Finset.range (n + 1),
        (∑ j ∈ Finset.range ((n + 1) - i + 1), F i j) =
        (∑ j ∈ Finset.range (n - i + 1), F i j) + F i (n - i + 1) := by
      intro i hi
      have hle : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have heq : (n + 1) - i + 1 = (n - i + 1) + 1 := by omega
      rw [heq]
      exact Finset.sum_range_succ _ _
    have hSumEq : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range ((n + 1) - i + 1), F i j) =
        (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n - i + 1), F i j) +
        (∑ i ∈ Finset.range (n + 1), F i (n - i + 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact hTinner i hi
    rw [hSumEq]
    rw [← ih]
    have hS : (∑ i ∈ Finset.range ((n + 1) + 1), F i ((n + 1) - i)) =
        (∑ i ∈ Finset.range (n + 1), F i (n - i + 1)) + F (n + 1) 0 := by
      rw [Finset.sum_range_succ (fun i => F i ((n + 1) - i)) (n + 1)]
      have hlast : F (n + 1) ((n + 1) - (n + 1)) = F (n + 1) 0 := by simp
      rw [hlast]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hle : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have heq : (n + 1) - i = n - i + 1 := by omega
      rw [heq]
    rw [hS]
    ac_rfl

/-- The sum convolution is associative over any (not necessarily
unital) semiring: the proof uses only distributivity, additive
commutativity, and associativity of the value multiplication. -/
theorem sumConv_assoc {R : Type*} [NonUnitalSemiring R] (f g h : ℕ → R) :
    sumConv (sumConv f g) h = sumConv f (sumConv g h) := by
  ext n
  simp only [sumConv_apply]
  have hTri := sumConv_triangular_sum R (fun i j => (f i * g j) * h (n - i - j)) n
  calc
    ∑ k ∈ Finset.range (n + 1), (∑ i ∈ Finset.range (k + 1), f i * g (k - i)) * h (n - k)
        = ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (k + 1),
          (fun i j => (f i * g j) * h (n - i - j)) i (k - i) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hle : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have heq : n - k = n - i - (k - i) := by omega
      rw [heq]
    _ = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n - i + 1),
          (f i * g j) * h (n - i - j) := hTri
    _ = ∑ k ∈ Finset.range (n + 1),
          f k * (∑ j ∈ Finset.range (n - k + 1), g j * h (n - k - j)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact mul_assoc _ _ _

end AdditiveCombinatorics
