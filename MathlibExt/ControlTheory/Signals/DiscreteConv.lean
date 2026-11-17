/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Causal finite convolution

For sequences `f g : ℕ → R` valued in a semiring, the causal
convolution is
`(causalConv f g) n = ∑ k ∈ range (n + 1), f k * g (n - k)`: the
output at time `n` depends only on input values at times `≤ n`, and
every value is a finite sum, so no topology or summability side
condition is needed. It agrees with Mathlib's generic discrete
convolution `DiscreteConvolution.addRingConvolution` specialized to
`ℕ` (the `tsum` there is finite on `ℕ`), has the unit sample
`Pi.single 0 1` as a two-sided identity, and is commutative and
associative under the usual hypotheses on the value semiring.
-/

@[expose] public section

namespace ControlTheory

/-- Causal finite convolution of natural-time sequences valued in a
semiring `R`: `(causalConv f g) n = ∑ k ∈ range (n + 1), f k * g (n - k)`.
The output at time `n` depends only on input values at times `≤ n`, and
every value is a finite sum: no topology or summability side condition
is needed. -/
def causalConv {R : Type*} [NonUnitalNonAssocSemiring R] (f g : ℕ → R) :
    ℕ → R :=
  fun n => ∑ k ∈ Finset.range (n + 1), f k * g (n - k)

@[simp]
theorem causalConv_apply {R : Type*} [NonUnitalNonAssocSemiring R]
    (f g : ℕ → R) (n : ℕ) :
    causalConv f g n = ∑ k ∈ Finset.range (n + 1), f k * g (n - k) := by
  rfl

/-- Agreement with Mathlib's generic discrete convolution
(`DiscreteConvolution.addRingConvolution`, the additive-index
ring convolution, specialized to `ℕ`): on `ℕ` the generic
`tsum`-based convolution is the finite causal sum. -/
theorem causalConv_eq_addRingConvolution {R : Type*}
    [NonUnitalNonAssocSemiring R] [TopologicalSpace R] (f g : ℕ → R) :
    causalConv f g = DiscreteConvolution.addRingConvolution f g := by
  ext n
  simp only [causalConv_apply,
    DiscreteConvolution.addRingConvolution_eq_sum_antidiagonal]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => f k * g l) n).symm

@[simp]
theorem zero_causalConv {R : Type*} [NonUnitalNonAssocSemiring R]
    (g : ℕ → R) : causalConv 0 g = 0 := by
  ext n
  simp

@[simp]
theorem causalConv_zero {R : Type*} [NonUnitalNonAssocSemiring R]
    (f : ℕ → R) : causalConv f 0 = 0 := by
  ext n
  simp

/-- Unit-sample identity, left: convolution with the unit sample
`Pi.single 0 1` (the sequence that is `1` at time `0` and `0`
elsewhere) is the identity. -/
theorem single_zero_causalConv {R : Type*} [NonAssocSemiring R]
    (f : ℕ → R) : causalConv (Pi.single 0 1) f = f := by
  ext n
  simp only [causalConv_apply]
  rw [Finset.sum_eq_single_of_mem (a := 0) (Finset.mem_range.mpr (Nat.zero_lt_succ n))]
  · simp
  · intro b _ hb
    simp [hb]

/-- Unit-sample identity, right. -/
theorem causalConv_single_zero {R : Type*} [NonAssocSemiring R]
    (f : ℕ → R) : causalConv f (Pi.single 0 1) = f := by
  ext n
  simp only [causalConv_apply]
  rw [Finset.sum_eq_single_of_mem (a := n) (Finset.mem_range.mpr (Nat.lt_succ_self n))]
  · simp
  · intro b hb hbn
    have hle : b ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hne : n - b ≠ 0 := by omega
    simp [Pi.single_eq_of_ne hne]

/-- Causal convolution is commutative when the value multiplication
is. -/
theorem causalConv_comm {R : Type*} [NonUnitalNonAssocCommSemiring R]
    (f g : ℕ → R) : causalConv f g = causalConv g f := by
  ext n
  simp only [causalConv_apply]
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

private theorem causalConv_triangular_sum (R : Type*) [AddCommMonoid R]
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

/-- Causal convolution is associative over a semiring. -/
theorem causalConv_assoc {R : Type*} [Semiring R] (f g h : ℕ → R) :
    causalConv (causalConv f g) h = causalConv f (causalConv g h) := by
  ext n
  simp only [causalConv_apply]
  have hTri := causalConv_triangular_sum R (fun i j => (f i * g j) * h (n - i - j)) n
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

end ControlTheory
