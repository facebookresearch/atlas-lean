/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring

/-!
# Explicit formula for an inhomogeneous linear recurrence

Let `P` be the generating polynomial of the recurrence coefficients. Multiplication by
`1 - P` sends the generating series of the normalized homogeneous solution to `X ^ (k - 1)`.
Applied to the series starting at `G k`, it leaves the forcing terms and the contributions
from the initial values. Convolving these contributions with the homogeneous solution
therefore gives the series starting at `G k` multiplied by `X ^ (k - 1)`.
-/

namespace MetaMathlibExt

open Finset PowerSeries

namespace linearRecurrence_inhomogeneous_explicit

private lemma coeff_product (a b : ℕ → ℂ) (m : ℕ) :
    coeff m (PowerSeries.mk a * PowerSeries.mk b) =
      ∑ i ∈ range (m + 1), a i * b (m - i) := by
  simp only [coeff_mul, coeff_mk]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ a i * b j) m

private noncomputable def lagSeries (k : ℕ) (A : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun i ↦ if i ∈ Icc 1 k then A i else 0

private lemma coeff_lagSeries_mul (k : ℕ) (A s : ℕ → ℂ) (m : ℕ) :
    coeff m (lagSeries k A * PowerSeries.mk s) =
      ∑ i ∈ Icc 1 k with i ≤ m, A i * s (m - i) := by
  rw [lagSeries, coeff_product]
  simp only [ite_mul, zero_mul, ← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range, mem_Icc]
  omega

private lemma fundamental_series {k : ℕ} (hk : 0 < k) (A f : ℕ → ℂ)
    (hf : ∀ m, k ≤ m → f m = ∑ i ∈ Icc 1 k, A i * f (m - i))
    (hf₀ : ∀ j, j + 1 < k → f j = 0) (hf₁ : f (k - 1) = 1) :
    PowerSeries.mk f - lagSeries k A * PowerSeries.mk f = X ^ (k - 1) := by
  apply PowerSeries.ext
  intro m
  rw [map_sub, coeff_mk, coeff_lagSeries_mul, coeff_X_pow]
  by_cases hm : k ≤ m
  · rw [filter_true_of_mem (fun i hi ↦ (mem_Icc.mp hi).2.trans hm), ← hf m hm,
      sub_self, ite_eq_right (by omega)]
  · have hz : (∑ i ∈ Icc 1 k with i ≤ m, A i * f (m - i)) = 0 := by
      apply sum_eq_zero
      intro i hi
      obtain ⟨hi, him⟩ := mem_filter.mp hi
      have := (mem_Icc.mp hi).1
      rw [hf₀ _ (by omega), mul_zero]
    rw [hz, sub_zero]
    split_ifs with h
    · exact h ▸ hf₁
    · exact hf₀ _ (by omega)

private lemma tail_series (k : ℕ) (A G w : ℕ → ℂ)
    (hG : ∀ m, k ≤ m → G m = ∑ i ∈ Icc 1 k, A i * G (m - i) + w (m - k)) :
    let T := PowerSeries.mk fun j ↦ G (j + k)
    T - lagSeries k A * T =
      PowerSeries.mk (fun j ↦ ∑ i ∈ range (k - j), A (j + 1 + i) * G (k - 1 - i)) +
        PowerSeries.mk w := by
  dsimp only
  apply PowerSeries.ext
  intro j
  rw [map_sub, map_add, coeff_lagSeries_mul]
  simp only [coeff_mk]
  rw [hG (j + k) (by omega), Nat.add_sub_cancel]
  rw [← sum_filter_add_sum_filter_not (Icc 1 k) (· ≤ j)]
  have htail : (∑ i ∈ Icc 1 k with i ≤ j, A i * G (j + k - i)) =
      ∑ i ∈ Icc 1 k with i ≤ j, A i * G (j - i + k) := by
    apply sum_congr rfl
    intro i hi
    have := (mem_filter.mp hi).2
    rw [show j + k - i = j - i + k by omega]
  rw [htail, add_assoc, add_sub_cancel_left, add_left_inj]
  have hinit : {i ∈ Icc 1 k | ¬ i ≤ j} = Ico (j + 1) (k + 1) := by
    ext i
    simp only [mem_filter, mem_Icc, mem_Ico]
    omega
  rw [hinit, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_add_right]
  apply sum_congr rfl
  intro i hi
  rw [show j + k - (j + 1 + i) = k - 1 - i by omega]

end linearRecurrence_inhomogeneous_explicit

open linearRecurrence_inhomogeneous_explicit

/-- **Explicit formula for an inhomogeneous linear recurrence.** Let $k \in \mathbb{N}$ and let
$A, f, G, w \colon \mathbb{N} \to \mathbb{C}$ be sequences such that, for every $m \ge k$,
$f_m = \sum_{i=1}^{k} A_i f_{m-i}$ and $G_m = \sum_{i=1}^{k} A_i G_{m-i} + w_{m-k}$. Suppose
moreover that $f_j = 0$ for every $j < k - 1$ and $f_{k-1} = 1$. Then for every $n \ge k - 1$,

$$G_{n+1} = \sum_{j=0}^{k-1} \sum_{i=0}^{k-1-j} f_{n-j} A_{j+1+i} G_{k-1-i} +
\sum_{j=0}^{n} f_{n-j} w_j.$$

For $k = 0$ the index $k - 1$ is read as $0$, so the hypotheses cannot all hold. The source
states the formula for $n \ge k$, as a consequence of its Theorem 1.

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Corollary 1
(`integers-2024-A84-cor-1`). -/
public theorem linearRecurrence_inhomogeneous_explicit (k : ℕ) (A f G w : ℕ → ℂ)
    (hf : ∀ n, k ≤ n → f n = ∑ i ∈ Finset.Icc 1 k, A i * f (n - i))
    (hG : ∀ n, k ≤ n → G n = ∑ i ∈ Finset.Icc 1 k, A i * G (n - i) + w (n - k))
    (hf₀ : ∀ j, j + 1 < k → f j = 0) (hf₁ : f (k - 1) = 1) {n : ℕ} (hn : k ≤ n + 1) :
    G (n + 1) =
      ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range (k - j),
        f (n - j) * A (j + 1 + i) * G (k - 1 - i) +
        ∑ j ∈ Finset.range (n + 1), f (n - j) * w j := by
  obtain rfl | hk := Nat.eq_zero_or_pos k
  · have hz : f 0 = 0 := by simpa using hf 0 (by omega)
    exact (zero_ne_one (hz.symm.trans hf₁)).elim
  let T := PowerSeries.mk fun j ↦ G (j + k)
  let B := fun j ↦ ∑ i ∈ range (k - j), A (j + 1 + i) * G (k - 1 - i)
  have h : T * X ^ (k - 1) = (PowerSeries.mk B + PowerSeries.mk w) * PowerSeries.mk f := by
    rw [← fundamental_series hk A f hf hf₀ hf₁, ← tail_series k A G w hG]
    change T * (_ - _ * _) = (T - _ * T) * _
    ring
  have hc := congrArg (coeff n) h
  rw [coeff_mul_X_pow', ite_eq_left (by omega), add_mul, map_add,
    coeff_product, coeff_product] at hc
  simp only [T, coeff_mk, show n - (k - 1) + k = n + 1 by omega] at hc
  rw [hc]
  congr 1
  · rw [← sum_subset (range_mono hn) (f := fun j ↦ B j * f (n - j)) (by
        intro j _ hj
        have hjk : k ≤ j := by simpa using hj
        simp [B, Nat.sub_eq_zero_of_le hjk])]
    apply sum_congr rfl
    intro j _
    rw [mul_comm]
    simp only [B, mul_sum, mul_assoc]
  · apply sum_congr rfl
    intro j _
    exact mul_comm _ _

end MetaMathlibExt
