/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Int.Interval
import MathlibExt.NumberTheory.FloorQuotientDivisorSummatory

open MetaMathlibExt

example : (floorQuotientOddCount 0 : ℤ) = 0 := by
  rw [floorQuotientOddCount_eq_divisor_summatory_sub]
  decide

example : (floorQuotientOddCount 1 : ℤ) = 1 := by
  rw [floorQuotientOddCount_eq_divisor_summatory_sub]
  decide

example : (floorQuotientOddCount 6 : ℤ) = 4 := by
  rw [floorQuotientOddCount_eq_divisor_summatory_sub]
  decide

example : (floorQuotientOddCount 7 : ℤ) = 6 := by
  rw [floorQuotientOddCount_eq_divisor_summatory_sub]
  decide

-- Check the regions independently by enumerating a coordinate box, rather than by divisors.
private theorem card_bounded_pairs (n : ℤ) (P : ℤ × ℤ → Prop) [DecidablePred P]
    (h : ∀ p, P p → 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 * p.2 ≤ n) :
    Nat.card {p // P p} = ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter P).card := by
  apply Nat.subtype_card
  intro p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨And.right, fun hp => ?_⟩
  obtain ⟨hx, hy, hxy⟩ := h p hp
  have hx' : p.1 ≤ p.1 * p.2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hy (show 0 ≤ p.1 by omega)
  have hy' : p.2 ≤ p.1 * p.2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (show 0 ≤ p.2 by omega)
  exact ⟨⟨⟨hx, hx'.trans hxy⟩, ⟨hy, hy'.trans hxy⟩⟩, hp⟩

private theorem upper_count (n : ℤ) :
    Nat.card {p : ℤ × ℤ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ n < 2 * (p.1 * p.2) ∧ p.1 * p.2 ≤ n} =
      ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
        (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ n < 2 * (p.1 * p.2) ∧ p.1 * p.2 ≤ n)).card :=
  card_bounded_pairs n _ fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩

private theorem lower_count (n : ℤ) (hn : 0 ≤ n) :
    Nat.card {p : ℤ × ℤ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 2 * (p.1 * p.2) ≤ n} =
      ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
        (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 2 * (p.1 * p.2) ≤ n)).card :=
  card_bounded_pairs n _ fun _ ⟨hx, hy, hxy⟩ => ⟨hx, hy, by omega⟩

-- The shared boundary point (1, 1) is counted only in the lower region.
example :
    Nat.card {p : ℤ × ℤ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 2 < 2 * (p.1 * p.2) ∧ p.1 * p.2 ≤ 2} = 2 ∧
      Nat.card {p : ℤ × ℤ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 2 * (p.1 * p.2) ≤ 2} = 1 := by
  rw [upper_count, lower_count 2 (by decide)]
  decide

-- Dent and Shor, Example 5: 32 upper points minus 20 lower points.
example : (floorQuotientOddCount 17 : ℤ) = 12 := by
  rw [floorQuotientOddCount_eq_hyperbolic_lattice_difference, upper_count,
    lower_count ((17 : ℕ) : ℤ) (by decide)]
  decide
