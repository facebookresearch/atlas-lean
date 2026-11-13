/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section



private theorem pmf_toReal_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  have h : (∑ a, p a).toReal = (1 : ENNReal).toReal := by
    congr 1
    rw [← PMF.tsum_coe p, tsum_eq_sum (fun a ha => False.elim (ha (Finset.mem_univ a)))]
  rw [ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a), ENNReal.toReal_one] at h
  exact h

private theorem bind_toReal {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (K : α → PMF β) (b : β) :
    ((p.bind K) b).toReal = ∑ a, (p a).toReal * ((K a) b).toReal := by
  rw [PMF.bind_apply,
    tsum_eq_sum (fun a ha => False.elim (ha (Finset.mem_univ a))),
    ENNReal.toReal_sum (fun a _ =>
      ENNReal.mul_ne_top (PMF.apply_ne_top p a) (PMF.apply_ne_top (K a) b))]
  exact Finset.sum_congr rfl (fun a _ => ENNReal.toReal_mul)

/-- Total variation distance contracts under stochastic maps
(the classical data-processing inequality): applying the same
channel `K` to two distributions cannot increase their
`L1` distance. -/
theorem tv_contract {α β : Type*} [Fintype α] [Fintype β]
    (p q : PMF α) (K : α → PMF β) :
    (∑ b, |((p.bind K) b).toReal - ((q.bind K) b).toReal|) ≤
      ∑ a, |(p a).toReal - (q a).toReal| := by
  calc (∑ b, |((p.bind K) b).toReal - ((q.bind K) b).toReal|)
      = ∑ b, |∑ a, ((p a).toReal - (q a).toReal) * ((K a) b).toReal| := by
        apply Finset.sum_congr rfl; intro b _
        rw [bind_toReal p K b, bind_toReal q K b]
        congr 1
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun a _ => (sub_mul _ _ _).symm)
    _ ≤ ∑ b, ∑ a, |(p a).toReal - (q a).toReal| * ((K a) b).toReal := by
        apply Finset.sum_le_sum; intro b _
        calc |∑ a, ((p a).toReal - (q a).toReal) * ((K a) b).toReal|
            ≤ ∑ a, |((p a).toReal - (q a).toReal) * ((K a) b).toReal| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ a, |(p a).toReal - (q a).toReal| * ((K a) b).toReal := by
              apply Finset.sum_congr rfl; intro a _
              rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ = ∑ a, |(p a).toReal - (q a).toReal| := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro a _
        rw [← Finset.mul_sum, pmf_toReal_sum (K a), mul_one]

/-- Helstrom discrimination for two equally likely classical
states: the optimal guessing probability (sum over outcomes of
the larger likelihood, halved) equals `(1 + TV / 2) / 2` where
`TV = ∑ a, |p a - q a|`; in the pinned form: the sum of
pointwise maxima is `(2 + ∑ a, |p a - q a|) / 2` (using
`∑ p = ∑ q = 1`). -/
theorem helstrom_max_sum {α : Type*} [Fintype α]
    (p q : PMF α) :
    (∑ a, max (p a).toReal (q a).toReal) =
      (2 + ∑ a, |(p a).toReal - (q a).toReal|) / 2 := by
  have hpt : ∀ a, max (p a).toReal (q a).toReal
      = ((p a).toReal + (q a).toReal + |(p a).toReal - (q a).toReal|) / 2 := by
    intro a
    rcases le_total (p a).toReal (q a).toReal with h | h
    · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  calc (∑ a, max (p a).toReal (q a).toReal)
      = ∑ a, (((p a).toReal + (q a).toReal) / 2
          + |(p a).toReal - (q a).toReal| / 2) :=
        Finset.sum_congr rfl (fun a _ => by rw [hpt a]; ring)
    _ = (∑ a, ((p a).toReal + (q a).toReal)) / 2
          + (∑ a, |(p a).toReal - (q a).toReal|) / 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
    _ = (2 + ∑ a, |(p a).toReal - (q a).toReal|) / 2 := by
        rw [Finset.sum_add_distrib, pmf_toReal_sum p, pmf_toReal_sum q]
        ring
