/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-! # Markov chains: contraction of total variation

Applying a Markov kernel contracts total variation (data
processing), so the total variation between two chains started at
different states is nonincreasing in time. This is the contraction
core of roadmap package ML-24 of the Atlas TCS canon roadmap;
mixing-time quantities built on `tvDist` are follow-ups. The
definition of `tvDist` here agrees with
`MathlibExt/Probability/TotalVariationCoupling.lean`.

Source: Levin and Peres, Markov Chains and Mixing Times (2017),
Chapter 4.
-/

open Finset

/-- Total variation distance between two probability mass functions
on a finite type: half the `L1` distance. -/
noncomputable def tvDist {α : Type*} [Fintype α] (p q : PMF α) : ℝ :=
  (1 / 2) * ∑ a, |(p a).toReal - (q a).toReal|

/-- The distribution of a Markov chain after `t` steps started from
`x`, where `K` is the one-step kernel (as a PMF-valued function). -/
noncomputable def chainDist {α : Type*} (K : α → PMF α) (x : α) : ℕ → PMF α
  | 0 => PMF.pure x
  | t + 1 => (chainDist K x t).bind K

/-- `toReal` of a one-step bind is the finite mixture of `toReal` masses. -/
private theorem bind_toReal {α : Type*} [Fintype α] (K : α → PMF α) (p : PMF α)
    (a : α) :
    ((p.bind K) a).toReal = ∑ x, (p x).toReal * (K x a).toReal := by
  rw [PMF.bind_apply,
    ENNReal.tsum_toReal_eq
      (fun x => ENNReal.mul_ne_top (p.apply_ne_top x) ((K x).apply_ne_top a))]
  simp only [ENNReal.toReal_mul, tsum_fintype]

/-- Each kernel row sums to one in `toReal`. -/
private theorem kernel_toReal_sum {α : Type*} [Fintype α] (K : α → PMF α)
    (x : α) :
    ∑ a, (K x a).toReal = 1 := by
  have h := congrArg ENNReal.toReal (K x).tsum_coe
  rw [ENNReal.tsum_toReal_eq (fun a => (K x).apply_ne_top a), tsum_fintype,
    ENNReal.toReal_one] at h
  exact h

/-- Data processing for one Markov step: total variation between
the one-step distributions is at most the total variation between
the starting distributions. -/
theorem tvDist_bind_le {α : Type*} [Fintype α] (K : α → PMF α) (p q : PMF α) :
    tvDist (p.bind K) (q.bind K) ≤ tvDist p q := by
  unfold tvDist
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc ∑ a, |((p.bind K) a).toReal - ((q.bind K) a).toReal|
      ≤ ∑ a, ∑ x, |(p x).toReal - (q x).toReal| * (K x a).toReal := by
        apply Finset.sum_le_sum
        intro a _
        rw [bind_toReal K p a, bind_toReal K q a]
        have hsub : (∑ x, (p x).toReal * (K x a).toReal)
            - (∑ x, (q x).toReal * (K x a).toReal)
            = ∑ x, ((p x).toReal - (q x).toReal) * (K x a).toReal := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x _
          rw [sub_mul]
        rw [hsub]
        calc |∑ x, ((p x).toReal - (q x).toReal) * (K x a).toReal|
            ≤ ∑ x, |((p x).toReal - (q x).toReal) * (K x a).toReal| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ x, |(p x).toReal - (q x).toReal| * (K x a).toReal := by
              apply Finset.sum_congr rfl
              intro x _
              rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ = ∑ x, |(p x).toReal - (q x).toReal| := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.mul_sum, kernel_toReal_sum K x, mul_one]

/-- Total variation between two chains started at `x` and `y` is
nonincreasing in time. -/
theorem tvDist_chainDist_mono {α : Type*} [Fintype α] (K : α → PMF α)
    (x y : α) (t : ℕ) :
    tvDist (chainDist K x (t + 1)) (chainDist K y (t + 1)) ≤
      tvDist (chainDist K x t) (chainDist K y t) := by
  have h : ∀ z : α, chainDist K z (t + 1) = (chainDist K z t).bind K :=
    fun z => rfl
  rw [h x, h y]
  exact tvDist_bind_le K _ _
