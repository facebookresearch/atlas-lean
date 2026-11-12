/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Basic

@[expose] public section

/-! # The AEP estimate (Chebyshev form)

For a probability vector on a finite alphabet, the probability
that the self-information of a single sample deviates from the
Shannon entropy by more than `ε` is at most the self-information
variance over `ε^2`. This one-shot Chebyshev estimate is the core
of the asymptotic equipartition property and of typical-set source
coding, and covers the finite core of roadmap package QCI-31 of
the Atlas TCS canon roadmap.

Source: Shannon (1948); Cover and Thomas, Elements of Information
Theory (2006), Chapter 3.
-/

open Finset

/-- Shannon entropy (nats) of a probability mass function on a
finite type, with the `0 log 0 = 0` convention read off from
`Real.log` at the support: terms with `p a = 0` contribute `0`. -/
noncomputable def shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a, (if p a = 0 then 0 else -(p a) * Real.log (p a))

/-- The asymptotic equipartition property, Chebyshev form: for the
self-information of a single sample from `p` (a probability vector on
a finite type), the probability that its deviation from the entropy
exceeds `ε` is at most the self-information variance divided by
`ε²`. This is the one-shot estimate behind typical-set coding. -/
theorem aep_chebyshev {α : Type*} [Fintype α] (p : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (ε : ℝ) (hε : 0 < ε) :
    (∑ a ∈ Finset.univ.filter
        (fun a => ε < |(if p a = 0 then 0 else -Real.log (p a)) - shannonEntropy p|),
        p a) ≤
      (∑ a, p a * ((if p a = 0 then 0 else -Real.log (p a)) - shannonEntropy p) ^ 2)
        / ε ^ 2 := by
  have hε2pos : 0 < ε ^ 2 := pow_pos hε 2
  have hpoint : ∀ a ∈ Finset.univ.filter
      (fun a => ε < |(if p a = 0 then 0 else -Real.log (p a)) - shannonEntropy p|),
      p a ≤ p a * ((if p a = 0 then 0 else -Real.log (p a)) - shannonEntropy p) ^ 2 / ε ^ 2 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨_, hbad⟩ := ha
    have hε2lt : ε ^ 2 < ((if p a = 0 then 0 else -Real.log (p a)) - shannonEntropy p) ^ 2 := by
      have h1 : ε ^ 2 < (|(if p a = 0 then 0 else -Real.log (p a)) - shannonEntropy p|) ^ 2 :=
        pow_lt_pow_left₀ hbad hε.le (by norm_num)
      rwa [sq_abs] at h1
    have hmul : p a * ε ^ 2 ≤ p a * (((if p a = 0 then 0 else -Real.log (p a)) - shannonEntropy p) ^ 2) :=
      mul_le_mul_of_nonneg_left hε2lt.le (hp_nonneg a)
    exact (le_div_iff₀ hε2pos).mpr hmul
  calc (∑ a ∈ Finset.univ.filter
        (fun a => ε < |(if p a = 0 then 0 else -Real.log (p a)) - shannonEntropy p|),
        p a)
      ≤ ∑ a ∈ Finset.univ.filter
        (fun a => ε < |(if p a = 0 then 0 else -Real.log (p a)) - shannonEntropy p|),
          p a * ((if p a = 0 then 0 else -Real.log (p a)) - shannonEntropy p) ^ 2 / ε ^ 2 :=
        Finset.sum_le_sum hpoint
    _ ≤ ∑ a ∈ Finset.univ,
          p a * ((if p a = 0 then 0 else -Real.log (p a)) - shannonEntropy p) ^ 2 / ε ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro a _ _
        exact div_nonneg (mul_nonneg (hp_nonneg a) (sq_nonneg _)) hε2pos.le
    _ = (∑ a, p a * ((if p a = 0 then 0 else -Real.log (p a)) - shannonEntropy p) ^ 2) / ε ^ 2 := by
        rw [Finset.sum_div]
