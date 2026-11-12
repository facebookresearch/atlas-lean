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
public import MathlibExt.InformationTheory.FiniteEntropy

import Mathlib.Tactic.NormNum

@[expose] public section

/-! # The AEP estimate (Chebyshev form)

For a probability mass function on a finite alphabet, the probability
that the self-information of a single sample deviates from the
Shannon entropy by more than `ε` is at most the self-information
variance over `ε^2`. This one-shot Chebyshev estimate is the core
of the asymptotic equipartition property and of typical-set source
coding, and covers the finite core of roadmap package QCI-31 of
the Atlas TCS canon roadmap.

The entropy here is in nats, `shannonEntropyNats`, for a `PMF α`.
It is the established bits entropy `InformationTheory.shannonEntropy`
multiplied by `Real.log 2`; see `shannonEntropyNats_eq_mul_log_two`.
There is no second, incompatible entropy API: the `α → ℝ` weight
vector is not a probability law, and a statement over it could not
reuse the existing entropy results.

Source: Shannon (1948); Cover and Thomas, Elements of Information
Theory (2006), Chapter 3.
-/

open Finset

namespace InformationTheory

/-- Self-information (nats) of an outcome `a` under the law `p`, with the
`0 log 0 = 0` convention: an outcome of probability `0` has self-information
`0`, since `-Real.log 0` is not a meaningful information content. -/
noncomputable def selfInformationNats {α : Type*} (p : PMF α) (a : α) : ℝ :=
  if (p a).toReal = 0 then 0 else -Real.log (p a).toReal

/-- Shannon entropy (nats) of a probability mass function on a finite type,
`∑ a, -(p a) * log (p a)`, with the `0 log 0 = 0` convention read off from
`Real.negMulLog` at the support: terms with `p a = 0` contribute `0`. -/
noncomputable def shannonEntropyNats {α : Type*} [Fintype α] (p : PMF α) : ℝ :=
  ∑ a, Real.negMulLog (p a).toReal

/-- Bridge to the established bits entropy: the nats entropy is the bits
entropy times `Real.log 2`. -/
theorem shannonEntropyNats_eq_mul_log_two {α : Type*} [Fintype α] (p : PMF α) :
    shannonEntropyNats p = shannonEntropy p * Real.log 2 := by
  rw [shannonEntropyNats, shannonEntropy, div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']

/-- The nats entropy is the expected self-information. -/
theorem shannonEntropyNats_eq_sum_mul_selfInformation {α : Type*} [Fintype α]
    (p : PMF α) :
    shannonEntropyNats p = ∑ a, (p a).toReal * selfInformationNats p a := by
  rw [shannonEntropyNats]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : (p a).toReal = 0
  · simp [selfInformationNats, h]
  · have hself : selfInformationNats p a = -Real.log (p a).toReal := by
      simp [selfInformationNats, h]
    rw [hself]
    unfold Real.negMulLog
    ring

/-- The asymptotic equipartition property, Chebyshev form: for the
self-information of a single sample from a finite law `p`, the probability
that its deviation from the entropy exceeds `ε` is at most the
self-information variance divided by `ε²`. This is the one-shot estimate
behind typical-set coding. -/
theorem aep_chebyshev {α : Type*} [Fintype α] (p : PMF α)
    (ε : ℝ) (hε : 0 < ε) :
    (∑ a ∈ Finset.univ.filter
        (fun a => ε < |selfInformationNats p a - shannonEntropyNats p|),
        (p a).toReal) ≤
      (∑ a, (p a).toReal * (selfInformationNats p a - shannonEntropyNats p) ^ 2)
        / ε ^ 2 := by
  have hε2pos : 0 < ε ^ 2 := pow_pos hε 2
  have hpoint : ∀ a ∈ Finset.univ.filter
      (fun a => ε < |selfInformationNats p a - shannonEntropyNats p|),
      (p a).toReal ≤ (p a).toReal * (selfInformationNats p a - shannonEntropyNats p) ^ 2
        / ε ^ 2 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨_, hbad⟩ := ha
    have hε2lt : ε ^ 2 < (selfInformationNats p a - shannonEntropyNats p) ^ 2 := by
      have h1 : ε ^ 2 < (|selfInformationNats p a - shannonEntropyNats p|) ^ 2 :=
        pow_lt_pow_left₀ hbad hε.le (by norm_num)
      rwa [sq_abs] at h1
    have hmul : (p a).toReal * ε ^ 2 ≤ (p a).toReal *
        ((selfInformationNats p a - shannonEntropyNats p) ^ 2) :=
      mul_le_mul_of_nonneg_left hε2lt.le (ENNReal.toReal_nonneg)
    exact (le_div_iff₀ hε2pos).mpr hmul
  calc (∑ a ∈ Finset.univ.filter
        (fun a => ε < |selfInformationNats p a - shannonEntropyNats p|),
        (p a).toReal)
      ≤ ∑ a ∈ Finset.univ.filter
        (fun a => ε < |selfInformationNats p a - shannonEntropyNats p|),
          (p a).toReal * (selfInformationNats p a - shannonEntropyNats p) ^ 2 / ε ^ 2 :=
        Finset.sum_le_sum hpoint
    _ ≤ ∑ a ∈ Finset.univ,
          (p a).toReal * (selfInformationNats p a - shannonEntropyNats p) ^ 2 / ε ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro a _ _
        exact div_nonneg (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) hε2pos.le
    _ = (∑ a, (p a).toReal * (selfInformationNats p a - shannonEntropyNats p) ^ 2)
        / ε ^ 2 := by
        rw [Finset.sum_div]

end InformationTheory
