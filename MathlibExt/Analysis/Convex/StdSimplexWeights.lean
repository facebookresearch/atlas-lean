/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.StdSimplex
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.InformationTheory.LogSum

/-!
# Real distributions on a finite type from weight functions

This file extends `MathlibExt/Analysis/Convex/StdSimplex.lean` with constructors of real points of
`Convexity.StdSimplex ℝ α` on a finite type `α` from weight functions. It is a separate module so
that its imports are not added to the canonical module, which most of the simplicial and
topological library imports.

* `StdSimplex.ofWeights`: the point with given nonnegative coordinates summing to `1`.
* `StdSimplex.normalizeWeights`, `StdSimplex.normalize`: normalization of nonnegative weights on a
  nonempty type, uniform when all weights are zero.
* `StdSimplex.prod_rpow_le_prod_rpow_normalizeWeights`: Gibbs' inequality in product form,
  `∏ θ i ^ a i ≤ ∏ (a i / ∑ a) ^ a i` over probability vectors `θ`, derived from the log-sum
  inequality `Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div`.
-/

@[expose] public section

namespace Convexity.StdSimplex

open Finset

variable {α : Type*} [Fintype α]

/-- The point of the standard simplex on a finite type with coordinates `p`. -/
noncomputable def ofWeights (p : α → ℝ) (h0 : ∀ a, 0 ≤ p a) (h1 : ∑ a, p a = 1) :
    StdSimplex ℝ α where
  weights := Finsupp.equivFunOnFinite.symm p
  nonneg := fun a => by simpa using h0 a
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    simpa using h1

@[simp]
theorem ofWeights_weights (p : α → ℝ) (h0 : ∀ a, 0 ≤ p a) (h1 : ∑ a, p a = 1) (a : α) :
    (ofWeights p h0 h1).weights a = p a := by
  simp [ofWeights]

/-- Normalize weights: `a i / ∑ j, a j`, or the uniform vector `(card α)⁻¹` when the total is zero.
For nonnegative weights on a nonempty type this is a probability vector
(`normalizeWeights_nonneg`, `sum_normalizeWeights`), and a zero total means all weights are
zero. -/
noncomputable def normalizeWeights (a : α → ℝ) (i : α) : ℝ :=
  if ∑ j, a j = 0 then (Fintype.card α : ℝ)⁻¹ else a i / ∑ j, a j

theorem normalizeWeights_of_pos {a : α → ℝ} (hA : 0 < ∑ i, a i) (i : α) :
    normalizeWeights a i = a i / ∑ j, a j := by
  simp [normalizeWeights, hA.ne']

theorem normalizeWeights_nonneg {a : α → ℝ} (ha : ∀ i, 0 ≤ a i) (i : α) :
    0 ≤ normalizeWeights a i := by
  unfold normalizeWeights
  split_ifs
  · positivity
  · exact div_nonneg (ha i) (sum_nonneg fun j _ => ha j)

theorem sum_normalizeWeights [Nonempty α] {a : α → ℝ} (ha : ∀ i, 0 ≤ a i) :
    ∑ i, normalizeWeights a i = 1 := by
  by_cases h : ∑ i, a i = 0
  · have hn : ∀ i, normalizeWeights a i = (Fintype.card α : ℝ)⁻¹ := fun i => by
      simp [normalizeWeights, h]
    simp only [hn, sum_const, card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · have hA : 0 < ∑ i, a i := lt_of_le_of_ne (sum_nonneg fun i _ => ha i) (Ne.symm h)
    simp only [normalizeWeights_of_pos hA, ← Finset.sum_div]
    exact div_self hA.ne'

/-- Nonnegative weights on a nonempty finite type, normalized to a point of the simplex (uniform
when all weights are zero). -/
noncomputable def normalize [Nonempty α] (a : α → ℝ) (ha : ∀ i, 0 ≤ a i) : StdSimplex ℝ α :=
  ofWeights (normalizeWeights a) (normalizeWeights_nonneg ha) (sum_normalizeWeights ha)

@[simp]
theorem normalize_weights [Nonempty α] (a : α → ℝ) (ha : ∀ i, 0 ≤ a i) (i : α) :
    (normalize a ha).weights i = normalizeWeights a i :=
  ofWeights_weights _ _ _ i

/-- **Gibbs' inequality in product form**: for weights `a ≥ 0`, every probability vector `θ`
satisfies `∏ θ i ^ a i ≤ ∏ (normalizeWeights a i) ^ a i`. On a nonempty type `normalizeWeights a`
is itself a probability vector, hence a maximizer. Derived from the log-sum inequality
`Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div` (`MathlibExt/InformationTheory/LogSum.lean`) on
the support of `a`; this is the categorical maximum likelihood inequality. -/
theorem prod_rpow_le_prod_rpow_normalizeWeights {a θ : α → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθ1 : ∑ i, θ i = 1) :
    ∏ i, θ i ^ a i ≤ ∏ i, normalizeWeights a i ^ a i := by
  classical
  rcases (sum_nonneg fun i (_ : i ∈ univ) => ha i).eq_or_lt with hA | hA
  · have h0 : ∀ i, a i = 0 := fun i => (sum_eq_zero_iff_of_nonneg fun i _ => ha i).1 hA.symm i
      (mem_univ i)
    simp [h0]
  set A := ∑ i, a i with hAdef
  set S := univ.filter fun i => 0 < a i with hS
  have hmem : ∀ {i}, i ∈ S ↔ 0 < a i := by simp [hS]
  have hout : ∀ i, i ∉ S → a i = 0 := fun i hi =>
    le_antisymm (not_lt.1 fun h => hi (hmem.2 h)) (ha i)
  have hres : ∀ f : α → ℝ, ∏ i, f i ^ a i = ∏ i ∈ S, f i ^ a i := fun f =>
    (prod_subset (subset_univ S) fun i _ hi => by rw [hout i hi, Real.rpow_zero]).symm
  rw [hres θ, hres (normalizeWeights a)]
  have hnormEq : ∀ i, normalizeWeights a i = a i / A := fun i =>
    normalizeWeights_of_pos hA i
  have hnorm : ∀ i ∈ S, 0 < normalizeWeights a i := fun i hi => by
    rw [hnormEq]; exact div_pos (hmem.1 hi) hA
  by_cases hz : ∃ i ∈ S, θ i = 0
  · obtain ⟨i, hi, h0⟩ := hz
    rw [prod_eq_zero hi (by rw [h0, Real.zero_rpow (hmem.1 hi).ne'])]
    exact prod_nonneg fun i hi => Real.rpow_nonneg (hnorm i hi).le _
  push Not at hz
  have hθpos : ∀ i ∈ S, 0 < θ i := fun i hi => lt_of_le_of_ne (hθ0 i) (hz i hi).symm
  have hL : 0 < ∏ i ∈ S, θ i ^ a i :=
    prod_pos fun i hi => Real.rpow_pos_of_pos (hθpos i hi) _
  have hR : 0 < ∏ i ∈ S, normalizeWeights a i ^ a i :=
    prod_pos fun i hi => Real.rpow_pos_of_pos (hnorm i hi) _
  rw [← Real.log_le_log_iff hL hR,
    Real.log_prod fun i hi => (Real.rpow_pos_of_pos (hθpos i hi) _).ne',
    Real.log_prod fun i hi => (Real.rpow_pos_of_pos (hnorm i hi) _).ne',
    sum_congr rfl fun i hi => Real.log_rpow (hθpos i hi) _,
    sum_congr rfl fun i hi => Real.log_rpow (hnorm i hi) _]
  have hsumS : ∑ i ∈ S, a i = A := sum_subset (subset_univ S) fun i _ hi => hout i hi
  have hSne : S.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.1 h, sum_empty] at hsumS
    exact hA.ne' hsumS.symm
  have hΘpos : 0 < ∑ i ∈ S, θ i := sum_pos hθpos hSne
  have hΘ1 : ∑ i ∈ S, θ i ≤ 1 :=
    hθ1 ▸ sum_le_sum_of_subset_of_nonneg (subset_univ S) fun i _ _ => hθ0 i
  have hls := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div S a θ (fun i _ => ha i) hθpos
  rw [hsumS, Real.log_div hA.ne' hΘpos.ne'] at hls
  have hlogΘ : Real.log (∑ i ∈ S, θ i) ≤ 0 := Real.log_nonpos hΘpos.le hΘ1
  have hlhs : ∑ i ∈ S, a i * Real.log (a i / θ i) =
      ∑ i ∈ S, a i * Real.log (a i) - ∑ i ∈ S, a i * Real.log (θ i) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i hi => ?_
    rw [Real.log_div (hmem.1 hi).ne' (hθpos i hi).ne', mul_sub]
  have hrhs : ∑ i ∈ S, a i * Real.log (normalizeWeights a i) =
      ∑ i ∈ S, a i * Real.log (a i) - A * Real.log A := by
    rw [← hsumS, sum_mul, ← sum_sub_distrib, hsumS]
    refine sum_congr rfl fun i hi => ?_
    rw [hnormEq, Real.log_div (hmem.1 hi).ne' hA.ne', mul_sub]
  rw [hlhs] at hls
  rw [hrhs]
  nlinarith [mul_nonneg hA.le (neg_nonneg.2 hlogΘ)]

end Convexity.StdSimplex
