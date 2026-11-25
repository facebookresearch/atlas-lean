/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.StrictLiminfGapFiniteSetCountable
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.EReal.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.DenselyOrdered

/-! # Tests for strict liminf gaps and strict local extrema -/

open Filter Topology
open MathlibExt.MeasureTheory.StrictLiminfGapFiniteSetCountableWanted

namespace MathlibExt.MeasureTheory.StrictLiminfGapFiniteSetCountableWanted.Test

/-- The function on `[0, 1]` equal to `0` at the endpoint `0` and to `∞` elsewhere. -/
private noncomputable def spike (y : Set.Icc (0 : ℝ) 1) : ENNReal := by
  classical
  exact if (y : ℝ) = 0 then 0 else ⊤

/-- The hypothesis can hold at a finite value, here at an endpoint of `[0, 1]`, where the
punctured neighborhood is one-sided. -/
private theorem spike_gap (y : Set.Icc (0 : ℝ) 1) (hy : spike y ≠ ⊤) :
    Filter.liminf spike (nhdsWithin y ({y}ᶜ)) > spike y := by
  classical
  have hy0 : (y : ℝ) = 0 := by
    by_contra h
    simp [spike, h] at hy
  have hev : ∀ᶠ x in 𝓝[≠] y, (⊤ : ENNReal) ≤ spike x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (x : ℝ) ≠ 0 := fun h => hx (Subtype.ext (h.trans hy0.symm))
    simp [spike, hx0]
  calc spike y = 0 := by simp [spike, hy0]
    _ < ⊤ := ENNReal.zero_lt_top
    _ ≤ liminf spike (𝓝[≠] y) := le_liminf_of_le (by isBoundedDefault) hev

example : Set.Countable {y : Set.Icc (0 : ℝ) 1 | spike y < (⊤ : ENNReal)} :=
  countable_setOf_lt_top_of_lt_liminf spike spike_gap

/-- Punctured neighborhoods in `[0, 1]` are nontrivial, even at the endpoint `0`. -/
private theorem nhdsNE_zero_neBot : (𝓝[≠] (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1)).NeBot :=
  (nhdsGT_neBot_of_exists_gt ⟨⟨1, by simp⟩, by simp⟩).mono
    (nhdsWithin_mono _ fun _ hx => ne_of_gt hx)

/-- Hence the hypothesis does not hold for free: the zero function, whose values are all finite,
has no strict liminf gap at `0`. -/
example : ¬ Filter.liminf (fun _ : Set.Icc (0 : ℝ) 1 => (0 : ENNReal))
    (nhdsWithin ⟨0, by simp⟩ ({⟨0, by simp⟩}ᶜ)) > 0 := by
  have := nhdsNE_zero_neBot
  simp [liminf_const]

/-- Without the hypothesis the conclusion fails: every value of the zero function is finite, and
`[0, 1]` is uncountable. -/
example : ¬ Set.Countable
    {y : Set.Icc (0 : ℝ) 1 | (fun _ => (0 : ENNReal)) y < (⊤ : ENNReal)} := by
  simp only [ENNReal.zero_lt_top, Set.ofPred_true, Set.countable_univ_iff,
    ← Cardinal.mk_le_aleph0_iff, Cardinal.mk_Icc_real zero_lt_one, not_le]
  exact Cardinal.aleph0_lt_continuum

/-- The strict local extrema of an arbitrary real function form a countable set. -/
example (f : ℝ → ℝ) : {a | IsStrictLocalMin f a ∨ IsStrictLocalMax f a}.Countable :=
  (countable_setOf_isStrictLocalMin f).union (countable_setOf_isStrictLocalMax f)

/-- The codomain only needs a preorder: here the coordinatewise order on the plane. -/
example (f : ℝ × ℝ → ℝ × ℝ) : {a | IsStrictLocalMin f a}.Countable :=
  countable_setOf_isStrictLocalMin f

/-- Strict liminf gaps of an extended-real function on the plane. -/
example (f : ℝ × ℝ → EReal) : {a | f a < liminf f (𝓝[≠] a)}.Countable :=
  countable_setOf_lt_liminf f

end MathlibExt.MeasureTheory.StrictLiminfGapFiniteSetCountableWanted.Test
