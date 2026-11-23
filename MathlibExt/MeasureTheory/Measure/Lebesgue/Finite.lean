/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Sets of finite Lebesgue measure

This file records an elementary unbounded-complement property of subsets of the real line
with finite Lebesgue measure.
-/

@[expose] public section

namespace MeasureTheory

open Set
open scoped ENNReal

/-- **Sets of finite Lebesgue measure contain no right half-line.** Let $E \subseteq \mathbb{R}$
have finite Lebesgue outer measure ($E$ need not be measurable). Then for every real $X$ there
is a real $x > X$ with $x \notin E$; that is, $E$ contains no half-line $(X, \infty)$. -/
theorem exists_gt_not_mem_of_volume_lt_top
    (E : Set ℝ) (hE : volume E < ∞) (X : ℝ) :
    ∃ x : ℝ, X < x ∧ x ∉ E := by
  by_contra! h
  have hmono : volume (Ioi X) ≤ volume E := measure_mono fun x hx ↦ h x hx
  have htop : (∞ : ℝ≥0∞) ≤ volume E := by
    simpa only [Real.volume_Ioi] using hmono
  exact (not_lt_of_ge htop) hE

end MeasureTheory
