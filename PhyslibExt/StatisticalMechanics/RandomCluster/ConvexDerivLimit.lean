/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.IVPressureConvex

/-!
# Pointwise limits of convex functions and their one-sided derivatives

A pointwise limit `g` of convex functions on `ℝ` is convex, has one-sided derivatives everywhere
that are limits of slopes, and its left and right derivatives agree off a countable set; slopes of
the approximants converge to slopes of `g`.

## i. Overview

This packages the one-variable convex-analysis facts used for the random-cluster free energy in
the tilt variable `t` (with `p = logistic(t)`): the free energy is a pointwise limit of convex
finite-volume free energies, and its one-sided derivatives are the candidate edge densities. The
one-sided derivative facts come from Mathlib's
`ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior`
and the lemmas on `pressureRightDeriv` and `pressureLeftDeriv` in `PressureDiff`.

## ii. Key results

- `cdl_slope_tendsto` : slopes of pointwise convergent functions converge.
- `cdl_rightDeriv_tendsto_slope`, `cdl_leftDeriv_tendsto_slope` : one-sided derivatives of a convex
  function are one-sided limits of slopes.
- `cdl_convexDerivLimit` : all of the above for a pointwise limit of convex functions.

## iii. Table of contents

- A. Slopes of pointwise limits
- B. One-sided derivatives of convex functions

## iv. References

- R. T. Rockafellar, *Convex Analysis*, Princeton (1970), Theorem 24.1.
-/

@[expose] public section

open Set Filter Topology

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

/-! ## A. Slopes of pointwise limits -/

lemma cdl_slope_tendsto {κ : Type*} {l : Filter κ}
    (gn : κ → ℝ → ℝ) (glim : ℝ → ℝ)
    (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (glim x))) (a b : ℝ) :
    Tendsto (fun i => slope (gn i) a b) l (𝓝 (slope glim a b)) := by
  simp only [slope_def_field]
  exact ((hlim b).sub (hlim a)).div_const _

variable {g : ℝ → ℝ}

/-! ## B. One-sided derivatives of convex functions -/

lemma cdl_rightDeriv_tendsto_slope (hg : ConvexOn ℝ univ g) (t : ℝ) :
    Tendsto (slope g t) (𝓝[>] t) (𝓝 (pressureRightDeriv g t)) := by
  have h : HasDerivWithinAt g (pressureRightDeriv g t) (Ioi t) t :=
    hg.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at h
  exact h

lemma cdl_leftDeriv_tendsto_slope (hg : ConvexOn ℝ univ g) (t : ℝ) :
    Tendsto (slope g t) (𝓝[<] t) (𝓝 (pressureLeftDeriv g t)) := by
  have h : HasDerivWithinAt g (pressureLeftDeriv g t) (Iio t) t :=
    hg.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp)
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at h
  exact h

/-- A pointwise limit `g` of convex functions on `ℝ` is convex; its one-sided derivatives exist,
are
monotone, are one-sided limits of slopes, and agree off a countable set; slopes of the
approximants converge to slopes of `g`.
-/
lemma cdl_convexDerivLimit {κ : Type*} {l : Filter κ} [l.NeBot]
    (gn : κ → ℝ → ℝ) (g : ℝ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ univ (gn i))
    (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (g x))) :
    ConvexOn ℝ univ g
      ∧ (∀ t, HasDerivWithinAt g (pressureRightDeriv g t) (Ioi t) t)
      ∧ (∀ t, HasDerivWithinAt g (pressureLeftDeriv g t) (Iio t) t)
      ∧ (∀ t, Tendsto (slope g t) (𝓝[>] t) (𝓝 (pressureRightDeriv g t)))
      ∧ (∀ t, Tendsto (slope g t) (𝓝[<] t) (𝓝 (pressureLeftDeriv g t)))
      ∧ (∀ a b, Tendsto (fun i => slope (gn i) a b) l (𝓝 (slope g a b)))
      ∧ (∀ t, pressureLeftDeriv g t ≤ pressureRightDeriv g t)
      ∧ Monotone (pressureRightDeriv g)
      ∧ Monotone (pressureLeftDeriv g)
      ∧ {t : ℝ | pressureLeftDeriv g t ≠ pressureRightDeriv g t}.Countable := by
  have hg : ConvexOn ℝ univ g := ivp2_convexOn_of_tendsto gn g hconv hlim
  exact ⟨hg,
    fun t => hg.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp),
    fun t => hg.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp),
    cdl_rightDeriv_tendsto_slope hg,
    cdl_leftDeriv_tendsto_slope hg,
    cdl_slope_tendsto gn g hlim,
    pressureLeftDeriv_le_rightDeriv hg,
    pressureRightDeriv_monotone hg,
    pressureLeftDeriv_monotone hg,
    countable_leftDeriv_ne_rightDeriv hg⟩

end FK

end StatMech
