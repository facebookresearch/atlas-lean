/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Uniqueness
/-!
# One-sided derivatives of a convex pressure and uniqueness off a countable set

A convex function has equal left and right derivatives except at countably many points; when
edge densities of two measures are the one-sided derivatives of a convex pressure, the measures
agree on increasing events off a countable set of parameters.

## i. Overview

For a convex `g : ℝ → ℝ`, the right derivative `pressureRightDeriv g` and the left derivative
`pressureLeftDeriv g` are monotone, satisfy `g'₋(x) ≤ g'₊(x)` and `g'₊(z) ≤ g'₋(x)` for `z < x`,
and agree wherever `g'₊` is continuous, hence off a countable set
(`countable_leftDeriv_ne_rightDeriv`). In the random-cluster model the free and wired edge
densities are the left and right derivatives of the pressure in the edge parameter. Combined
with a monotone coupling of the two measures and equality of all edge marginals at continuity
points, this gives agreement on increasing events off a countable set
(`fk_uniqueness_of_pressure_convex`, `countable_phi_ne_of_pressure_convex`). The convex-analysis
inputs are Mathlib's `ConvexOn.monotoneOn_rightDeriv`,
`ConvexOn.leftDeriv_le_rightDeriv_of_mem_interior` and
`ConvexOn.rightDeriv_le_slope_of_mem_interior`.

## ii. Key results

- `StatMech.FK.pressureRightDeriv`, `StatMech.FK.pressureLeftDeriv` : one-sided derivatives.
- `StatMech.FK.countable_leftDeriv_ne_rightDeriv` : a convex function on `ℝ` is differentiable
  off a countable set, in the form `g'₋ = g'₊`.
- `StatMech.FK.fk_uniqueness_of_pressure_convex`,
  `StatMech.FK.countable_phi_ne_of_pressure_convex` : agreement on increasing events off a
  countable set.

## iii. Table of contents

- A. One-sided derivatives of convex functions
- B. Edge densities as derivatives of a convex pressure

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 4.

-/

@[expose] public section

open Set Filter Topology

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

section ConvexFunction

variable {g : ℝ → ℝ}

/-!

## A. One-sided derivatives of convex functions

-/

/-- The right derivative `g'₊(x) = derivWithin g (Ioi x) x`, the form used by Mathlib's
`ConvexOn.monotoneOn_rightDeriv`. -/
noncomputable def pressureRightDeriv (g : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin g (Ioi x) x

/-- The left derivative `g'₋(x) = derivWithin g (Iio x) x`. -/
noncomputable def pressureLeftDeriv (g : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin g (Iio x) x

lemma pressureRightDeriv_monotone (hg : ConvexOn ℝ univ g) :
    Monotone (pressureRightDeriv g) := by
  have hm := hg.monotoneOn_rightDeriv
  rw [interior_univ] at hm
  intro x y hxy
  exact hm (mem_univ x) (mem_univ y) hxy

lemma pressureLeftDeriv_monotone (hg : ConvexOn ℝ univ g) :
    Monotone (pressureLeftDeriv g) := by
  have hm := hg.monotoneOn_leftDeriv
  rw [interior_univ] at hm
  intro x y hxy
  exact hm (mem_univ x) (mem_univ y) hxy

/-- `g'₋(x) ≤ g'₊(x)`; Mathlib's `ConvexOn.leftDeriv_le_rightDeriv_of_mem_interior` on `univ`. -/
lemma pressureLeftDeriv_le_rightDeriv (hg : ConvexOn ℝ univ g) (x : ℝ) :
    pressureLeftDeriv g x ≤ pressureRightDeriv g x :=
  hg.leftDeriv_le_rightDeriv_of_mem_interior (x := x) (by rw [interior_univ]; trivial)

lemma pressureRightDeriv_le_leftDeriv_of_lt (hg : ConvexOn ℝ univ g) {z x : ℝ}
    (hzx : z < x) : pressureRightDeriv g z ≤ pressureLeftDeriv g x := by
  have h1 : pressureRightDeriv g z ≤ slope g z x :=
    hg.rightDeriv_le_slope_of_mem_interior (by rw [interior_univ]; trivial) (mem_univ x) hzx
  have h2 : slope g z x ≤ pressureLeftDeriv g x :=
    hg.slope_le_leftDeriv_of_mem_interior (mem_univ z) (by rw [interior_univ]; trivial) hzx
  exact h1.trans h2

lemma pressureLeftDeriv_eq_rightDeriv_of_continuousAt (hg : ConvexOn ℝ univ g) {x : ℝ}
    (hc : ContinuousAt (pressureRightDeriv g) x) :
    pressureLeftDeriv g x = pressureRightDeriv g x := by
  refine le_antisymm (pressureLeftDeriv_le_rightDeriv hg x) ?_
  have hlim : Tendsto (pressureRightDeriv g) (𝓝[<] x) (𝓝 (pressureRightDeriv g x)) :=
    hc.continuousWithinAt
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with z (hz : z < x)
  exact pressureRightDeriv_le_leftDeriv_of_lt hg hz

/-- A convex function on `ℝ` has equal left and right derivatives off a countable set. -/
lemma countable_leftDeriv_ne_rightDeriv (hg : ConvexOn ℝ univ g) :
    {x : ℝ | pressureLeftDeriv g x ≠ pressureRightDeriv g x}.Countable := by
  refine ((pressureRightDeriv_monotone hg).countable_not_continuousAt).mono ?_
  intro x hx
  simp only [mem_ofPred_eq] at hx ⊢
  exact fun hcont => hx (pressureLeftDeriv_eq_rightDeriv_of_continuousAt hg hcont)

end ConvexFunction

section Bridge

variable {E : Type*} [Fintype E] [DecidableEq E]

/-!

## B. Edge densities as derivatives of a convex pressure

-/

/-- If two families of edge marginals are the left and right derivatives of a convex `g`, they
differ only on a countable set of parameters. -/
lemma pressure_convex_countable_density_ne
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (μ ν : ℝ → ConfigSpace E → ℝ) (e : E)
    (ha_eq : ∀ p, edgeMargProb (μ p) e = pressureLeftDeriv g p)
    (hb_eq : ∀ p, edgeMargProb (ν p) e = pressureRightDeriv g p) :
    {p : ℝ | edgeMargProb (μ p) e ≠ edgeMargProb (ν p) e}.Countable := by
  refine (countable_leftDeriv_ne_rightDeriv hg).mono ?_
  intro p hp
  simp only [mem_ofPred_eq] at hp ⊢
  rw [ha_eq p, hb_eq p] at hp
  exact hp

/-- If `μ p` and `ν p` are monotonically coupled, the edge density of `ν p` at `e` is the right
derivative of a convex `g`, and all edge marginals agree wherever that density is continuous in
`p`, then `μ p` and `ν p` agree on every increasing event for `p` off a countable set. -/
lemma fk_uniqueness_of_pressure_convex
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (μ ν : ℝ → ConfigSpace E → ℝ) (e : E)
    (P : ℝ → ConfigSpace E × ConfigSpace E → ℝ)
    (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
    (hb_eq : ∀ p, edgeMargProb (ν p) e = pressureRightDeriv g p)
    (heq_at_cont : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p →
      ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e') :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ p ∉ S, ∀ {A : Set (ConfigSpace E)}, IsIncreasing A →
        eventMassProb (μ p) A = eventMassProb (ν p) A := by
  have hbmono : Monotone (fun p => edgeMargProb (ν p) e) := by
    have : (fun p => edgeMargProb (ν p) e) = pressureRightDeriv g := by
      funext p; exact hb_eq p
    rw [this]; exact pressureRightDeriv_monotone hg
  exact phi0_eq_phi1_off_countable μ ν e P hcoup hbmono heq_at_cont

/-- The set of parameters at which `μ p` and `ν p` differ on some increasing event is countable,
under the hypotheses of `fk_uniqueness_of_pressure_convex`. -/
lemma countable_phi_ne_of_pressure_convex
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (μ ν : ℝ → ConfigSpace E → ℝ) (e : E)
    (P : ℝ → ConfigSpace E × ConfigSpace E → ℝ)
    (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
    (hb_eq : ∀ p, edgeMargProb (ν p) e = pressureRightDeriv g p)
    (heq_at_cont : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p →
      ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e') :
    {p : ℝ | ∃ A : Set (ConfigSpace E), IsIncreasing A ∧
        eventMassProb (μ p) A ≠ eventMassProb (ν p) A}.Countable := by
  have hbmono : Monotone (fun p => edgeMargProb (ν p) e) := by
    have : (fun p => edgeMargProb (ν p) e) = pressureRightDeriv g := by
      funext p; exact hb_eq p
    rw [this]; exact pressureRightDeriv_monotone hg
  exact countable_phi_ne μ ν e P hcoup hbmono heq_at_cont

end Bridge

end FK

end StatMech
