/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.PcNontrivial

import MathlibExt.Probability.Percolation.DifferentialInequality
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Right-continuity of the percolation probability

The probability of an infinite open cluster at the origin is the infimum of the probabilities
of exiting the finite boxes. These are continuous and nondecreasing in the density, so their
infimum is upper semicontinuous and nondecreasing. This gives right-continuity, in particular
at the critical probability.
-/

namespace MathlibExt.Probability.Percolation.ThetaContinuityWanted

open StatMech.Percolation
open scoped NNReal

/-- **Percolation probability on the parameter interval.** The percolation probability `θ_d` as
a function on `{p : ℝ≥0 // p ≤ 1} = [0, 1]`. -/
public noncomputable abbrev thetaOnUnit (d : ℕ) : {p : ℝ≥0 // p ≤ 1} → ℝ :=
  fun p => theta d p.1 p.2

private theorem crossProb_eq_crossPoly (d n : ℕ) (p : {p : ℝ≥0 // p ≤ 1}) :
    crossProb d p.1 p.2 (n + 1) = crossPoly d n (p.1 : ℝ) :=
  (crossProb_eq_boxCrossProb p.1 p.2 _ (Nat.succ_pos _)).trans (boxCrossProb_eq_prob p.1 p.2 _)

private theorem continuous_crossPoly (d n : ℕ) : Continuous (crossPoly d n) :=
  (differentiable_boxCrossProb (d := d) (n + 1)).continuous

private theorem monotoneOn_crossPoly (d n : ℕ) : MonotoneOn (crossPoly d n) (Set.Icc 0 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) (continuous_crossPoly d n).continuousOn
    (differentiable_boxCrossProb (d := d) (n + 1)).differentiableOn ?_
  intro p hp
  have hp' : p ∈ Set.Icc (0 : ℝ) 1 := interior_subset hp
  exact deriv_boxCrossProb_nonneg (d := d) (n + 1) p hp'.1 hp'.2

/-- **Right-continuity of θ at p_c.** For Bernoulli bond percolation on `ℤ^d`, the map
`p ↦ θ_d(p)` is right-continuous at `p_c(d)`. Source: H. Duminil-Copin, *Introduction to
Bernoulli percolation*, lecture notes (2018), Proposition 3.2. -/
public theorem theta_continuousWithinAt_pc (d : ℕ) :
    ContinuousWithinAt (thetaOnUnit d) {p | pc d ≤ p.1} ⟨pc d, pc_le_one⟩ := by
  let f (n : ℕ) (p : {p : ℝ≥0 // p ≤ 1}) := crossProb d p.1 p.2 (n + 1)
  have hf_cont (n : ℕ) : Continuous (f n) := by
    simpa only [f, crossProb_eq_crossPoly, Function.comp_def] using
      (continuous_crossPoly d n).comp (NNReal.continuous_coe.comp continuous_subtype_val)
  have hf_mono (n : ℕ) : Monotone (f n) := by
    intro p q hpq
    simp only [f, crossProb_eq_crossPoly]
    exact monotoneOn_crossPoly d n ⟨p.1.coe_nonneg, by exact_mod_cast p.2⟩
      ⟨q.1.coe_nonneg, by exact_mod_cast q.2⟩ (by exact_mod_cast hpq)
  have hf_bdd (p : {p : ℝ≥0 // p ≤ 1}) : BddBelow (Set.range fun n => f n p) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact crossProb_nonneg d p.1 p.2 (n + 1)⟩
  -- Continuity from above gives the infimum, since the finite exit events decrease to percolation.
  have hinf : thetaOnUnit d = fun p => ⨅ n, f n p := by
    funext p
    have hanti : Antitone (fun n => f n p) :=
      fun _ _ h => crossProb_antitone d p.1 p.2 (Nat.succ_le_succ h)
    exact ((isGLB_of_tendsto_atTop hanti (tendsto_crossProb_theta p.1 p.2)).csInf_eq
      (Set.range_nonempty _)).symm
  have hmono : Monotone (thetaOnUnit d) := by
    rw [hinf]
    exact fun p _ hpq => ciInf_mono (hf_bdd p) (fun n => hf_mono n hpq)
  have hupper : UpperSemicontinuous (thetaOnUnit d) := by
    rw [hinf]
    exact upperSemicontinuous_ciInf hf_bdd (fun n => (hf_cont n).upperSemicontinuous)
  refine continuousWithinAt_iff_lower_upperSemicontinuousWithinAt.mpr
    ⟨?_, hupper.upperSemicontinuousWithinAt _ _⟩
  -- On the right, monotonicity already bounds θ below by its value at the base point.
  intro y hy
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact hy.trans_le (hmono hp)

end MathlibExt.Probability.Percolation.ThetaContinuityWanted
