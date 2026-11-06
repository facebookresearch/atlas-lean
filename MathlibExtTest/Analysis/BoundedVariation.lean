/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.BoundedVariation
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Tests for the algebraic closure properties of bounded variation
-/

@[expose] public section

open scoped ENNReal

/-- The Heaviside step function has bounded variation on `ℝ`. -/
private lemma bv_step : BoundedVariationOn (fun y : ℝ => if 0 ≤ y then (1 : ℝ) else 0) Set.univ :=
  boundedVariationOn_ite_le 0 1 0 Set.univ

/-- The variation of a single jump is at most its size: here `‖3 - (-2)‖ₑ = 5`. -/
example : eVariationOn (fun y : ℝ => if 0 ≤ y then (3 : ℝ) else -2) Set.univ ≤ 5 := by
  refine (eVariationOn_ite_le_enorm_sub 0 3 (-2) Set.univ).trans_eq ?_
  norm_num [← ofReal_norm]

/-- A staircase with two jumps, as a sum. -/
example : BoundedVariationOn
    ((fun y : ℝ => if 0 ≤ y then (1 : ℝ) else 0) + fun y : ℝ => if 1 ≤ y then (1 : ℝ) else 0)
    Set.univ :=
  bv_step.add (boundedVariationOn_ite_le 1 1 0 Set.univ)

/-- A finite staircase `∑_{i < 5} 1_{[i, ∞)}`. -/
example : BoundedVariationOn (fun y : ℝ => ∑ i ∈ Finset.range 5, if (i : ℝ) ≤ y then (1 : ℝ) else 0)
    Set.univ :=
  BoundedVariationOn.finsetSum fun i _ => boundedVariationOn_ite_le (i : ℝ) 1 0 Set.univ

example : BoundedVariationOn (-fun y : ℝ => if 0 ≤ y then (1 : ℝ) else 0) Set.univ := bv_step.neg

example : BoundedVariationOn
    ((fun y : ℝ => if 0 ≤ y then (1 : ℝ) else 0) - fun _ => (3 : ℝ)) Set.univ :=
  bv_step.sub (boundedVariationOn_const 3 _)

/-- Vector-valued constants. -/
example : BoundedVariationOn (fun _ : ℕ => ((2 : ℝ), (5 : ℝ))) Set.univ :=
  boundedVariationOn_const _ _

/-- `eVariationOn (-f) = eVariationOn f`. -/
example (f : ℝ → ℝ) (s : Set ℝ) : eVariationOn (-f) s = eVariationOn f s := eVariationOn.neg f s

/-- Subadditivity: `V(f + (-f)) = 0 ≤ 2 V(f)`. -/
example (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (f + -f) s ≤ eVariationOn f s + eVariationOn (-f) s :=
  eVariationOn.add_le f (-f) s

/-- Non-example (for contrast): the identity on `ℝ` does not have bounded variation. -/
example : ¬ BoundedVariationOn (fun x : ℝ => x) Set.univ := by
  intro h
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h
  have h2 := eVariationOn.edist_le (fun x : ℝ => x) (Set.mem_univ ((n : ℝ) + 1))
    (Set.mem_univ (0 : ℝ))
  have h3 : edist ((n : ℝ) + 1) 0 = (n : ℝ≥0∞) + 1 := by
    rw [edist_dist, dist_zero_right, Real.norm_of_nonneg (by positivity),
      ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  have : (n : ℝ≥0∞) + 1 ≤ n := by rw [← h3]; exact h2.trans hn.le
  exact absurd this (by simpa using ENNReal.lt_add_right (ENNReal.natCast_ne_top n) one_ne_zero)
