/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.CylinderDerivative

/-!
# Tests for `MathlibExt.Probability.Percolation.CylinderDerivative`

Tests Russo's formula (`StatMech.Percolation.russo_derivative`, `russo_formula`,
`russo_derivative_measure`) on the one-edge space `E = Unit` with the increasing event
`A = {ω | ω () = true}` (the edge is open), at `p = 1/2`. The hypothesis `IsIncreasing A` is proved,
and the pivotal sum is computed: the edge is always pivotal, so `∑_e pivotalProb p A e = 1`, and
Russo's formula gives `d/dp ℙ_p(A) = 1` at `p = 1/2`. Also computes `measureProb A p = p` on
`[0, 1]` and `measureProb A 2 = 2` outside it (the polynomial extension).
-/

@[expose] public section

open StatMech StatMech.Percolation
open scoped NNReal

namespace MathlibExtTest.StatMech.Probability.Percolation.CylinderDerivative

/-- The event "the single edge is open". -/
def edgeOpen : Set (ConfigSpace Unit) := {ω | ω () = true}

-- `edgeOpen` is increasing.
theorem edgeOpen_increasing : IsIncreasing edgeOpen := by
  intro a b hab ha
  have h := hab ()
  simp only [edgeOpen, Set.mem_ofPred_eq] at ha ⊢
  rw [ha] at h
  cases hb : b ()
  · rw [hb] at h; exact absurd h (by decide)
  · rfl

-- The weight polynomial of `edgeOpen` is `p`.
theorem prob_edgeOpen (p : ℝ) : prob p edgeOpen = p := by
  rw [prob, ← (Equiv.funUnique Unit Bool).symm.sum_comp]
  simp [edgeOpen, configWeight, edgeWeight, Set.indicator]

-- The single edge is pivotal in every configuration, so its pivotal weight is `1`.
theorem pivotalProb_edgeOpen (p : ℝ) : pivotalProb p edgeOpen () = 1 := by
  rw [pivotalProb, ← (Equiv.funUnique Unit Bool).symm.sum_comp]
  simp [edgeOpen, configWeight, edgeWeight, Set.indicator, IsPivotal, setOpen, setClosed]

-- `measureProb` agrees with the polynomial on `[0, 1]` and outside it.
example : measureProb edgeOpen (1 / 2) = 1 / 2 := by
  rw [measureProb_eq_prob _ (by norm_num) (by norm_num), prob_edgeOpen]

example : measureProb edgeOpen 2 = 2 := by
  unfold measureProb
  split_ifs with h
  · norm_num at h
  · exact prob_edgeOpen 2

-- Russo's formula at `p = 1/2`, with the concrete derivative `1`.
example : HasDerivAt (fun p => measureProb edgeOpen p) 1 (1 / 2) := by
  have h := russo_derivative edgeOpen edgeOpen_increasing (p := 1 / 2) (by norm_num) (by norm_num)
  simpa [pivotalProb_edgeOpen] using h

example : deriv (fun p => measureProb edgeOpen p) (1 / 2) = 1 := by
  rw [russo_formula edgeOpen edgeOpen_increasing (by norm_num) (by norm_num)]
  simp [pivotalProb_edgeOpen]

-- The `ℝ≥0` form, which also identifies `measureProb` with the Bernoulli product measure.
example (hp : (1 / 2 : ℝ≥0) ≤ 1) :
    measureProb edgeOpen ((1 / 2 : ℝ≥0) : ℝ) =
      (bernoulliProductMeasure (E := Unit) (1 / 2) hp).real edgeOpen :=
  (russo_derivative_measure edgeOpen edgeOpen_increasing (1 / 2) hp (by norm_num)
    (by norm_num)).2

end MathlibExtTest.StatMech.Probability.Percolation.CylinderDerivative
