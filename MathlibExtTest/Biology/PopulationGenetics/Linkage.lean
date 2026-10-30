/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Linkage
public import Mathlib.Tactic.NormNum

@[expose] public section

open Filter Topology MathlibExt.Biology.PopulationGenetics.Linkage

namespace MathlibExtTest.Biology.PopulationGenetics.Linkage

/-! ### Complete coupling disequilibrium (non-vacuity witness)

Only `AB` and `ab` gametes, each at frequency `1/2`: `D = 1/4`, the maximum. With `r = 1/2`
(unlinked loci) one generation gives `x' = (3/8, 1/8, 1/8, 3/8)` and `D' = 1/8`. -/

/-- Gamete frequencies with only coupling gametes `AB` and `ab`. -/
noncomputable def xCoupling : Bool × Bool → ℝ := fun g => if g.1 = g.2 then 1 / 2 else 0

theorem sum_xCoupling : ∑ g, xCoupling g = 1 := by
  norm_num [xCoupling, Fintype.sum_prod_type]

example : linkageDiseq xCoupling = 1 / 4 := by
  norm_num [linkageDiseq, xCoupling]

example : recombine (1 / 2) xCoupling (true, true) = 3 / 8 ∧
    recombine (1 / 2) xCoupling (true, false) = 1 / 8 := by
  norm_num [recombine, alleleFreqFst, alleleFreqSnd, xCoupling]

example : linkageDiseq (recombine (1 / 2) xCoupling) = 1 / 8 := by
  rw [linkageDiseq_recombine sum_xCoupling]
  norm_num [linkageDiseq, xCoupling]

example (t : ℕ) : linkageDiseq ((recombine (1 / 2))^[t] xCoupling) = (1 / 2) ^ t * (1 / 4) := by
  rw [linkageDiseq_iterate sum_xCoupling]
  norm_num [linkageDiseq, xCoupling]

example : Tendsto (fun t : ℕ => linkageDiseq ((recombine (1 / 2))^[t] xCoupling)) atTop (𝓝 0) :=
  tendsto_linkageDiseq_iterate sum_xCoupling (by norm_num) (by norm_num)

/-- Allele frequencies stay at `1/2`. -/
example (a : Bool) : alleleFreqFst (recombine (1 / 2) xCoupling) a = 1 / 2 := by
  rw [alleleFreqFst_recombine sum_xCoupling]
  cases a <;> norm_num [alleleFreqFst, xCoupling]

/-! ### Boundary cases -/

/-- `r = 0` (complete linkage): gamete frequencies never change. -/
example (x : Bool × Bool → ℝ) : recombine 0 x = x := by
  funext g
  simp [recombine]

/-- Linkage equilibrium (`D = 0`) is preserved for every `r`. -/
example (x : Bool × Bool → ℝ) (hx : ∑ g, x g = 1) (hD : linkageDiseq x = 0) (r : ℝ) :
    linkageDiseq (recombine r x) = 0 := by
  rw [linkageDiseq_recombine hx, hD, mul_zero]

example (x : Bool × Bool → ℝ) (hx0 : ∀ g, 0 ≤ x g) (hx : ∑ g, x g = 1) (g : Bool × Bool) :
    0 ≤ recombine (1 / 2) x g ∧ ∑ g, recombine (1 / 2) x g = 1 ∧
      recombine (1 / 2) x (true, true) = x (true, true) - 1 / 2 * linkageDiseq x := by
  refine ⟨recombine_nonneg hx0 (by norm_num) (by norm_num) g, sum_recombine hx _, ?_⟩
  rw [recombine_eq_sub hx]
  simp

/-! ### Haldane's map function -/

/-- Coincident loci are completely linked. -/
example : haldane 0 = 0 := by simp [haldane]

example (d : NNReal) :
    (ProbabilityTheory.poissonMeasure d).real {k | Odd k} = (1 - Real.exp (-2 * d)) / 2 :=
  poissonMeasure_real_odd d

example (d : ℝ) (hd : 0 ≤ d) : 0 ≤ haldane d ∧ haldane d < 1 / 2 :=
  ⟨haldane_nonneg hd, haldane_lt_half d⟩

example : Tendsto haldane atTop (𝓝 (1 / 2)) := tendsto_haldane_atTop

/-- Map distance of `r = (1 - e⁻¹)/2` is `1/2` Morgan. -/
example : haldane (1 / 2) = (1 - Real.exp (-1)) / 2 := by
  norm_num [haldane]

example (r : ℝ) (hr : r < 1 / 2) : haldane (-(1 / 2) * Real.log (1 - 2 * r)) = r :=
  haldane_neg_half_log hr

/-- `r = 1`: disequilibrium vanishes after one generation. -/
example : linkageDiseq (recombine 1 xCoupling) = 0 := by
  rw [linkageDiseq_recombine sum_xCoupling]
  ring

/-- Outside the domain `r < 1/2` of `haldane_neg_half_log`: at `r = 1/2` the inverse map uses
the junk value `log 0 = 0` and returns distance `0`, whose recombination fraction is `0`. -/
example : haldane (-(1 / 2) * Real.log (1 - 2 * (1 / 2))) = 0 := by
  norm_num [haldane]

#print axioms linkageDiseq_iterate
#print axioms poissonMeasure_real_odd
#print axioms tendsto_haldane_atTop

end MathlibExtTest.Biology.PopulationGenetics.Linkage
