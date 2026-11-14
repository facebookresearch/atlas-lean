/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Causality.ExposureMapping
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Tactic.NormNum

/-!
# Boundary tests for exposure mappings

Two units joined by an edge with independent fair-coin treatments; the
fine exposure is (own treatment, neighbour treatment).

* Nonvacuity: spillover outcomes satisfy the design-free Condition 1, every
  `πᵢ(d) = 1/4`, and the HT exposure-total estimator, built from the
  observed outcomes, is unbiased for all four exposures, both for
  `exposurePotential` and for the explicit potentials `yPot`; the mean
  estimator targets `μ((1, 1)) = 7 / 2`.
* Violated sufficiency: the coarser "own treatment only" map with the
  same spillover outcomes has no potential outcomes, and the same
  estimator for the coarse map has expectation `-1` at `false`, which
  estimates no potential-outcome total.
* Zero exposure probability: a design that never treats both units has
  `πᵢ((1, 1)) = 0` and estimator expectation `0`, while the design-free
  potential-outcome total at `(1, 1)` is `7`.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Causality.ExposureMapping

open MathlibExt.Probability.Causality MathlibExt.Probability.Sampling

/-- Bit indicator as a real number. -/
def bit : Bool → ℝ := fun b => if b then 1 else 0

/-- Unit constants: `c 0 = -1`, `c 1 = -2`. -/
def c : Fin 2 → ℝ := fun i => if i = 0 then -1 else -2

/-- Fine exposure: own treatment and neighbour treatment. -/
def exMap : Fin 2 → Bool × Bool → Bool × Bool :=
  fun i z => if i = 0 then z else (z.2, z.1)

/-- Coarse exposure: own treatment only. -/
def coarseMap : Fin 2 → Bool × Bool → Bool :=
  fun i z => if i = 0 then z.1 else z.2

/-- Spillover outcomes: `3 * own + 2 * neighbour + c`. -/
def yr : Fin 2 → Bool × Bool → ℝ :=
  fun i z => 3 * bit (exMap i z).1 + 2 * bit (exMap i z).2 + c i

/-- Uniform mass over the four assignments. -/
noncomputable def unifMass : Bool × Bool → ENNReal :=
  fun _ => ENNReal.ofReal (1 / 4 : ℝ)

/-- The uniform masses sum to one. -/
theorem unifMass_sum : ∑ z : Bool × Bool, unifMass z = 1 := by
  simp only [unifMass, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  have h14 : ((1 / 4 : ℝ) + 1 / 4) + (1 / 4 + 1 / 4) = 1 := by norm_num
  rw [h14, ENNReal.ofReal_one]

/-- Uniform design on assignments. -/
noncomputable def unifP : PMF (Bool × Bool) :=
  PMF.ofFintype unifMass unifMass_sum

/-- Point masses of the uniform design. -/
theorem unif_toReal (z : Bool × Bool) : (unifP z).toReal = 1 / 4 := by
  have h : ∀ w : Bool × Bool, unifP w = ENNReal.ofReal (1 / 4 : ℝ) := by
    intro w
    simp [unifP, PMF.ofFintype_apply, unifMass]
  rw [h z, ENNReal.toReal_ofReal (by norm_num)]

/-- Every assignment has positive mass. -/
theorem unifP_ne_zero (z : Bool × Bool) : unifP z ≠ 0 := by
  have h : unifP z = ENNReal.ofReal (1 / 4 : ℝ) := by
    simp [unifP, PMF.ofFintype_apply, unifMass]
  rw [h]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))

/-- Condition 1 holds for the fine map: outcomes depend on the
assignment only through the exposure. -/
theorem sufficiency : ExposureSufficiency exMap yr := by
  intro i z z' h
  show 3 * bit (exMap i z).1 + 2 * bit (exMap i z).2 + c i
    = 3 * bit (exMap i z').1 + 2 * bit (exMap i z').2 + c i
  rw [h]

/-- Explicit exposure potentials of the spillover outcomes. -/
def yPot : Fin 2 → Bool × Bool → ℝ :=
  fun i d => 3 * bit d.1 + 2 * bit d.2 + c i

/-- The observed outcomes are the explicit potentials at the realized
exposure, at every assignment. -/
theorem yPot_consistent (i : Fin 2) (z : Bool × Bool) :
    yr i z = yPot i (exMap i z) := rfl

/-- Exposure probabilities are `1/4` at unit `0`. -/
theorem pi_quarter_0 (d : Bool × Bool) :
    exposureProbability exMap unifP 0 d = 1 / 4 := by
  rw [exposureProbability_eq_sum]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  obtain ⟨d1, d2⟩ := d
  cases d1 <;> cases d2 <;> norm_num [exMap, unif_toReal]

/-- Exposure probabilities are `1/4` at unit `1`. -/
theorem pi_quarter_1 (d : Bool × Bool) :
    exposureProbability exMap unifP 1 d = 1 / 4 := by
  rw [exposureProbability_eq_sum]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  obtain ⟨d1, d2⟩ := d
  cases d1 <;> cases d2 <;> norm_num [exMap, unif_toReal]

/-- Every unit has positive exposure probability under the uniform design. -/
theorem pi_pos (d : Bool × Bool) : ∀ i, 0 < exposureProbability exMap unifP i d := by
  rw [Fin.forall_fin_two]
  constructor
  · rw [pi_quarter_0 d]
    norm_num
  · rw [pi_quarter_1 d]
    norm_num

/-- Nonvacuity: unbiasedness for every exposure, under Condition 1. -/
theorem nonvacuous_unbiased (d : Bool × Bool) :
    ∫ z, exposureHTTotal exMap unifP yr d z ∂unifP.toMeasure
      = ∑ i, exposurePotential exMap yr i d :=
  integral_exposureHTTotal exMap unifP yr sufficiency d (pi_pos d)

/-- Nonvacuity: unbiasedness for the explicit potentials `yPot`. -/
theorem nonvacuous_unbiased_explicit (d : Bool × Bool) :
    ∫ z, exposureHTTotal exMap unifP yr d z ∂unifP.toMeasure
      = ∑ i, yPot i d :=
  integral_exposureHTTotal_of_consistent exMap unifP yr yPot
    (fun i z _ => yPot_consistent i z) d (pi_pos d)

/-- The `(1, 1)` potential-outcome total is `7`; it does not depend on a
design. -/
theorem total_TT :
    (∑ i, exposurePotential exMap yr i (true, true)) = 7 := by
  have e0 : exMap 0 (true, true) = (true, true) := rfl
  have e1 : exMap 1 (true, true) = (true, true) := rfl
  rw [Fin.sum_univ_two,
    exposurePotential_eq_of_mem _ _ sufficiency _ _ _ e0,
    exposurePotential_eq_of_mem _ _ sufficiency _ _ _ e1]
  norm_num [yr, bit, c, exMap]

/-- The mean estimator at `(1, 1)` targets Aronow and Samii's mean
`μ((1, 1)) = 7 / 2`. -/
theorem mean_TT :
    ∫ z, exposureHTTotal exMap unifP yr (true, true) z / (Fintype.card (Fin 2) : ℝ)
      ∂unifP.toMeasure = 7 / 2 := by
  rw [integral_exposureHTTotal_div_card exMap unifP yr sufficiency _ (pi_pos _),
    total_TT]
  norm_num

/-- The explicit potentials give the same `(1, 1)` total. -/
theorem yPot_total_TT : (∑ i, yPot i (true, true)) = 7 := by
  norm_num [Fin.sum_univ_two, yPot, bit, c]

/-- Values of `yr` at the two witnesses: they differ on one exposure class. -/
theorem v0 : yr 0 (false, false) = -1 := by norm_num [yr, bit, c, exMap]

/-- Values of `yr` at the two witnesses: they differ on one exposure class. -/
theorem v1 : yr 0 (false, true) = 1 := by norm_num [yr, bit, c, exMap]

/-- Violated sufficiency: the coarse map is not exposure-sufficient. -/
theorem coarse_not_sufficient :
    ¬ ExposureSufficiency coarseMap yr := by
  intro h
  have h0 := h 0 (false, false) (false, true) rfl
  rw [v0, v1] at h0
  norm_num at h0

/-- Violated sufficiency: no potential-outcome function exists. -/
theorem coarse_no_factorization :
    ¬ ∃ y : Fin 2 → Bool → ℝ, ∀ i z, unifP z ≠ 0
      → yr i z = y i (coarseMap i z) := by
  intro hcon
  obtain ⟨y, hy⟩ := hcon
  have h1 := hy 0 (false, false) (unifP_ne_zero _)
  have h2 := hy 0 (false, true) (unifP_ne_zero _)
  have c0 : coarseMap 0 (false, false) = false := rfl
  have c1 : coarseMap 0 (false, true) = false := rfl
  rw [c0] at h1
  rw [c1] at h2
  rw [v0] at h1
  rw [v1] at h2
  rw [← h2] at h1
  norm_num at h1

/-- Coarse exposure probabilities are `1/2` at unit `0`. -/
theorem coarse_pi_0 (d : Bool) :
    exposureProbability coarseMap unifP 0 d = 1 / 2 := by
  rw [exposureProbability_eq_sum]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  cases d <;> norm_num [coarseMap, unif_toReal]

/-- Coarse exposure probabilities are `1/2` at unit `1`. -/
theorem coarse_pi_1 (d : Bool) :
    exposureProbability coarseMap unifP 1 d = 1 / 2 := by
  rw [exposureProbability_eq_sum]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  cases d <;> norm_num [coarseMap, unif_toReal]

/-- Coarse exposed sets at each assignment. -/
theorem coarse_set_FF :
    exposedSet coarseMap false (false, false) = {0, 1} := by decide

/-- Coarse exposed sets at each assignment. -/
theorem coarse_set_FT :
    exposedSet coarseMap false (false, true) = {0} := by decide

/-- Coarse exposed sets at each assignment. -/
theorem coarse_set_TF :
    exposedSet coarseMap false (true, false) = {1} := by decide

/-- Coarse exposed sets at each assignment. -/
theorem coarse_set_TT :
    exposedSet coarseMap false (true, true) = ∅ := by decide

/-- Coarse estimator values at each assignment. -/
theorem coarseHT_FF :
    exposureHTTotal coarseMap unifP yr false (false, false) = -6 := by
  simp only [exposureHTTotal, coarse_set_FF]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, coarse_pi_0, coarse_pi_1]
  norm_num [yr, bit, c, exMap]

/-- Coarse estimator values at each assignment. -/
theorem coarseHT_FT :
    exposureHTTotal coarseMap unifP yr false (false, true) = 2 := by
  simp only [exposureHTTotal, coarse_set_FT, Finset.sum_singleton]
  rw [coarse_pi_0]
  norm_num [yr, bit, c, exMap]

/-- Coarse estimator values at each assignment. -/
theorem coarseHT_TF :
    exposureHTTotal coarseMap unifP yr false (true, false) = 0 := by
  simp only [exposureHTTotal, coarse_set_TF, Finset.sum_singleton]
  rw [coarse_pi_1]
  norm_num [yr, bit, c, exMap]

/-- Coarse estimator values at each assignment. -/
theorem coarseHT_TT :
    exposureHTTotal coarseMap unifP yr false (true, true) = 0 := by
  simp only [exposureHTTotal, coarse_set_TT, Finset.sum_empty]

/-- The coarse estimator expectation is `-1`: it estimates no
potential-outcome total (`coarse_no_factorization`). -/
theorem coarse_expectation :
    (∫ z, exposureHTTotal coarseMap unifP yr false z ∂unifP.toMeasure) = -1 := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_bool,
    unif_toReal, coarseHT_FF, coarseHT_FT, coarseHT_TF, coarseHT_TT]
  norm_num

/-- Mass for the design that never treats both units. -/
noncomputable def noBothMass : Bool × Bool → ENNReal :=
  fun z => if z = (true, true) then 0 else ENNReal.ofReal (1 / 3)

/-- The never-both masses sum to one. -/
theorem noBothMass_sum : ∑ z : Bool × Bool, noBothMass z = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  have mFF : noBothMass (false, false) = ENNReal.ofReal (1 / 3 : ℝ) := by
    simp [noBothMass]
  have mFT : noBothMass (false, true) = ENNReal.ofReal (1 / 3 : ℝ) := by
    simp [noBothMass]
  have mTF : noBothMass (true, false) = ENNReal.ofReal (1 / 3 : ℝ) := by
    simp [noBothMass]
  have mTT : noBothMass (true, true) = 0 := by simp [noBothMass]
  rw [mFF, mFT, mTF, mTT, zero_add,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  have h13 : (1 / 3 : ℝ) + (1 / 3 + 1 / 3) = 1 := by norm_num
  rw [h13, ENNReal.ofReal_one]

/-- Design that never treats both units. -/
noncomputable def noBothP : PMF (Bool × Bool) :=
  PMF.ofFintype noBothMass noBothMass_sum

/-- Point masses of the never-both design. -/
theorem noBoth_toReal_FF : (noBothP (false, false)).toReal = 1 / 3 := by
  have h : noBothP (false, false) = ENNReal.ofReal (1 / 3 : ℝ) := by
    simp [noBothP, PMF.ofFintype_apply, noBothMass]
  rw [h, ENNReal.toReal_ofReal (by norm_num)]

/-- Point masses of the never-both design. -/
theorem noBoth_toReal_FT : (noBothP (false, true)).toReal = 1 / 3 := by
  have h : noBothP (false, true) = ENNReal.ofReal (1 / 3 : ℝ) := by
    simp [noBothP, PMF.ofFintype_apply, noBothMass]
  rw [h, ENNReal.toReal_ofReal (by norm_num)]

/-- Point masses of the never-both design. -/
theorem noBoth_toReal_TF : (noBothP (true, false)).toReal = 1 / 3 := by
  have h : noBothP (true, false) = ENNReal.ofReal (1 / 3 : ℝ) := by
    simp [noBothP, PMF.ofFintype_apply, noBothMass]
  rw [h, ENNReal.toReal_ofReal (by norm_num)]

/-- Point masses of the never-both design. -/
theorem noBoth_toReal_TT : (noBothP (true, true)).toReal = 0 := by
  have h : noBothP (true, true) = 0 := by
    simp [noBothP, PMF.ofFintype_apply, noBothMass]
  rw [h, ENNReal.toReal_zero]

/-- The `(1, 1)` exposure probability is zero at unit `0`. -/
theorem zero_pi_0 :
    exposureProbability exMap noBothP 0 (true, true) = 0 := by
  rw [exposureProbability_eq_sum]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [exMap, noBoth_toReal_FF, noBoth_toReal_FT, noBoth_toReal_TF,
    noBoth_toReal_TT]

/-- The `(1, 1)` exposure probability is zero at unit `1`. -/
theorem zero_pi_1 :
    exposureProbability exMap noBothP 1 (true, true) = 0 := by
  rw [exposureProbability_eq_sum]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [exMap, noBoth_toReal_FF, noBoth_toReal_FT, noBoth_toReal_TF,
    noBoth_toReal_TT]

/-- Exposed sets for `(1, 1)` under the never-both assignments. -/
theorem zero_set_FF :
    exposedSet exMap (true, true) (false, false) = ∅ := by decide

/-- Exposed sets for `(1, 1)` under the never-both assignments. -/
theorem zero_set_FT :
    exposedSet exMap (true, true) (false, true) = ∅ := by decide

/-- Exposed sets for `(1, 1)` under the never-both assignments. -/
theorem zero_set_TF :
    exposedSet exMap (true, true) (true, false) = ∅ := by decide

/-- Estimator values at the never-both assignments vanish. -/
theorem zero_est_FF :
    exposureHTTotal exMap noBothP yr (true, true) (false, false) = 0 := by
  simp only [exposureHTTotal, zero_set_FF, Finset.sum_empty]

/-- Estimator values at the never-both assignments vanish. -/
theorem zero_est_FT :
    exposureHTTotal exMap noBothP yr (true, true) (false, true) = 0 := by
  simp only [exposureHTTotal, zero_set_FT, Finset.sum_empty]

/-- Estimator values at the never-both assignments vanish. -/
theorem zero_est_TF :
    exposureHTTotal exMap noBothP yr (true, true) (true, false) = 0 := by
  simp only [exposureHTTotal, zero_set_TF, Finset.sum_empty]

/-- The `(1, 1)` estimator expectation is zero. -/
theorem zero_expectation :
    (∫ z, exposureHTTotal exMap noBothP yr (true, true) z
      ∂noBothP.toMeasure) = 0 := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_bool,
    zero_est_FF, zero_est_FT, zero_est_TF, noBoth_toReal_TT]
  simp

/-- The zero-probability estimator misses the true total `7`: the target
`∑ i, exposurePotential exMap yr i (true, true)` is the same design-free
total as in `total_TT`. -/
theorem zero_bias :
    (∫ z, exposureHTTotal exMap noBothP yr (true, true) z
      ∂noBothP.toMeasure)
      ≠ (∑ i, exposurePotential exMap yr i (true, true)) := by
  rw [zero_expectation, total_TT]
  norm_num

/-- The same miss, against the explicit potentials `yPot`. -/
theorem zero_bias_explicit :
    (∫ z, exposureHTTotal exMap noBothP yr (true, true) z
      ∂noBothP.toMeasure) ≠ (∑ i, yPot i (true, true)) := by
  rw [zero_expectation, yPot_total_TT]
  norm_num

end MathlibExtTest.Probability.Causality.ExposureMapping
