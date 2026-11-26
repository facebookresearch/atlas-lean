/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Probability.Distributions.Bernoulli
import MathlibExt.Probability.ProportionalStratification

/-! # Two half-weight strata: independent sampling versus a common coin -/

noncomputable section

open MeasureTheory ProbabilityTheory MathlibExt.Probability
open scoped ENNReal

namespace ProportionalStratificationTest

private abbrev half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
private abbrev coin := bernoulliMeasure true false half
private abbrev population := coin.prod coin
private def bit (b : Bool) : ℝ := if b then 1 else 0
private def outcome (x : Bool × Bool) := bit x.2

private lemma half_mass (j : Bool) : coin.real {j} = 1 / 2 := by
  cases j <;> norm_num [bernoulliMeasure_real_apply, half]

private def strata : Stratification population Bool where
  cell j := {j} ×ˢ Set.univ
  measurableSet_cell _ := (MeasurableSet.singleton _).prod MeasurableSet.univ
  disjoint := by
    intro i j hij
    exact Set.disjoint_left.mpr fun x hx hy ↦ hij (hx.1.symm.trans hy.1)
  covers := Filter.Eventually.of_forall fun x ↦ Set.mem_iUnion.mpr ⟨x.1, rfl, Set.mem_univ _⟩
  mass_ne_zero := by
    intro j h
    have : population.real ({j} ×ˢ Set.univ) = 0 := by
      rw [measureReal_def, h, ENNReal.toReal_zero]
    rw [measureReal_prod_prod, half_mass] at this
    norm_num at this

private lemma weight_half (j : Bool) : strata.weight j = 1 / 2 := by
  simp [Stratification.weight, strata, measureReal_prod_prod, half_mass]

-- Pinning the first bit to `j` and tossing the second bit gives the *actual* conditional law.
private lemma conditional (j : Bool) : population[|strata.cell j] = coin.map (Prod.mk j) := by
  change population[|{j} ×ˢ Set.univ] = _
  have hj : coin {j} ≠ 0 := by
    intro h
    simpa [measureReal_def, h] using half_mass j
  rw [ProbabilityTheory.cond, Measure.prod_prod, measure_univ, mul_one, ← Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_singleton, Measure.prod_smul_left, smul_smul,
    ENNReal.inv_mul_cancel hj (measure_ne_top _ _), one_smul, Measure.dirac_prod]

private lemma pin (j : Bool) : MeasurePreserving (Prod.mk j) coin population[|strata.cell j] :=
  ⟨measurable_prodMk_left, (conditional j).symm⟩

private lemma var_bit : Var[bit; coin] = 1 / 4 := by
  rw [variance_eq_sub (MemLp.of_discrete : MemLp bit 2 coin)]
  norm_num [integral_bernoulliMeasure, Pi.pow_apply, bit, half]

private lemma within : strata.withinVariance outcome = 1 / 4 := by
  have hv (j : Bool) : Var[outcome; population[|strata.cell j]] = 1 / 4 :=
    ((pin j).variance_fun_comp (f := outcome) (.of_discrete)).symm.trans var_bit
  norm_num [Stratification.withinVariance, weight_half, hv, Fintype.sum_bool]

private abbrev counts (_ : Bool) := 1
private lemma allocation (j : Bool) : (counts j : ℝ) = (2 : ℕ) * strata.weight j := by
  norm_num [weight_half]

-- Independent conditional draws, one per cell.
example : Var[strata.estimator outcome counts; strata.sampleLaw counts] = 1 / 8 := by
  rw [strata.variance_proportional MemLp.of_discrete (by decide : 0 < 2) allocation, within]
  norm_num

-- The same Bernoulli outcome is shared by both strata. Each marginal is still correct, but
-- the very same estimator is now just the common coin, with variance 1/4 rather than 1/8.
private def shared (b : Bool) (t : Σ j, Fin (counts j)) := (t.1, b)

example (t : Σ j, Fin (counts j)) :
    MeasurePreserving (fun b ↦ shared b t) coin population[|strata.cell t.1] := pin _

private lemma shared_variance : Var[fun b ↦ strata.estimator outcome counts (shared b); coin] = 1 / 4 := by
  have h (b : Bool) : strata.estimator outcome counts (shared b) = bit b := by
    simp [Stratification.estimator, counts, shared, outcome, weight_half]
  simp_rw [h]
  exact var_bit

example : ¬ iIndepFun (fun (t : Σ j, Fin (counts j)) b ↦ shared b t) coin := by
  intro hi
  have h := strata.variance_proportional_of_indep (f := outcome) MemLp.of_discrete
    (by decide : 0 < 2) allocation (fun t ↦ (pin t.1).hasLaw) hi
  change Var[fun b ↦ strata.estimator outcome counts (shared b); coin] = _ at h
  rw [shared_variance, within] at h
  norm_num at h

-- Reading the label instead of the second bit makes the within-cell variance vanish. Plain
-- MC still sees a random bit, so the equal-size comparison is strict for this integrand.
example : Var[strata.estimator (fun x ↦ bit x.1) counts; strata.sampleLaw counts] <
    Var[Stratification.plainMean (fun x ↦ bit x.1) 2; Measure.pi (fun _ : Fin 2 ↦ population)] := by
  have hcell (j : Bool) : Var[fun x : Bool × Bool ↦ bit x.1; population[|strata.cell j]] = 0 := by
    rw [← (pin j).variance_fun_comp (f := fun x ↦ bit x.1) (.of_discrete)]
    simp [variance_eq_integral aemeasurable_const]
  have hpop := (measurePreserving_fst (μ := coin) (ν := coin)).variance_fun_comp (f := bit)
    (.of_discrete)
  rw [strata.variance_proportional MemLp.of_discrete (by decide : 0 < 2) allocation,
    Stratification.withinVariance, Stratification.variance_plainMean MemLp.of_discrete (by decide),
    hpop, var_bit]
  simp [hcell]

-- At cost 2 per stratified draw and 1 per plain draw, budget 4 buys two versus four
-- observations. There is no between-cell variation for `outcome`, so plain MC wins strictly.
example : Var[Stratification.plainMean outcome 4; Measure.pi (fun _ : Fin 4 ↦ population)] <
    Var[strata.estimator outcome counts; strata.sampleLaw counts] := by
  have hpop : Var[outcome; population] = 1 / 4 :=
    (measurePreserving_snd.variance_fun_comp (f := bit) (.of_discrete)).trans var_bit
  obtain ⟨hs, hp, _⟩ := strata.equal_budget (f := outcome) MemLp.of_discrete
    (np := 4) (by norm_num : (0 : ℝ) < 4) (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 1) (by norm_num) (by norm_num) allocation
  rw [hs, hp, within, hpop]
  norm_num

end ProportionalStratificationTest
