/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Sampling.HorvitzThompsonVariance
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.ENNReal.Real
import Mathlib.Tactic.NormNum.Basic

/-!
# Boundary tests for Horvitz-Thompson variance and the Sen-Yates-Grundy form

Non-vacuity on SRSWOR `N = 3, n = 2`; the Bernoulli fixed-expected-size
counterexample; and the systematic zero-pair-inclusion design.
-/

@[expose] public section

namespace MathlibExt.Probability.Sampling.Test

private theorem sum_univ_fin2 {M : Type*} [AddCommMonoid M]
    (g : Finset (Fin 2) → M) :
    ∑ s, g s = g ∅ + (g {0} + (g {1} + g {0, 1})) := by
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have hsub : ∀ s : Finset (Fin 2), s ∈ Finset.powerset {0, 1} := by
    intro s
    rw [Finset.mem_powerset, ← huniv]
    exact Finset.subset_univ s
  have hps : Finset.powerset ({0, 1} : Finset (Fin 2)) = Finset.univ :=
    Finset.eq_univ_of_forall hsub
  have hlist : Finset.powerset ({0, 1} : Finset (Fin 2))
      = {∅, {0}, {1}, {0, 1}} := by decide
  calc ∑ s, g s
      = ∑ s ∈ Finset.powerset {0, 1}, g s := by rw [hps]
    _ = g ∅ + (g {0} + (g {1} + g {0, 1})) := by
        rw [hlist, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_singleton]

private theorem sum_univ_fin3 {M : Type*} [AddCommMonoid M]
    (g : Finset (Fin 3) → M) :
    ∑ s, g s = g ∅ + (g {0} + (g {1} + (g {2} + (g {0, 1}
      + (g {0, 2} + (g {1, 2} + g {0, 1, 2})))))) := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have hsub : ∀ s : Finset (Fin 3), s ∈ Finset.powerset {0, 1, 2} := by
    intro s
    rw [Finset.mem_powerset, ← huniv]
    exact Finset.subset_univ s
  have hps : Finset.powerset ({0, 1, 2} : Finset (Fin 3)) = Finset.univ :=
    Finset.eq_univ_of_forall hsub
  have hlist : Finset.powerset ({0, 1, 2} : Finset (Fin 3))
      = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  calc ∑ s, g s
      = ∑ s ∈ Finset.powerset {0, 1, 2}, g s := by rw [hps]
    _ = g ∅ + (g {0} + (g {1} + (g {2} + (g {0, 1}
      + (g {0, 2} + (g {1, 2} + g {0, 1, 2})))))) := by
        rw [hlist, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_singleton]

/-- SRSWOR `N = 3, n = 2`: mass `1/3` on each 2-subset. -/
noncomputable def srsworMass : Finset (Fin 3) → ENNReal :=
  fun s => if s = {0, 1} ∨ s = {0, 2} ∨ s = {1, 2} then
    ENNReal.ofReal (1 / 3) else 0

private theorem srswor_m01 : srsworMass {0, 1} = ENNReal.ofReal (1 / 3) := by
  have h : (({0, 1} : Finset (Fin 3)) = {0, 1}
      ∨ ({0, 1} : Finset (Fin 3)) = {0, 2}
      ∨ ({0, 1} : Finset (Fin 3)) = {1, 2}) := Or.inl rfl
  unfold srsworMass
  rw [ite_eq_left h]

private theorem srswor_m02 : srsworMass {0, 2} = ENNReal.ofReal (1 / 3) := by
  have h : (({0, 2} : Finset (Fin 3)) = {0, 1}
      ∨ ({0, 2} : Finset (Fin 3)) = {0, 2}
      ∨ ({0, 2} : Finset (Fin 3)) = {1, 2}) := Or.inr (Or.inl rfl)
  unfold srsworMass
  rw [ite_eq_left h]

private theorem srswor_m12 : srsworMass {1, 2} = ENNReal.ofReal (1 / 3) := by
  have h : (({1, 2} : Finset (Fin 3)) = {0, 1}
      ∨ ({1, 2} : Finset (Fin 3)) = {0, 2}
      ∨ ({1, 2} : Finset (Fin 3)) = {1, 2}) := Or.inr (Or.inr rfl)
  unfold srsworMass
  rw [ite_eq_left h]

private theorem srswor_m0 : srsworMass {0} = 0 := by
  have h : ¬((({0} : Finset (Fin 3)) = {0, 1}
      ∨ ({0} : Finset (Fin 3)) = {0, 2}
      ∨ ({0} : Finset (Fin 3)) = {1, 2})) := by decide
  unfold srsworMass
  rw [ite_eq_right h]

private theorem srswor_m1 : srsworMass {1} = 0 := by
  have h : ¬((({1} : Finset (Fin 3)) = {0, 1}
      ∨ ({1} : Finset (Fin 3)) = {0, 2}
      ∨ ({1} : Finset (Fin 3)) = {1, 2})) := by decide
  unfold srsworMass
  rw [ite_eq_right h]

private theorem srswor_m2 : srsworMass {2} = 0 := by
  have h : ¬((({2} : Finset (Fin 3)) = {0, 1}
      ∨ ({2} : Finset (Fin 3)) = {0, 2}
      ∨ ({2} : Finset (Fin 3)) = {1, 2})) := by decide
  unfold srsworMass
  rw [ite_eq_right h]

private theorem srswor_me : srsworMass ∅ = 0 := by
  have h : ¬(((∅ : Finset (Fin 3)) = {0, 1}
      ∨ (∅ : Finset (Fin 3)) = {0, 2}
      ∨ (∅ : Finset (Fin 3)) = {1, 2})) := by decide
  unfold srsworMass
  rw [ite_eq_right h]

private theorem srswor_mf : srsworMass {0, 1, 2} = 0 := by
  have h : ¬((({0, 1, 2} : Finset (Fin 3)) = {0, 1}
      ∨ ({0, 1, 2} : Finset (Fin 3)) = {0, 2}
      ∨ ({0, 1, 2} : Finset (Fin 3)) = {1, 2})) := by decide
  unfold srsworMass
  rw [ite_eq_right h]

/-- The SRSWOR masses sum to one. -/
theorem srsworMass_sum : ∑ s, srsworMass s = 1 := by
  rw [sum_univ_fin3, srswor_me, srswor_m0, srswor_m1, srswor_m2,
    srswor_m01, srswor_m02, srswor_m12, srswor_mf, zero_add, add_zero,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- SRSWOR `N = 3, n = 2` as a normalized `PMF`. -/
noncomputable def srsworPmf : PMF (Finset (Fin 3)) :=
  PMF.ofFintype srsworMass srsworMass_sum

private theorem srswor_t01 : (srsworPmf {0, 1}).toReal = (1 / 3 : ℝ) := by
  calc (srsworPmf {0, 1}).toReal = (srsworMass {0, 1}).toReal := rfl
    _ = (1 / 3 : ℝ) := by
        rw [srswor_m01, ENNReal.toReal_ofReal (by norm_num)]

private theorem srswor_t02 : (srsworPmf {0, 2}).toReal = (1 / 3 : ℝ) := by
  calc (srsworPmf {0, 2}).toReal = (srsworMass {0, 2}).toReal := rfl
    _ = (1 / 3 : ℝ) := by
        rw [srswor_m02, ENNReal.toReal_ofReal (by norm_num)]

private theorem srswor_t12 : (srsworPmf {1, 2}).toReal = (1 / 3 : ℝ) := by
  calc (srsworPmf {1, 2}).toReal = (srsworMass {1, 2}).toReal := rfl
    _ = (1 / 3 : ℝ) := by
        rw [srswor_m12, ENNReal.toReal_ofReal (by norm_num)]

private theorem srswor_t0 : (srsworPmf {0}).toReal = 0 := by
  calc (srsworPmf {0}).toReal = (srsworMass {0}).toReal := rfl
    _ = 0 := by rw [srswor_m0, ENNReal.toReal_zero]

private theorem srswor_t1 : (srsworPmf {1}).toReal = 0 := by
  calc (srsworPmf {1}).toReal = (srsworMass {1}).toReal := rfl
    _ = 0 := by rw [srswor_m1, ENNReal.toReal_zero]

private theorem srswor_t2 : (srsworPmf {2}).toReal = 0 := by
  calc (srsworPmf {2}).toReal = (srsworMass {2}).toReal := rfl
    _ = 0 := by rw [srswor_m2, ENNReal.toReal_zero]

private theorem srswor_te : (srsworPmf ∅).toReal = 0 := by
  calc (srsworPmf ∅).toReal = (srsworMass ∅).toReal := rfl
    _ = 0 := by rw [srswor_me, ENNReal.toReal_zero]

private theorem srswor_tf : (srsworPmf {0, 1, 2}).toReal = 0 := by
  calc (srsworPmf {0, 1, 2}).toReal = (srsworMass {0, 1, 2}).toReal := rfl
    _ = 0 := by rw [srswor_mf, ENNReal.toReal_zero]

private theorem srswor_h00 : ∀ (c : Prop) [Decidable c],
    (if c then (0 : ℝ) else 0) = 0 := by
  intro c _
  by_cases h : c <;> simp [h]

private theorem srswor_pi : ∀ i, inclusionProbability srsworPmf i
    = (if i ∈ ({0, 1} : Finset (Fin 3)) then (1 / 3 : ℝ) else 0)
    + ((if i ∈ ({0, 2} : Finset (Fin 3)) then (1 / 3 : ℝ) else 0)
    + (if i ∈ ({1, 2} : Finset (Fin 3)) then (1 / 3 : ℝ) else 0)) := by
  intro i
  unfold inclusionProbability
  rw [sum_univ_fin3, srswor_te, srswor_t0, srswor_t1, srswor_t2,
    srswor_t01, srswor_t02, srswor_t12, srswor_tf]
  simp only [srswor_h00, zero_add, add_zero]

private theorem srswor_pair : ∀ i j, pairInclusionProbability srsworPmf i j
    = (if i ∈ ({0, 1} : Finset (Fin 3)) ∧ j ∈ ({0, 1} : Finset (Fin 3))
      then (1 / 3 : ℝ) else 0)
    + ((if i ∈ ({0, 2} : Finset (Fin 3)) ∧ j ∈ ({0, 2} : Finset (Fin 3))
      then (1 / 3 : ℝ) else 0)
    + (if i ∈ ({1, 2} : Finset (Fin 3)) ∧ j ∈ ({1, 2} : Finset (Fin 3))
      then (1 / 3 : ℝ) else 0)) := by
  intro i j
  unfold pairInclusionProbability
  rw [sum_univ_fin3, srswor_te, srswor_t0, srswor_t1, srswor_t2,
    srswor_t01, srswor_t02, srswor_t12, srswor_tf]
  simp only [srswor_h00, zero_add, add_zero]

/-- First inclusion probabilities of SRSWOR `N = 3, n = 2`. -/
theorem srswor_pi0 : inclusionProbability srsworPmf 0 = 2 / 3 := by
  have c1 : (0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) := by decide
  have c2 : (0 : Fin 3) ∈ ({0, 2} : Finset (Fin 3)) := by decide
  have c3 : ¬((0 : Fin 3) ∈ ({1, 2} : Finset (Fin 3))) := by decide
  rw [srswor_pi, ite_eq_left c1, ite_eq_left c2, ite_eq_right c3]
  norm_num

/-- First inclusion probabilities of SRSWOR `N = 3, n = 2`. -/
theorem srswor_pi1 : inclusionProbability srsworPmf 1 = 2 / 3 := by
  have c1 : (1 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) := by decide
  have c2 : ¬((1 : Fin 3) ∈ ({0, 2} : Finset (Fin 3))) := by decide
  have c3 : (1 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := by decide
  rw [srswor_pi, ite_eq_left c1, ite_eq_right c2, ite_eq_left c3]
  norm_num

/-- First inclusion probabilities of SRSWOR `N = 3, n = 2`. -/
theorem srswor_pi2 : inclusionProbability srsworPmf 2 = 2 / 3 := by
  have c1 : ¬((2 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))) := by decide
  have c2 : (2 : Fin 3) ∈ ({0, 2} : Finset (Fin 3)) := by decide
  have c3 : (2 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := by decide
  rw [srswor_pi, ite_eq_right c1, ite_eq_left c2, ite_eq_left c3]
  norm_num

/-- Pair inclusion probabilities of SRSWOR `N = 3, n = 2`. -/
theorem srswor_pij_01 : pairInclusionProbability srsworPmf 0 1 = 1 / 3 := by
  have c1 : (0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))
      ∧ (1 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) := by decide
  have c2 : ¬((0 : Fin 3) ∈ ({0, 2} : Finset (Fin 3))
      ∧ (1 : Fin 3) ∈ ({0, 2} : Finset (Fin 3))) := by decide
  have c3 : ¬((0 : Fin 3) ∈ ({1, 2} : Finset (Fin 3))
      ∧ (1 : Fin 3) ∈ ({1, 2} : Finset (Fin 3))) := by decide
  rw [srswor_pair, ite_eq_left c1, ite_eq_right c2, ite_eq_right c3]
  norm_num

/-- Pair inclusion probabilities of SRSWOR `N = 3, n = 2`. -/
theorem srswor_pij_02 : pairInclusionProbability srsworPmf 0 2 = 1 / 3 := by
  have c1 : ¬((0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))
      ∧ (2 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))) := by decide
  have c2 : (0 : Fin 3) ∈ ({0, 2} : Finset (Fin 3))
      ∧ (2 : Fin 3) ∈ ({0, 2} : Finset (Fin 3)) := by decide
  have c3 : ¬((0 : Fin 3) ∈ ({1, 2} : Finset (Fin 3))
      ∧ (2 : Fin 3) ∈ ({1, 2} : Finset (Fin 3))) := by decide
  rw [srswor_pair, ite_eq_right c1, ite_eq_left c2, ite_eq_right c3]
  norm_num

/-- Pair inclusion probabilities of SRSWOR `N = 3, n = 2`. -/
theorem srswor_pij_10 : pairInclusionProbability srsworPmf 1 0 = 1 / 3 := by
  have c1 : (1 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))
      ∧ (0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) := by decide
  have c2 : ¬((1 : Fin 3) ∈ ({0, 2} : Finset (Fin 3))
      ∧ (0 : Fin 3) ∈ ({0, 2} : Finset (Fin 3))) := by decide
  have c3 : ¬((1 : Fin 3) ∈ ({1, 2} : Finset (Fin 3))
      ∧ (0 : Fin 3) ∈ ({1, 2} : Finset (Fin 3))) := by decide
  rw [srswor_pair, ite_eq_left c1, ite_eq_right c2, ite_eq_right c3]
  norm_num

/-- Pair inclusion probabilities of SRSWOR `N = 3, n = 2`. -/
theorem srswor_pij_12 : pairInclusionProbability srsworPmf 1 2 = 1 / 3 := by
  have c1 : ¬((1 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))
      ∧ (2 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))) := by decide
  have c2 : ¬((1 : Fin 3) ∈ ({0, 2} : Finset (Fin 3))
      ∧ (2 : Fin 3) ∈ ({0, 2} : Finset (Fin 3))) := by decide
  have c3 : (1 : Fin 3) ∈ ({1, 2} : Finset (Fin 3))
      ∧ (2 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := by decide
  rw [srswor_pair, ite_eq_right c1, ite_eq_right c2, ite_eq_left c3]
  norm_num

/-- Pair inclusion probabilities of SRSWOR `N = 3, n = 2`. -/
theorem srswor_pij_20 : pairInclusionProbability srsworPmf 2 0 = 1 / 3 := by
  have c1 : ¬((2 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))
      ∧ (0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))) := by decide
  have c2 : (2 : Fin 3) ∈ ({0, 2} : Finset (Fin 3))
      ∧ (0 : Fin 3) ∈ ({0, 2} : Finset (Fin 3)) := by decide
  have c3 : ¬((2 : Fin 3) ∈ ({1, 2} : Finset (Fin 3))
      ∧ (0 : Fin 3) ∈ ({1, 2} : Finset (Fin 3))) := by decide
  rw [srswor_pair, ite_eq_right c1, ite_eq_left c2, ite_eq_right c3]
  norm_num

/-- Pair inclusion probabilities of SRSWOR `N = 3, n = 2`. -/
theorem srswor_pij_21 : pairInclusionProbability srsworPmf 2 1 = 1 / 3 := by
  have c1 : ¬((2 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))
      ∧ (1 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))) := by decide
  have c2 : ¬((2 : Fin 3) ∈ ({0, 2} : Finset (Fin 3))
      ∧ (1 : Fin 3) ∈ ({0, 2} : Finset (Fin 3))) := by decide
  have c3 : (2 : Fin 3) ∈ ({1, 2} : Finset (Fin 3))
      ∧ (1 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := by decide
  rw [srswor_pair, ite_eq_right c1, ite_eq_right c2, ite_eq_left c3]
  norm_num

/-- Outcomes `(0, 3, 6)` for the SRSWOR boundary case. -/
def srsworY : Fin 3 → ℝ :=
  fun i => if i = 0 then 0 else if i = 1 then 3 else 6

private theorem srswor_y0 : srsworY 0 = 0 := by simp [srsworY]

private theorem srswor_y1 : srsworY 1 = 3 := by
  have h : (1 : Fin 3) ≠ 0 := by decide
  simp [srsworY, h]

private theorem srswor_y2 : srsworY 2 = 6 := by
  have h0 : (2 : Fin 3) ≠ 0 := by decide
  have h1 : (2 : Fin 3) ≠ 1 := by decide
  simp [srsworY, h0, h1]

private theorem srswor_ht01 :
    horvitzThompsonTotal srsworPmf srsworY {0, 1} = 9 / 2 := by
  have h01 : (0 : Fin 3) ∉ ({1} : Finset (Fin 3)) := by decide
  unfold horvitzThompsonTotal
  rw [Finset.sum_insert h01, Finset.sum_singleton,
    srswor_y0, srswor_y1, srswor_pi0, srswor_pi1]
  norm_num

private theorem srswor_ht02 :
    horvitzThompsonTotal srsworPmf srsworY {0, 2} = 9 := by
  have h02 : (0 : Fin 3) ∉ ({2} : Finset (Fin 3)) := by decide
  unfold horvitzThompsonTotal
  rw [Finset.sum_insert h02, Finset.sum_singleton,
    srswor_y0, srswor_y2, srswor_pi0, srswor_pi2]
  norm_num

private theorem srswor_ht12 :
    horvitzThompsonTotal srsworPmf srsworY {1, 2} = 27 / 2 := by
  have h12 : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)) := by decide
  unfold horvitzThompsonTotal
  rw [Finset.sum_insert h12, Finset.sum_singleton,
    srswor_y1, srswor_y2, srswor_pi1, srswor_pi2]
  norm_num

private theorem srswor_hT : (∑ i, srsworY i) = 9 := by
  rw [Fin.sum_univ_three, srswor_y0, srswor_y1, srswor_y2]
  norm_num

/-- Non-vacuity: the SRSWOR variance integral equals `27 / 2`. -/
theorem srswor_var :
    ∫ s, (horvitzThompsonTotal srsworPmf srsworY s - ∑ i, srsworY i) ^ 2
      ∂srsworPmf.toMeasure = 27 / 2 := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  rw [sum_univ_fin3, srswor_te, srswor_t0, srswor_t1, srswor_t2,
    srswor_t01, srswor_t02, srswor_t12, srswor_tf,
    srswor_ht01, srswor_ht02, srswor_ht12, srswor_hT]
  norm_num

/-- Non-vacuity: the Yates-Grundy form equals `27 / 2`. -/
theorem srswor_syg : senYatesGrundyVariance srsworPmf srsworY = 27 / 2 := by
  have e0 : Finset.univ.erase (0 : Fin 3) = {1, 2} := by decide
  have e1 : Finset.univ.erase (1 : Fin 3) = {0, 2} := by decide
  have e2 : Finset.univ.erase (2 : Fin 3) = {0, 1} := by decide
  have p12 : (1 : Fin 3) ≠ 2 := by decide
  have p02 : (0 : Fin 3) ≠ 2 := by decide
  have p01 : (0 : Fin 3) ≠ 1 := by decide
  unfold senYatesGrundyVariance
  rw [Fin.sum_univ_three, e0, e1, e2,
    Finset.sum_pair p12, Finset.sum_pair p02, Finset.sum_pair p01,
    srswor_pi0, srswor_pi1, srswor_pi2,
    srswor_pij_01, srswor_pij_02, srswor_pij_10, srswor_pij_12,
    srswor_pij_20, srswor_pij_21, srswor_y0, srswor_y1, srswor_y2]
  norm_num

private theorem srswor_v01 :
    senYatesGrundyEstimate srsworPmf srsworY {0, 1} = 27 / 4 := by
  have h01 : (0 : Fin 3) ∉ ({1} : Finset (Fin 3)) := by decide
  have e01 : ({0, 1} : Finset (Fin 3)).erase 0 = {1} := by decide
  have e10 : ({0, 1} : Finset (Fin 3)).erase 1 = {0} := by decide
  unfold senYatesGrundyEstimate
  rw [Finset.sum_insert h01, Finset.sum_singleton, e01, e10,
    Finset.sum_singleton, Finset.sum_singleton,
    srswor_pi0, srswor_pi1, srswor_pij_01, srswor_pij_10,
    srswor_y0, srswor_y1]
  norm_num

private theorem srswor_v02 :
    senYatesGrundyEstimate srsworPmf srsworY {0, 2} = 27 := by
  have h02 : (0 : Fin 3) ∉ ({2} : Finset (Fin 3)) := by decide
  have e02 : ({0, 2} : Finset (Fin 3)).erase 0 = {2} := by decide
  have e20 : ({0, 2} : Finset (Fin 3)).erase 2 = {0} := by decide
  unfold senYatesGrundyEstimate
  rw [Finset.sum_insert h02, Finset.sum_singleton, e02, e20,
    Finset.sum_singleton, Finset.sum_singleton,
    srswor_pi0, srswor_pi2, srswor_pij_02, srswor_pij_20,
    srswor_y0, srswor_y2]
  norm_num

private theorem srswor_v12 :
    senYatesGrundyEstimate srsworPmf srsworY {1, 2} = 27 / 4 := by
  have h12 : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)) := by decide
  have e12 : ({1, 2} : Finset (Fin 3)).erase 1 = {2} := by decide
  have e21 : ({1, 2} : Finset (Fin 3)).erase 2 = {1} := by decide
  unfold senYatesGrundyEstimate
  rw [Finset.sum_insert h12, Finset.sum_singleton, e12, e21,
    Finset.sum_singleton, Finset.sum_singleton,
    srswor_pi1, srswor_pi2, srswor_pij_12, srswor_pij_21,
    srswor_y1, srswor_y2]
  norm_num

/-- Non-vacuity: the SYG estimator expectation equals `27 / 2`. -/
theorem srswor_est :
    ∫ s, senYatesGrundyEstimate srsworPmf srsworY s ∂srsworPmf.toMeasure
      = 27 / 2 := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  rw [sum_univ_fin3, srswor_te, srswor_t0, srswor_t1, srswor_t2,
    srswor_t01, srswor_t02, srswor_t12, srswor_tf,
    srswor_v01, srswor_v02, srswor_v12]
  norm_num

/-- Bernoulli `(1 / 2)` sampling on `N = 2`: mass `1 / 4` on every subset. -/
noncomputable def bernMass : Finset (Fin 2) → ENNReal :=
  fun _ => ENNReal.ofReal (1 / 4)

/-- The Bernoulli masses sum to one. -/
theorem bernMass_sum : ∑ s, bernMass s = 1 := by
  have m : ∀ s : Finset (Fin 2), bernMass s = ENNReal.ofReal (1 / 4) :=
    fun s => rfl
  rw [sum_univ_fin2, m ∅, m {0}, m {1}, m {0, 1},
    ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- Bernoulli `(1 / 2)` sampling on `N = 2` as a normalized `PMF`. -/
noncomputable def bernPmf : PMF (Finset (Fin 2)) :=
  PMF.ofFintype bernMass bernMass_sum

private theorem bern_t0 : (bernPmf ∅).toReal = (1 / 4 : ℝ) := by
  calc (bernPmf ∅).toReal = (bernMass ∅).toReal := rfl
    _ = (1 / 4 : ℝ) := by
        rw [show bernMass ∅ = ENNReal.ofReal (1 / 4) from rfl,
          ENNReal.toReal_ofReal (by norm_num)]

private theorem bern_t1 : (bernPmf {0}).toReal = (1 / 4 : ℝ) := by
  calc (bernPmf {0}).toReal = (bernMass {0}).toReal := rfl
    _ = (1 / 4 : ℝ) := by
        rw [show bernMass {0} = ENNReal.ofReal (1 / 4) from rfl,
          ENNReal.toReal_ofReal (by norm_num)]

private theorem bern_t2 : (bernPmf {1}).toReal = (1 / 4 : ℝ) := by
  calc (bernPmf {1}).toReal = (bernMass {1}).toReal := rfl
    _ = (1 / 4 : ℝ) := by
        rw [show bernMass {1} = ENNReal.ofReal (1 / 4) from rfl,
          ENNReal.toReal_ofReal (by norm_num)]

private theorem bern_t3 : (bernPmf {0, 1}).toReal = (1 / 4 : ℝ) := by
  calc (bernPmf {0, 1}).toReal = (bernMass {0, 1}).toReal := rfl
    _ = (1 / 4 : ℝ) := by
        rw [show bernMass {0, 1} = ENNReal.ofReal (1 / 4) from rfl,
          ENNReal.toReal_ofReal (by norm_num)]

private theorem bern_pi : ∀ i, inclusionProbability bernPmf i
    = (if i ∈ (∅ : Finset (Fin 2)) then (1 / 4 : ℝ) else 0)
    + ((if i ∈ ({0} : Finset (Fin 2)) then (1 / 4 : ℝ) else 0)
    + ((if i ∈ ({1} : Finset (Fin 2)) then (1 / 4 : ℝ) else 0)
    + (if i ∈ ({0, 1} : Finset (Fin 2)) then (1 / 4 : ℝ) else 0))) := by
  intro i
  unfold inclusionProbability
  rw [sum_univ_fin2, bern_t0, bern_t1, bern_t2, bern_t3]

private theorem bern_pair : ∀ i j, pairInclusionProbability bernPmf i j
    = (if i ∈ (∅ : Finset (Fin 2)) ∧ j ∈ (∅ : Finset (Fin 2))
      then (1 / 4 : ℝ) else 0)
    + ((if i ∈ ({0} : Finset (Fin 2)) ∧ j ∈ ({0} : Finset (Fin 2))
      then (1 / 4 : ℝ) else 0)
    + ((if i ∈ ({1} : Finset (Fin 2)) ∧ j ∈ ({1} : Finset (Fin 2))
      then (1 / 4 : ℝ) else 0)
    + (if i ∈ ({0, 1} : Finset (Fin 2)) ∧ j ∈ ({0, 1} : Finset (Fin 2))
      then (1 / 4 : ℝ) else 0))) := by
  intro i j
  unfold pairInclusionProbability
  rw [sum_univ_fin2, bern_t0, bern_t1, bern_t2, bern_t3]

/-- First inclusion probabilities of Bernoulli `(1 / 2)` sampling. -/
theorem bern_pi0 : inclusionProbability bernPmf 0 = 1 / 2 := by
  have c1 : ¬((0 : Fin 2) ∈ (∅ : Finset (Fin 2))) := by decide
  have c2 : (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) := by decide
  have c3 : ¬((0 : Fin 2) ∈ ({1} : Finset (Fin 2))) := by decide
  have c4 : (0 : Fin 2) ∈ ({0, 1} : Finset (Fin 2)) := by decide
  rw [bern_pi, ite_eq_right c1, ite_eq_left c2, ite_eq_right c3,
    ite_eq_left c4]
  norm_num

/-- First inclusion probabilities of Bernoulli `(1 / 2)` sampling. -/
theorem bern_pi1 : inclusionProbability bernPmf 1 = 1 / 2 := by
  have c1 : ¬((1 : Fin 2) ∈ (∅ : Finset (Fin 2))) := by decide
  have c2 : ¬((1 : Fin 2) ∈ ({0} : Finset (Fin 2))) := by decide
  have c3 : (1 : Fin 2) ∈ ({1} : Finset (Fin 2)) := by decide
  have c4 : (1 : Fin 2) ∈ ({0, 1} : Finset (Fin 2)) := by decide
  rw [bern_pi, ite_eq_right c1, ite_eq_right c2, ite_eq_left c3,
    ite_eq_left c4]
  norm_num

/-- Pair inclusion probabilities of Bernoulli `(1 / 2)` sampling. -/
theorem bern_pij_01 : pairInclusionProbability bernPmf 0 1 = 1 / 4 := by
  have c1 : ¬((0 : Fin 2) ∈ (∅ : Finset (Fin 2))
      ∧ (1 : Fin 2) ∈ (∅ : Finset (Fin 2))) := by decide
  have c2 : ¬((0 : Fin 2) ∈ ({0} : Finset (Fin 2))
      ∧ (1 : Fin 2) ∈ ({0} : Finset (Fin 2))) := by decide
  have c3 : ¬((0 : Fin 2) ∈ ({1} : Finset (Fin 2))
      ∧ (1 : Fin 2) ∈ ({1} : Finset (Fin 2))) := by decide
  have c4 : (0 : Fin 2) ∈ ({0, 1} : Finset (Fin 2))
      ∧ (1 : Fin 2) ∈ ({0, 1} : Finset (Fin 2)) := by decide
  rw [bern_pair, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3,
    ite_eq_left c4]
  norm_num

/-- Pair inclusion probabilities of Bernoulli `(1 / 2)` sampling. -/
theorem bern_pij_10 : pairInclusionProbability bernPmf 1 0 = 1 / 4 := by
  have c1 : ¬((1 : Fin 2) ∈ (∅ : Finset (Fin 2))
      ∧ (0 : Fin 2) ∈ (∅ : Finset (Fin 2))) := by decide
  have c2 : ¬((1 : Fin 2) ∈ ({0} : Finset (Fin 2))
      ∧ (0 : Fin 2) ∈ ({0} : Finset (Fin 2))) := by decide
  have c3 : ¬((1 : Fin 2) ∈ ({1} : Finset (Fin 2))
      ∧ (0 : Fin 2) ∈ ({1} : Finset (Fin 2))) := by decide
  have c4 : (1 : Fin 2) ∈ ({0, 1} : Finset (Fin 2))
      ∧ (0 : Fin 2) ∈ ({0, 1} : Finset (Fin 2)) := by decide
  rw [bern_pair, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3,
    ite_eq_left c4]
  norm_num

/-- Outcomes `(1, 1)` for the Bernoulli counterexample. -/
def bernY : Fin 2 → ℝ := fun _ => 1

private theorem bern_y0 : bernY 0 = 1 := rfl

private theorem bern_y1 : bernY 1 = 1 := rfl

private theorem bern_ht_empty :
    horvitzThompsonTotal bernPmf bernY ∅ = 0 := by
  unfold horvitzThompsonTotal
  rw [Finset.sum_empty]

private theorem bern_ht0 : horvitzThompsonTotal bernPmf bernY {0} = 2 := by
  unfold horvitzThompsonTotal
  rw [Finset.sum_singleton, bern_y0, bern_pi0]
  norm_num

private theorem bern_ht1 : horvitzThompsonTotal bernPmf bernY {1} = 2 := by
  unfold horvitzThompsonTotal
  rw [Finset.sum_singleton, bern_y1, bern_pi1]
  norm_num

private theorem bern_ht01 : horvitzThompsonTotal bernPmf bernY {0, 1} = 4 := by
  have h01 : (0 : Fin 2) ∉ ({1} : Finset (Fin 2)) := by decide
  unfold horvitzThompsonTotal
  rw [Finset.sum_insert h01, Finset.sum_singleton, bern_y0, bern_y1,
    bern_pi0, bern_pi1]
  norm_num

private theorem bern_hT : (∑ i, bernY i) = 2 := by
  rw [Fin.sum_univ_two, bern_y0, bern_y1]
  norm_num

/-- Fixed expected size is not fixed size: the variance is `2`. -/
theorem bern_var :
    ∫ s, (horvitzThompsonTotal bernPmf bernY s - ∑ i, bernY i) ^ 2
      ∂bernPmf.toMeasure = 2 := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  rw [sum_univ_fin2, bern_t0, bern_t1, bern_t2, bern_t3,
    bern_ht_empty, bern_ht0, bern_ht1, bern_ht01, bern_hT]
  norm_num

/-- Fixed expected size is not fixed size: the Yates-Grundy form is `0`. -/
theorem bern_syg : senYatesGrundyVariance bernPmf bernY = 0 := by
  have e0 : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  have e1 : Finset.univ.erase (1 : Fin 2) = {0} := by decide
  unfold senYatesGrundyVariance
  rw [Fin.sum_univ_two, e0, e1, Finset.sum_singleton, Finset.sum_singleton,
    bern_pi0, bern_pi1, bern_pij_01, bern_pij_10, bern_y0, bern_y1]
  norm_num

private theorem sum_univ_fin4 {M : Type*} [AddCommMonoid M]
    (g : Finset (Fin 4) → M) :
    ∑ s, g s = g ∅ + (g {0} + (g {1} + (g {2} + (g {3} + (g {0, 1}
      + (g {0, 2} + (g {0, 3} + (g {1, 2} + (g {1, 3} + (g {2, 3}
      + (g {0, 1, 2} + (g {0, 1, 3} + (g {0, 2, 3}
      + (g {1, 2, 3} + g {0, 1, 2, 3})))))))))))))) := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  have hsub : ∀ s : Finset (Fin 4), s ∈ Finset.powerset {0, 1, 2, 3} := by
    intro s
    rw [Finset.mem_powerset, ← huniv]
    exact Finset.subset_univ s
  have hps : Finset.powerset ({0, 1, 2, 3} : Finset (Fin 4))
      = Finset.univ := Finset.eq_univ_of_forall hsub
  have hlist : Finset.powerset ({0, 1, 2, 3} : Finset (Fin 4))
      = {∅, {0}, {1}, {2}, {3}, {0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3},
        {2, 3}, {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3},
        {0, 1, 2, 3}} := by decide
  calc ∑ s, g s
      = ∑ s ∈ Finset.powerset {0, 1, 2, 3}, g s := by rw [hps]
    _ = g ∅ + (g {0} + (g {1} + (g {2} + (g {3} + (g {0, 1}
      + (g {0, 2} + (g {0, 3} + (g {1, 2} + (g {1, 3} + (g {2, 3}
      + (g {0, 1, 2} + (g {0, 1, 3} + (g {0, 2, 3}
      + (g {1, 2, 3} + g {0, 1, 2, 3})))))))))))))) := by
        rw [hlist, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_singleton]

/-- Systematic design `{0, 2}`, `{1, 3}` with probability `1 / 2` each. -/
noncomputable def sysMass : Finset (Fin 4) → ENNReal :=
  fun s => if s = {0, 2} ∨ s = {1, 3} then ENNReal.ofReal (1 / 2) else 0

private theorem sys_m02 : sysMass {0, 2} = ENNReal.ofReal (1 / 2) := by
  have h : (({0, 2} : Finset (Fin 4)) = {0, 2}
      ∨ ({0, 2} : Finset (Fin 4)) = {1, 3}) := Or.inl rfl
  unfold sysMass
  rw [ite_eq_left h]

private theorem sys_m13 : sysMass {1, 3} = ENNReal.ofReal (1 / 2) := by
  have h : (({1, 3} : Finset (Fin 4)) = {0, 2}
      ∨ ({1, 3} : Finset (Fin 4)) = {1, 3}) := Or.inr rfl
  unfold sysMass
  rw [ite_eq_left h]

private theorem sys_me : sysMass ∅ = 0 := by
  have h : ¬(((∅ : Finset (Fin 4)) = {0, 2}
      ∨ (∅ : Finset (Fin 4)) = {1, 3})) := by decide
  unfold sysMass
  rw [ite_eq_right h]

private theorem sys_m0 : sysMass {0} = 0 := by
  have h : ¬((({0} : Finset (Fin 4)) = {0, 2}
      ∨ ({0} : Finset (Fin 4)) = {1, 3})) := by decide
  unfold sysMass
  rw [ite_eq_right h]

private theorem sys_m1 : sysMass {1} = 0 := by
  have h : ¬((({1} : Finset (Fin 4)) = {0, 2}
      ∨ ({1} : Finset (Fin 4)) = {1, 3})) := by decide
  unfold sysMass
  rw [ite_eq_right h]

private theorem sys_m2 : sysMass {2} = 0 := by
  have h : ¬((({2} : Finset (Fin 4)) = {0, 2}
      ∨ ({2} : Finset (Fin 4)) = {1, 3})) := by decide
  unfold sysMass
  rw [ite_eq_right h]

private theorem sys_m3 : sysMass {3} = 0 := by
  have h : ¬((({3} : Finset (Fin 4)) = {0, 2}
      ∨ ({3} : Finset (Fin 4)) = {1, 3})) := by decide
  unfold sysMass
  rw [ite_eq_right h]

private theorem sys_m01 : sysMass {0, 1} = 0 := by
  have h : ¬((({0, 1} : Finset (Fin 4)) = {0, 2}
      ∨ ({0, 1} : Finset (Fin 4)) = {1, 3})) := by decide
  unfold sysMass
  rw [ite_eq_right h]

private theorem sys_m03 : sysMass {0, 3} = 0 := by
  have h : ¬((({0, 3} : Finset (Fin 4)) = {0, 2}
      ∨ ({0, 3} : Finset (Fin 4)) = {1, 3})) := by decide
  unfold sysMass
  rw [ite_eq_right h]

private theorem sys_m12 : sysMass {1, 2} = 0 := by
  have h : ¬((({1, 2} : Finset (Fin 4)) = {0, 2}
      ∨ ({1, 2} : Finset (Fin 4)) = {1, 3})) := by decide
  unfold sysMass
  rw [ite_eq_right h]

private theorem sys_m23 : sysMass {2, 3} = 0 := by
  have h : ¬((({2, 3} : Finset (Fin 4)) = {0, 2}
      ∨ ({2, 3} : Finset (Fin 4)) = {1, 3})) := by decide
  unfold sysMass
  rw [ite_eq_right h]

private theorem sys_m012 : sysMass {0, 1, 2} = 0 := by
  have h : ¬((({0, 1, 2} : Finset (Fin 4)) = {0, 2}
      ∨ ({0, 1, 2} : Finset (Fin 4)) = {1, 3})) := by decide
  unfold sysMass
  rw [ite_eq_right h]

private theorem sys_m013 : sysMass {0, 1, 3} = 0 := by
  have h : ¬((({0, 1, 3} : Finset (Fin 4)) = {0, 2}
      ∨ ({0, 1, 3} : Finset (Fin 4)) = {1, 3})) := by decide
  unfold sysMass
  rw [ite_eq_right h]

private theorem sys_m023 : sysMass {0, 2, 3} = 0 := by
  have h : ¬((({0, 2, 3} : Finset (Fin 4)) = {0, 2}
      ∨ ({0, 2, 3} : Finset (Fin 4)) = {1, 3})) := by decide
  unfold sysMass
  rw [ite_eq_right h]

private theorem sys_m123 : sysMass {1, 2, 3} = 0 := by
  have h : ¬((({1, 2, 3} : Finset (Fin 4)) = {0, 2}
      ∨ ({1, 2, 3} : Finset (Fin 4)) = {1, 3})) := by decide
  unfold sysMass
  rw [ite_eq_right h]

private theorem sys_mf : sysMass {0, 1, 2, 3} = 0 := by
  have h : ¬((({0, 1, 2, 3} : Finset (Fin 4)) = {0, 2}
      ∨ ({0, 1, 2, 3} : Finset (Fin 4)) = {1, 3})) := by decide
  unfold sysMass
  rw [ite_eq_right h]

/-- The systematic masses sum to one. -/
theorem sysMass_sum : ∑ s, sysMass s = 1 := by
  rw [sum_univ_fin4, sys_me, sys_m0, sys_m1, sys_m2, sys_m3, sys_m01,
    sys_m02, sys_m03, sys_m12, sys_m13, sys_m23, sys_m012, sys_m013,
    sys_m023, sys_m123, sys_mf]
  simp only [zero_add, add_zero]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- Systematic design `{0, 2}`, `{1, 3}` as a normalized `PMF`. -/
noncomputable def sysPmf : PMF (Finset (Fin 4)) :=
  PMF.ofFintype sysMass sysMass_sum

private theorem sys_t02 : (sysPmf {0, 2}).toReal = (1 / 2 : ℝ) := by
  calc (sysPmf {0, 2}).toReal = (sysMass {0, 2}).toReal := rfl
    _ = (1 / 2 : ℝ) := by
        rw [sys_m02, ENNReal.toReal_ofReal (by norm_num)]

private theorem sys_t13 : (sysPmf {1, 3}).toReal = (1 / 2 : ℝ) := by
  calc (sysPmf {1, 3}).toReal = (sysMass {1, 3}).toReal := rfl
    _ = (1 / 2 : ℝ) := by
        rw [sys_m13, ENNReal.toReal_ofReal (by norm_num)]

private theorem sys_te : (sysPmf ∅).toReal = 0 := by
  calc (sysPmf ∅).toReal = (sysMass ∅).toReal := rfl
    _ = 0 := by rw [sys_me, ENNReal.toReal_zero]

private theorem sys_t0 : (sysPmf {0}).toReal = 0 := by
  calc (sysPmf {0}).toReal = (sysMass {0}).toReal := rfl
    _ = 0 := by rw [sys_m0, ENNReal.toReal_zero]

private theorem sys_t1 : (sysPmf {1}).toReal = 0 := by
  calc (sysPmf {1}).toReal = (sysMass {1}).toReal := rfl
    _ = 0 := by rw [sys_m1, ENNReal.toReal_zero]

private theorem sys_t2 : (sysPmf {2}).toReal = 0 := by
  calc (sysPmf {2}).toReal = (sysMass {2}).toReal := rfl
    _ = 0 := by rw [sys_m2, ENNReal.toReal_zero]

private theorem sys_t3 : (sysPmf {3}).toReal = 0 := by
  calc (sysPmf {3}).toReal = (sysMass {3}).toReal := rfl
    _ = 0 := by rw [sys_m3, ENNReal.toReal_zero]

private theorem sys_t01 : (sysPmf {0, 1}).toReal = 0 := by
  calc (sysPmf {0, 1}).toReal = (sysMass {0, 1}).toReal := rfl
    _ = 0 := by rw [sys_m01, ENNReal.toReal_zero]

private theorem sys_t03 : (sysPmf {0, 3}).toReal = 0 := by
  calc (sysPmf {0, 3}).toReal = (sysMass {0, 3}).toReal := rfl
    _ = 0 := by rw [sys_m03, ENNReal.toReal_zero]

private theorem sys_t12 : (sysPmf {1, 2}).toReal = 0 := by
  calc (sysPmf {1, 2}).toReal = (sysMass {1, 2}).toReal := rfl
    _ = 0 := by rw [sys_m12, ENNReal.toReal_zero]

private theorem sys_t23 : (sysPmf {2, 3}).toReal = 0 := by
  calc (sysPmf {2, 3}).toReal = (sysMass {2, 3}).toReal := rfl
    _ = 0 := by rw [sys_m23, ENNReal.toReal_zero]

private theorem sys_t012 : (sysPmf {0, 1, 2}).toReal = 0 := by
  calc (sysPmf {0, 1, 2}).toReal = (sysMass {0, 1, 2}).toReal := rfl
    _ = 0 := by rw [sys_m012, ENNReal.toReal_zero]

private theorem sys_t013 : (sysPmf {0, 1, 3}).toReal = 0 := by
  calc (sysPmf {0, 1, 3}).toReal = (sysMass {0, 1, 3}).toReal := rfl
    _ = 0 := by rw [sys_m013, ENNReal.toReal_zero]

private theorem sys_t023 : (sysPmf {0, 2, 3}).toReal = 0 := by
  calc (sysPmf {0, 2, 3}).toReal = (sysMass {0, 2, 3}).toReal := rfl
    _ = 0 := by rw [sys_m023, ENNReal.toReal_zero]

private theorem sys_t123 : (sysPmf {1, 2, 3}).toReal = 0 := by
  calc (sysPmf {1, 2, 3}).toReal = (sysMass {1, 2, 3}).toReal := rfl
    _ = 0 := by rw [sys_m123, ENNReal.toReal_zero]

private theorem sys_tf : (sysPmf {0, 1, 2, 3}).toReal = 0 := by
  calc (sysPmf {0, 1, 2, 3}).toReal = (sysMass {0, 1, 2, 3}).toReal := rfl
    _ = 0 := by rw [sys_mf, ENNReal.toReal_zero]

private theorem sys_pi : ∀ i, inclusionProbability sysPmf i
    = (if i ∈ ({0, 2} : Finset (Fin 4)) then (1 / 2 : ℝ) else 0)
    + (if i ∈ ({1, 3} : Finset (Fin 4)) then (1 / 2 : ℝ) else 0) := by
  intro i
  unfold inclusionProbability
  rw [sum_univ_fin4, sys_te, sys_t0, sys_t1, sys_t2, sys_t3, sys_t01,
    sys_t02, sys_t03, sys_t12, sys_t13, sys_t23, sys_t012, sys_t013,
    sys_t023, sys_t123, sys_tf]
  simp only [srswor_h00, zero_add, add_zero]

private theorem sys_pair : ∀ i j, pairInclusionProbability sysPmf i j
    = (if i ∈ ({0, 2} : Finset (Fin 4)) ∧ j ∈ ({0, 2} : Finset (Fin 4))
      then (1 / 2 : ℝ) else 0)
    + (if i ∈ ({1, 3} : Finset (Fin 4)) ∧ j ∈ ({1, 3} : Finset (Fin 4))
      then (1 / 2 : ℝ) else 0) := by
  intro i j
  unfold pairInclusionProbability
  rw [sum_univ_fin4, sys_te, sys_t0, sys_t1, sys_t2, sys_t3, sys_t01,
    sys_t02, sys_t03, sys_t12, sys_t13, sys_t23, sys_t012, sys_t013,
    sys_t023, sys_t123, sys_tf]
  simp only [srswor_h00, zero_add, add_zero]

/-- First inclusion probabilities of the systematic design. -/
theorem sys_pi0 : inclusionProbability sysPmf 0 = 1 / 2 := by
  have c1 : (0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4)) := by decide
  have c2 : ¬((0 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) := by decide
  rw [sys_pi, ite_eq_left c1, ite_eq_right c2]
  norm_num

/-- First inclusion probabilities of the systematic design. -/
theorem sys_pi1 : inclusionProbability sysPmf 1 = 1 / 2 := by
  have c1 : ¬((1 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) := by decide
  have c2 : (1 : Fin 4) ∈ ({1, 3} : Finset (Fin 4)) := by decide
  rw [sys_pi, ite_eq_right c1, ite_eq_left c2]
  norm_num

/-- First inclusion probabilities of the systematic design. -/
theorem sys_pi2 : inclusionProbability sysPmf 2 = 1 / 2 := by
  have c1 : (2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4)) := by decide
  have c2 : ¬((2 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) := by decide
  rw [sys_pi, ite_eq_left c1, ite_eq_right c2]
  norm_num

/-- First inclusion probabilities of the systematic design. -/
theorem sys_pi3 : inclusionProbability sysPmf 3 = 1 / 2 := by
  have c1 : ¬((3 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) := by decide
  have c2 : (3 : Fin 4) ∈ ({1, 3} : Finset (Fin 4)) := by decide
  rw [sys_pi, ite_eq_right c1, ite_eq_left c2]
  norm_num

/-- Zero pair inclusion: `π 0 1 = 0`. -/
theorem sys_pij_01 : pairInclusionProbability sysPmf 0 1 = 0 := by
  have c1 : ¬((0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))
      ∧ (1 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) := by decide
  have c2 : ¬((0 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))
      ∧ (1 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) := by decide
  rw [sys_pair, ite_eq_right c1, ite_eq_right c2]
  norm_num

/-- Pair inclusion probabilities of the systematic design. -/
theorem sys_pij_02 : pairInclusionProbability sysPmf 0 2 = 1 / 2 := by
  have c1 : (0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))
      ∧ (2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4)) := by decide
  have c2 : ¬((0 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))
      ∧ (2 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) := by decide
  rw [sys_pair, ite_eq_left c1, ite_eq_right c2]
  norm_num

/-- Pair inclusion probabilities of the systematic design. -/
theorem sys_pij_03 : pairInclusionProbability sysPmf 0 3 = 0 := by
  have c1 : ¬((0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))
      ∧ (3 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) := by decide
  have c2 : ¬((0 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))
      ∧ (3 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) := by decide
  rw [sys_pair, ite_eq_right c1, ite_eq_right c2]
  norm_num

/-- Pair inclusion probabilities of the systematic design. -/
theorem sys_pij_10 : pairInclusionProbability sysPmf 1 0 = 0 := by
  have c1 : ¬((1 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))
      ∧ (0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) := by decide
  have c2 : ¬((1 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))
      ∧ (0 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) := by decide
  rw [sys_pair, ite_eq_right c1, ite_eq_right c2]
  norm_num

/-- Pair inclusion probabilities of the systematic design. -/
theorem sys_pij_12 : pairInclusionProbability sysPmf 1 2 = 0 := by
  have c1 : ¬((1 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))
      ∧ (2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) := by decide
  have c2 : ¬((1 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))
      ∧ (2 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) := by decide
  rw [sys_pair, ite_eq_right c1, ite_eq_right c2]
  norm_num

/-- Pair inclusion probabilities of the systematic design. -/
theorem sys_pij_13 : pairInclusionProbability sysPmf 1 3 = 1 / 2 := by
  have c1 : ¬((1 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))
      ∧ (3 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) := by decide
  have c2 : (1 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))
      ∧ (3 : Fin 4) ∈ ({1, 3} : Finset (Fin 4)) := by decide
  rw [sys_pair, ite_eq_right c1, ite_eq_left c2]
  norm_num

/-- Pair inclusion probabilities of the systematic design. -/
theorem sys_pij_20 : pairInclusionProbability sysPmf 2 0 = 1 / 2 := by
  have c1 : (2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))
      ∧ (0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4)) := by decide
  have c2 : ¬((2 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))
      ∧ (0 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) := by decide
  rw [sys_pair, ite_eq_left c1, ite_eq_right c2]
  norm_num

/-- Pair inclusion probabilities of the systematic design. -/
theorem sys_pij_21 : pairInclusionProbability sysPmf 2 1 = 0 := by
  have c1 : ¬((2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))
      ∧ (1 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) := by decide
  have c2 : ¬((2 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))
      ∧ (1 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) := by decide
  rw [sys_pair, ite_eq_right c1, ite_eq_right c2]
  norm_num

/-- Pair inclusion probabilities of the systematic design. -/
theorem sys_pij_23 : pairInclusionProbability sysPmf 2 3 = 0 := by
  have c1 : ¬((2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))
      ∧ (3 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) := by decide
  have c2 : ¬((2 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))
      ∧ (3 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) := by decide
  rw [sys_pair, ite_eq_right c1, ite_eq_right c2]
  norm_num

/-- Pair inclusion probabilities of the systematic design. -/
theorem sys_pij_30 : pairInclusionProbability sysPmf 3 0 = 0 := by
  have c1 : ¬((3 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))
      ∧ (0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) := by decide
  have c2 : ¬((3 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))
      ∧ (0 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) := by decide
  rw [sys_pair, ite_eq_right c1, ite_eq_right c2]
  norm_num

/-- Pair inclusion probabilities of the systematic design. -/
theorem sys_pij_31 : pairInclusionProbability sysPmf 3 1 = 1 / 2 := by
  have c1 : ¬((3 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))
      ∧ (1 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) := by decide
  have c2 : (3 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))
      ∧ (1 : Fin 4) ∈ ({1, 3} : Finset (Fin 4)) := by decide
  rw [sys_pair, ite_eq_right c1, ite_eq_left c2]
  norm_num

/-- Pair inclusion probabilities of the systematic design. -/
theorem sys_pij_32 : pairInclusionProbability sysPmf 3 2 = 0 := by
  have c1 : ¬((3 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))
      ∧ (2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) := by decide
  have c2 : ¬((3 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))
      ∧ (2 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) := by decide
  rw [sys_pair, ite_eq_right c1, ite_eq_right c2]
  norm_num

/-- Outcomes `(1, 2, 3, 5)` for the systematic design. -/
def sysY : Fin 4 → ℝ :=
  fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else 5

private theorem sys_y0 : sysY 0 = 1 := by simp [sysY]

private theorem sys_y1 : sysY 1 = 2 := by
  have h : (1 : Fin 4) ≠ 0 := by decide
  simp [sysY, h]

private theorem sys_y2 : sysY 2 = 3 := by
  have h0 : (2 : Fin 4) ≠ 0 := by decide
  have h1 : (2 : Fin 4) ≠ 1 := by decide
  simp [sysY, h0, h1]

private theorem sys_y3 : sysY 3 = 5 := by
  have h0 : (3 : Fin 4) ≠ 0 := by decide
  have h1 : (3 : Fin 4) ≠ 1 := by decide
  have h2 : (3 : Fin 4) ≠ 2 := by decide
  simp [sysY, h0, h1, h2]

private theorem sys_ht1 :
    horvitzThompsonTotal sysPmf sysY {0, 2} = 8 := by
  have hp02 : (0 : Fin 4) ≠ 2 := by decide
  unfold horvitzThompsonTotal
  rw [Finset.sum_pair hp02, sys_y0, sys_y2, sys_pi0, sys_pi2]
  norm_num

private theorem sys_ht2 :
    horvitzThompsonTotal sysPmf sysY {1, 3} = 14 := by
  have hp13 : (1 : Fin 4) ≠ 3 := by decide
  unfold horvitzThompsonTotal
  rw [Finset.sum_pair hp13, sys_y1, sys_y3, sys_pi1, sys_pi3]
  norm_num

private theorem sys_hT : (∑ i, sysY i) = 11 := by
  rw [Fin.sum_univ_four, sys_y0, sys_y1, sys_y2, sys_y3]
  norm_num

/-- Fixed-size systematic design: the variance integral equals `9`. -/
theorem sys_var :
    ∫ s, (horvitzThompsonTotal sysPmf sysY s - ∑ i, sysY i) ^ 2
      ∂sysPmf.toMeasure = 9 := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  rw [sum_univ_fin4, sys_te, sys_t0, sys_t1, sys_t2, sys_t3, sys_t01,
    sys_t02, sys_t03, sys_t12, sys_t13, sys_t23, sys_t012, sys_t013,
    sys_t023, sys_t123, sys_tf, sys_ht1, sys_ht2, sys_hT]
  norm_num

/-- Fixed-size systematic design: the Yates-Grundy form equals `9`. -/
theorem sys_syg : senYatesGrundyVariance sysPmf sysY = 9 := by
  have e0 : Finset.univ.erase (0 : Fin 4) = {1, 2, 3} := by decide
  have e1 : Finset.univ.erase (1 : Fin 4) = {0, 2, 3} := by decide
  have e2 : Finset.univ.erase (2 : Fin 4) = {0, 1, 3} := by decide
  have e3 : Finset.univ.erase (3 : Fin 4) = {0, 1, 2} := by decide
  unfold senYatesGrundyVariance
  rw [Fin.sum_univ_four, e0, e1, e2, e3,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    sys_pi0, sys_pi1, sys_pi2, sys_pi3,
    sys_pij_01, sys_pij_02, sys_pij_03, sys_pij_10, sys_pij_12,
    sys_pij_13, sys_pij_20, sys_pij_21, sys_pij_23, sys_pij_30,
    sys_pij_31, sys_pij_32, sys_y0, sys_y1, sys_y2, sys_y3]
  norm_num

/-- Pair-weighted variance estimator restricted to positive pairs. -/
noncomputable def sysEstPos (s : Finset (Fin 4)) : ℝ :=
  (1 / 2) * ∑ i ∈ s, ∑ j ∈ s.erase i,
    (if pairInclusionProbability sysPmf i j ≠ 0
      then ((inclusionProbability sysPmf i * inclusionProbability sysPmf j
      - pairInclusionProbability sysPmf i j)
      / pairInclusionProbability sysPmf i j)
      * ((sysY i / inclusionProbability sysPmf i
      - sysY j / inclusionProbability sysPmf j) ^ 2) else 0)

private theorem sys_v1 : sysEstPos {0, 2} = -8 := by
  have h02 : (0 : Fin 4) ∉ ({2} : Finset (Fin 4)) := by decide
  have e02 : ({0, 2} : Finset (Fin 4)).erase 0 = {2} := by decide
  have e20 : ({0, 2} : Finset (Fin 4)).erase 2 = {0} := by decide
  have hp02 : pairInclusionProbability sysPmf 0 2 ≠ 0 := by
    rw [sys_pij_02]; norm_num
  have hp20 : pairInclusionProbability sysPmf 2 0 ≠ 0 := by
    rw [sys_pij_20]; norm_num
  have hp01 : (0 : Fin 4) ≠ 2 := by decide
  unfold sysEstPos
  rw [Finset.sum_pair hp01, e02, e20, Finset.sum_singleton,
    Finset.sum_singleton, ite_eq_left hp02, ite_eq_left hp20,
    sys_pi0, sys_pi2, sys_pij_02, sys_pij_20, sys_y0, sys_y2]
  norm_num

private theorem sys_v2 : sysEstPos {1, 3} = -18 := by
  have h13 : (1 : Fin 4) ∉ ({3} : Finset (Fin 4)) := by decide
  have e13 : ({1, 3} : Finset (Fin 4)).erase 1 = {3} := by decide
  have e31 : ({1, 3} : Finset (Fin 4)).erase 3 = {1} := by decide
  have hp13 : pairInclusionProbability sysPmf 1 3 ≠ 0 := by
    rw [sys_pij_13]; norm_num
  have hp31 : pairInclusionProbability sysPmf 3 1 ≠ 0 := by
    rw [sys_pij_31]; norm_num
  have hp02 : (1 : Fin 4) ≠ 3 := by decide
  unfold sysEstPos
  rw [Finset.sum_pair hp02, e13, e31, Finset.sum_singleton,
    Finset.sum_singleton, ite_eq_left hp13, ite_eq_left hp31,
    sys_pi1, sys_pi3, sys_pij_13, sys_pij_31, sys_y1, sys_y3]
  norm_num

/-- Zero pair inclusion: the pair-weighted estimator restricted to positive
    pairs has expectation `-13`, while the variance is `9` (`sys_var`), so
    this standard restricted estimator is biased for this design. -/
theorem sys_est :
    ∫ s, sysEstPos s ∂sysPmf.toMeasure = -13 := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  rw [sum_univ_fin4, sys_te, sys_t0, sys_t1, sys_t2, sys_t3, sys_t01,
    sys_t02, sys_t03, sys_t12, sys_t13, sys_t23, sys_t012, sys_t013,
    sys_t023, sys_t123, sys_tf, sys_v1, sys_v2]
  norm_num

end MathlibExt.Probability.Sampling.Test
