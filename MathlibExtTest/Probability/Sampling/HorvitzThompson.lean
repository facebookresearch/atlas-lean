/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Sampling.HorvitzThompson
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad

import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.ENNReal.Real
import Mathlib.Tactic.NormNum.Basic

/-!
# Boundary tests for the Horvitz-Thompson estimator

Unequal design on `Fin 2`, census design, and a never-sampled counterexample.
-/

@[expose] public section

namespace MathlibExt.Probability.Sampling.Test

private theorem sum_fin2_explicit {M : Type*} [AddCommMonoid M]
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
        rw [hlist, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Unequal masses: `1/3` on `{0}`, `2/3` on `{1}`, else `0`. -/
noncomputable def unequalMass : Finset (Fin 2) → ENNReal :=
  fun s => if s = {0} then ENNReal.ofReal (1/3)
    else if s = {1} then ENNReal.ofReal (2/3) else 0

/-- The unequal masses sum to one. -/
theorem unequalMass_sum : ∑ s, unequalMass s = 1 := by
  have he0 : (∅ : Finset (Fin 2)) ≠ {0} := by decide
  have he1 : (∅ : Finset (Fin 2)) ≠ {1} := by decide
  have h10s : ({1} : Finset (Fin 2)) ≠ {0} := by decide
  have hb0 : ({0, 1} : Finset (Fin 2)) ≠ {0} := by decide
  have hb1 : ({0, 1} : Finset (Fin 2)) ≠ {1} := by decide
  have m_empty : unequalMass ∅ = 0 := by simp [unequalMass, he0, he1]
  have m0 : unequalMass {0} = ENNReal.ofReal (1/3) := by simp [unequalMass]
  have m1 : unequalMass {1} = ENNReal.ofReal (2/3) := by simp [unequalMass, h10s]
  have mb : unequalMass {0, 1} = 0 := by simp [unequalMass, hb0, hb1]
  rw [sum_fin2_explicit, m_empty, m0, m1, mb, zero_add, add_zero,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- Unequal design on `Fin 2` as a normalized `PMF`. -/
noncomputable def unequalPmf : PMF (Finset (Fin 2)) :=
  PMF.ofFintype unequalMass unequalMass_sum

/-- First inclusion probability of the unequal design. -/
theorem unequal_pi0 : inclusionProbability unequalPmf 0 = 1/3 := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have m0 : unequalMass {0} = ENNReal.ofReal (1/3) := by simp [unequalMass]
  have t0 : (unequalMass {0}).toReal = (1/3 : ℝ) := by
    rw [m0, ENNReal.toReal_ofReal (by norm_num)]
  have hb0 : ({0, 1} : Finset (Fin 2)) ≠ {0} := by decide
  have hb1 : ({0, 1} : Finset (Fin 2)) ≠ {1} := by decide
  have mb : unequalMass {0, 1} = 0 := by simp [unequalMass, hb0, hb1]
  have tb : (unequalMass {0, 1}).toReal = (0 : ℝ) := by
    rw [mb, ENNReal.toReal_zero]
  have p0 : (unequalPmf {0}).toReal = (1/3 : ℝ) := t0
  have pb : (unequalPmf {0, 1}).toReal = (0 : ℝ) := tb
  have mem0 : (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) := by simp
  have memB : (0 : Fin 2) ∈ ({0, 1} : Finset (Fin 2)) := by simp
  have e_empty : (if (0 : Fin 2) ∈ (∅ : Finset (Fin 2))
      then (unequalPmf ∅).toReal else (0 : ℝ)) = 0 := by simp
  have e0 : (if (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
      then (unequalPmf {0}).toReal else (0 : ℝ)) = 1/3 := by simp [mem0, p0]
  have e1 : (if (0 : Fin 2) ∈ ({1} : Finset (Fin 2))
      then (unequalPmf {1}).toReal else (0 : ℝ)) = 0 := by
    simp [Finset.mem_singleton, h01]
  have eb : (if (0 : Fin 2) ∈ ({0, 1} : Finset (Fin 2))
      then (unequalPmf {0, 1}).toReal else (0 : ℝ)) = 0 := by simp [memB, pb]
  unfold inclusionProbability
  rw [sum_fin2_explicit, e_empty, e0, e1, eb]
  norm_num

/-- Second inclusion probability of the unequal design. -/
theorem unequal_pi1 : inclusionProbability unequalPmf 1 = 2/3 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h10s : ({1} : Finset (Fin 2)) ≠ {0} := by decide
  have m1 : unequalMass {1} = ENNReal.ofReal (2/3) := by simp [unequalMass, h10s]
  have t1 : (unequalMass {1}).toReal = (2/3 : ℝ) := by
    rw [m1, ENNReal.toReal_ofReal (by norm_num)]
  have hb0 : ({0, 1} : Finset (Fin 2)) ≠ {0} := by decide
  have hb1 : ({0, 1} : Finset (Fin 2)) ≠ {1} := by decide
  have mb : unequalMass {0, 1} = 0 := by simp [unequalMass, hb0, hb1]
  have tb : (unequalMass {0, 1}).toReal = (0 : ℝ) := by
    rw [mb, ENNReal.toReal_zero]
  have p1 : (unequalPmf {1}).toReal = (2/3 : ℝ) := t1
  have pb : (unequalPmf {0, 1}).toReal = (0 : ℝ) := tb
  have mem1 : (1 : Fin 2) ∈ ({1} : Finset (Fin 2)) := by simp
  have memB : (1 : Fin 2) ∈ ({0, 1} : Finset (Fin 2)) := by simp
  have e_empty : (if (1 : Fin 2) ∈ (∅ : Finset (Fin 2))
      then (unequalPmf ∅).toReal else (0 : ℝ)) = 0 := by simp
  have e0 : (if (1 : Fin 2) ∈ ({0} : Finset (Fin 2))
      then (unequalPmf {0}).toReal else (0 : ℝ)) = 0 := by
    simp [Finset.mem_singleton, h10]
  have e1 : (if (1 : Fin 2) ∈ ({1} : Finset (Fin 2))
      then (unequalPmf {1}).toReal else (0 : ℝ)) = 2/3 := by simp [mem1, p1]
  have eb : (if (1 : Fin 2) ∈ ({0, 1} : Finset (Fin 2))
      then (unequalPmf {0, 1}).toReal else (0 : ℝ)) = 0 := by simp [memB, pb]
  unfold inclusionProbability
  rw [sum_fin2_explicit, e_empty, e0, e1, eb]
  norm_num

/-- Outcomes with a negative value: `(-2, 5)`. -/
def unequalY : Fin 2 → ℝ := fun i => if i = 0 then -2 else 5

/-- Population total of the unequal-design outcomes. -/
theorem unequal_total : (∑ i, unequalY i) = 3 := by
  simp only [unequalY, Fin.sum_univ_two]
  norm_num

/-- Unbiasedness on the unequal design. -/
theorem unequal_unbiased :
    ∫ s, horvitzThompsonTotal unequalPmf unequalY s ∂unequalPmf.toMeasure
      = ∑ i, unequalY i := by
  apply integral_horvitzThompsonTotal
  rw [Fin.forall_fin_two]
  constructor
  · rw [unequal_pi0]; norm_num
  · rw [unequal_pi1]; norm_num

/-- Mean unbiasedness on the unequal design. -/
theorem unequal_mean_unbiased :
    ∫ s, (horvitzThompsonTotal unequalPmf unequalY s
      / (Fintype.card (Fin 2) : ℝ)) ∂unequalPmf.toMeasure
      = (∑ i, unequalY i) / (Fintype.card (Fin 2) : ℝ) := by
  apply integral_horvitzThompsonTotal_div_card
  · rw [Fin.forall_fin_two]
    constructor
    · rw [unequal_pi0]; norm_num
    · rw [unequal_pi1]; norm_num
  · decide

/-- Expected value on the unequal design equals the total `3`. -/
theorem unequal_expectation :
    ∫ s, horvitzThompsonTotal unequalPmf unequalY s ∂unequalPmf.toMeasure
      = 3 := by
  rw [unequal_unbiased, unequal_total]

/-- Census inclusion probabilities are all one. -/
theorem census_pi {α : Type*} [Fintype α] [DecidableEq α]
    (i : α) : inclusionProbability (PMF.pure Finset.univ) i = 1 := by
  have h0 : ∀ b ∈ (Finset.univ : Finset (Finset α)), b ≠ Finset.univ →
      (if i ∈ b then ((PMF.pure Finset.univ : PMF (Finset α)) b).toReal
        else 0) = 0 := by
    intro b _ hb
    rw [PMF.pure_apply_of_ne _ _ hb]
    simp
  have hsum : (∑ s : Finset α, (if i ∈ s
      then ((PMF.pure Finset.univ : PMF (Finset α)) s).toReal else 0))
      = (if i ∈ Finset.univ
        then ((PMF.pure Finset.univ : PMF (Finset α)) Finset.univ).toReal
        else 0) :=
    Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
  unfold inclusionProbability
  rw [hsum]
  simp

/-- Census estimator at the full sample is the population total. -/
theorem census_total {α : Type*} [Fintype α] [DecidableEq α]
    (y : α → ℝ) :
    horvitzThompsonTotal (PMF.pure Finset.univ) y Finset.univ = ∑ i, y i := by
  unfold horvitzThompsonTotal
  simp only [census_pi, div_one]

/-- Never-sampled design: point mass on `{0}`. -/
noncomputable def neverPmf : PMF (Finset (Fin 2)) := PMF.pure {0}

/-- Outcomes where the missed unit matters: `(0, 1)`. -/
def neverY : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1

/-- The sampled unit has inclusion probability one. -/
theorem never_pi0 : inclusionProbability neverPmf 0 = 1 := by
  have h0 : ∀ b ∈ (Finset.univ : Finset (Finset (Fin 2))), b ≠ {0} →
      (if (0 : Fin 2) ∈ b then (neverPmf b).toReal else 0) = 0 := by
    intro b _ hb
    simp [neverPmf, PMF.pure_apply_of_ne _ _ hb]
  have hsum : (∑ s : Finset (Fin 2),
      (if (0 : Fin 2) ∈ s then (neverPmf s).toReal else 0))
      = (if (0 : Fin 2) ∈ ({0} : Finset (Fin 2))
        then (neverPmf {0}).toReal else 0) :=
    Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
  have mem0 : (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) := by simp
  have pself : (neverPmf {0}).toReal = (1 : ℝ) := by
    simp [neverPmf]
  unfold inclusionProbability
  rw [hsum]
  simp [mem0, pself]

/-- The never-sampled unit has inclusion probability zero. -/
theorem never_pi1 : inclusionProbability neverPmf 1 = 0 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hterm : ∀ s : Finset (Fin 2),
      (if (1 : Fin 2) ∈ s then (neverPmf s).toReal else 0) = 0 := by
    intro s
    by_cases h1 : (1 : Fin 2) ∈ s
    · have hs : s ≠ {0} := by
        intro hcon
        subst hcon
        rw [Finset.mem_singleton] at h1
        exact h10 h1
      simp [h1, neverPmf, PMF.pure_apply_of_ne _ _ hs]
    · simp [h1]
  unfold inclusionProbability
  simp [hterm]

/-- With a never-sampled unit, the estimator misses the total. -/
theorem never_not_unbiased :
    ∫ s, horvitzThompsonTotal neverPmf neverY s ∂neverPmf.toMeasure
      ≠ ∑ i, neverY i := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have y0 : neverY 0 = 0 := by simp [neverY]
  have y1 : neverY 1 = 1 := by simp [neverY, h10]
  have rhs : (∑ i, neverY i) = 1 := by
    rw [Fin.sum_univ_two, y0, y1, zero_add]
  have hint : (∫ s, horvitzThompsonTotal neverPmf neverY s
      ∂neverPmf.toMeasure) = 0 := by
    rw [PMF.integral_eq_sum]
    simp only [smul_eq_mul]
    have h0 : ∀ b ∈ (Finset.univ : Finset (Finset (Fin 2))), b ≠ {0} →
        (neverPmf b).toReal * horvitzThompsonTotal neverPmf neverY b = 0 := by
      intro b _ hb
      simp [neverPmf, PMF.pure_apply_of_ne _ _ hb]
    have hsum : (∑ s : Finset (Fin 2), (neverPmf s).toReal
        * horvitzThompsonTotal neverPmf neverY s)
        = (neverPmf {0}).toReal * horvitzThompsonTotal neverPmf neverY {0} :=
      Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0
    have pself : (neverPmf {0}).toReal = (1 : ℝ) := by
      simp [neverPmf]
    have ht0 : horvitzThompsonTotal neverPmf neverY {0} = 0 := by
      unfold horvitzThompsonTotal
      rw [Finset.sum_singleton, y0, never_pi0, div_one]
    rw [hsum, pself, ht0, mul_zero]
  rw [hint, rhs]
  norm_num

end MathlibExt.Probability.Sampling.Test
