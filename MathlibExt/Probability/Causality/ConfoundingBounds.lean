/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FinCases

/-!
# Finite categorical confounding bounds

The model describes two exposure arms within one stratum of measured
covariates. The standardized risks are evaluations of the risk kernels
against the marginal confounder law.

P. Ding and T. J. VanderWeele, *Sensitivity analysis without assumptions*,
Epidemiology 27 (2016), 368–377, Result 1 and eAppendix §2.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality

open scoped BigOperators

/-- A binary exposure and outcome with `n + 1` confounder levels.
`false` is the unexposed arm. Risks are kernel values on every level,
including levels with zero conditional mass in the exposed arm. -/
structure FiniteRiskModel (n : ℕ) where
  exposureProb : ℝ
  exposureProb_mem : exposureProb ∈ Set.Ioo 0 1
  confounderLaw : Bool → Convexity.StdSimplex ℝ (Fin (n + 1))
  control_mass_pos : ∀ u, 0 < (confounderLaw false).weights u
  risk : Bool → Fin (n + 1) → ℝ
  risk_mem : ∀ e u, risk e u ∈ Set.Ioc 0 1

namespace FiniteRiskModel

/-- Exposure-arm probability. -/
noncomputable def armProb {n : ℕ} (m : FiniteRiskModel n) (e : Bool) : ℝ :=
  if e then m.exposureProb else 1 - m.exposureProb

/-- Conditional confounder mass in one arm. -/
noncomputable def mass {n : ℕ} (m : FiniteRiskModel n) (e : Bool) (u : Fin (n + 1)) : ℝ :=
  (m.confounderLaw e).weights u

/-- Marginal confounder mass in the population. -/
noncomputable def marginalMass {n : ℕ} (m : FiniteRiskModel n) (u : Fin (n + 1)) : ℝ :=
  m.exposureProb * m.mass true u + (1 - m.exposureProb) * m.mass false u

/-- Atom mass of the joint law of exposure, confounder and binary outcome. -/
noncomputable def jointMass {n : ℕ} (m : FiniteRiskModel n) (e : Bool) (u : Fin (n + 1))
    (d : Bool) : ℝ :=
  m.armProb e * m.mass e u * (if d then m.risk e u else 1 - m.risk e u)

/-- The two outcome atoms recover the exposure-confounder atom. -/
theorem jointMass_sum_outcome {n : ℕ} (m : FiniteRiskModel n) (e : Bool)
    (u : Fin (n + 1)) :
    m.jointMass e u true + m.jointMass e u false = m.armProb e * m.mass e u := by
  simp [jointMass, mul_sub]

/-- Each joint atom has nonnegative mass. -/
theorem jointMass_nonneg {n : ℕ} (m : FiniteRiskModel n) (e : Bool)
    (u : Fin (n + 1)) (d : Bool) : 0 ≤ m.jointMass e u d := by
  have hp : 0 ≤ m.armProb e := by
    cases e
    · exact sub_nonneg.mpr m.exposureProb_mem.2.le
    · exact m.exposureProb_mem.1.le
  have hmass : 0 ≤ m.mass e u := (m.confounderLaw e).weights_nonneg u
  have hd : 0 ≤ (if d then m.risk e u else 1 - m.risk e u) := by
    cases d
    · exact sub_nonneg.mpr (m.risk_mem e u).2
    · exact (m.risk_mem e u).1.le
  exact mul_nonneg (mul_nonneg hp hmass) hd

/-- The joint law is normalized. -/
theorem jointMass_sum {n : ℕ} (m : FiniteRiskModel n) :
    ∑ e, ∑ u, ∑ d, m.jointMass e u d = 1 := by
  simp only [Fintype.sum_bool, jointMass_sum_outcome, ← Finset.mul_sum]
  have hsum (e : Bool) : ∑ u, m.mass e u = 1 := (m.confounderLaw e).total_of_fintype
  simp only [hsum, mul_one, armProb, Bool.false_eq_true, ↓reduceIte]
  rw [add_comm, sub_add_cancel]

/-- Marginal confounder masses are strictly positive. -/
theorem marginalMass_pos {n : ℕ} (m : FiniteRiskModel n) (u : Fin (n + 1)) :
    0 < m.marginalMass u :=
  add_pos_of_nonneg_of_pos
    (mul_nonneg m.exposureProb_mem.1.le ((m.confounderLaw true).weights_nonneg u))
    (mul_pos (sub_pos.mpr m.exposureProb_mem.2) (m.control_mass_pos u))

/-- Mean observed risk in an exposure arm. -/
noncomputable def observedRisk {n : ℕ} (m : FiniteRiskModel n) (e : Bool) : ℝ :=
  ∑ u, m.risk e u * m.mass e u

/-- The observed risk in each arm is positive. -/
theorem observedRisk_pos {n : ℕ} (m : FiniteRiskModel n) (e : Bool) :
    0 < m.observedRisk e := by
  apply Finset.sum_pos'
  · exact fun u _ => mul_nonneg (m.risk_mem e u).1.le ((m.confounderLaw e).weights_nonneg u)
  · have hp : ∃ u, 0 < m.mass e u := by
      by_contra! h
      have hz (u : Fin (n + 1)) : (m.confounderLaw e).weights u = 0 :=
        le_antisymm (h u) ((m.confounderLaw e).weights_nonneg u)
      have hn := (m.confounderLaw e).total_of_fintype
      simp [hz] at hn
    obtain ⟨u, hu⟩ := hp
    exact ⟨u, Finset.mem_univ _, mul_pos (m.risk_mem e u).1 hu⟩

/-- The observed risk ratio. -/
noncomputable def observedRR {n : ℕ} (m : FiniteRiskModel n) : ℝ :=
  m.observedRisk true / m.observedRisk false

/-- Arm-specific risk standardized to the population confounder law. -/
noncomputable def standardizedRisk {n : ℕ} (m : FiniteRiskModel n) (e : Bool) : ℝ :=
  ∑ u, m.risk e u * m.marginalMass u

/-- Each population-standardized risk is positive. -/
theorem standardizedRisk_pos {n : ℕ} (m : FiniteRiskModel n) (e : Bool) :
    0 < m.standardizedRisk e :=
  Finset.sum_pos (fun u _ => mul_pos (m.risk_mem e u).1 (m.marginalMass_pos u))
    Finset.univ_nonempty

/-- The risk ratio standardized to the population confounder law. -/
noncomputable def standardizedRR {n : ℕ} (m : FiniteRiskModel n) : ℝ :=
  m.standardizedRisk true / m.standardizedRisk false

/-- The risk ratio standardized to the confounder law of arm `e`. -/
noncomputable def armStandardizedRR {n : ℕ} (m : FiniteRiskModel n) (e : Bool) : ℝ :=
  (∑ u, m.risk true u * m.mass e u) / ∑ u, m.risk false u * m.mass e u

/-- `RR_EU`, the maximum exposed-to-unexposed confounder mass ratio. -/
noncomputable def exposureConfounderRR {n : ℕ} (m : FiniteRiskModel n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun u => m.mass true u / m.mass false u)

/-- `RR_UD` within one arm, with extrema over the marginal support. -/
noncomputable def armConfounderOutcomeRR {n : ℕ} (m : FiniteRiskModel n) (e : Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (m.risk e) /
    Finset.univ.inf' Finset.univ_nonempty (m.risk e)

/-- `RR_UD`, the larger of the two within-arm ratios. -/
noncomputable def confounderOutcomeRR {n : ℕ} (m : FiniteRiskModel n) : ℝ :=
  max (m.armConfounderOutcomeRR true) (m.armConfounderOutcomeRR false)

/-- Observed divided by population-standardized risk ratio. -/
noncomputable def confoundingRR {n : ℕ} (m : FiniteRiskModel n) : ℝ :=
  m.observedRR / m.standardizedRR

/-- Observed divided by the risk ratio standardized to arm `e`. -/
noncomputable def armConfoundingRR {n : ℕ} (m : FiniteRiskModel n) (e : Bool) : ℝ :=
  m.observedRR / m.armStandardizedRR e

private theorem mass_sum {n : ℕ} (m : FiniteRiskModel n) (e : Bool) :
    ∑ u, m.mass e u = 1 := (m.confounderLaw e).total_of_fintype

private theorem crossRisk_pos {n : ℕ} (m : FiniteRiskModel n) (e a : Bool) :
    0 < ∑ u, m.risk e u * m.mass a u := by
  apply Finset.sum_pos'
  · exact fun u _ => mul_nonneg (m.risk_mem e u).1.le
      ((m.confounderLaw a).weights_nonneg u)
  · have hp : ∃ u, 0 < m.mass a u := by
      by_contra! h
      have hz (u : Fin (n + 1)) : m.mass a u = 0 :=
        le_antisymm (h u) ((m.confounderLaw a).weights_nonneg u)
      have hn := mass_sum m a
      simp [hz] at hn
    obtain ⟨u, hu⟩ := hp
    exact ⟨u, Finset.mem_univ _, mul_pos (m.risk_mem e u).1 hu⟩

theorem observedRR_pos {n : ℕ} (m : FiniteRiskModel n) : 0 < m.observedRR :=
  div_pos (m.observedRisk_pos true) (m.observedRisk_pos false)

theorem standardizedRR_pos {n : ℕ} (m : FiniteRiskModel n) :
    0 < m.standardizedRR :=
  div_pos (m.standardizedRisk_pos true) (m.standardizedRisk_pos false)

private theorem armStandardizedRR_pos {n : ℕ} (m : FiniteRiskModel n) (e : Bool) :
    0 < m.armStandardizedRR e :=
  div_pos (crossRisk_pos m true e) (crossRisk_pos m false e)

private theorem standardizedRisk_eq {n : ℕ} (m : FiniteRiskModel n) (e : Bool) :
    m.standardizedRisk e = m.exposureProb * (∑ u, m.risk e u * m.mass true u) +
      (1 - m.exposureProb) * (∑ u, m.risk e u * m.mass false u) := by
  simp only [standardizedRisk, marginalMass, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

private theorem mass_le {n : ℕ} (m : FiniteRiskModel n) (u : Fin (n + 1)) :
    m.mass true u ≤ m.exposureConfounderRR * m.mass false u := by
  apply (div_le_iff₀ (m.control_mass_pos u)).mp
  exact Finset.le_sup' (fun v => m.mass true v / m.mass false v) (Finset.mem_univ u)

theorem exposureConfounderRR_one_le {n : ℕ} (m : FiniteRiskModel n) :
    1 ≤ m.exposureConfounderRR := by
  have h := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => mass_le m u)
  simpa only [← Finset.mul_sum, mass_sum, mul_one] using h

private theorem riskMin_pos {n : ℕ} (m : FiniteRiskModel n) (e : Bool) :
    0 < Finset.univ.inf' Finset.univ_nonempty (m.risk e) :=
  Finset.inf'_mem (Set.Ioi 0) (fun _ ha _ hb => lt_min ha hb)
    Finset.univ Finset.univ_nonempty (m.risk e) (fun u _ => (m.risk_mem e u).1)

theorem armConfounderOutcomeRR_one_le {n : ℕ} (m : FiniteRiskModel n) (e : Bool) :
    1 ≤ m.armConfounderOutcomeRR e := by
  apply (le_div_iff₀ (riskMin_pos m e)).mpr
  simpa only [one_mul] using (Finset.inf'_le (m.risk e) (Finset.mem_univ (0 : Fin (n + 1)))).trans
    (Finset.le_sup' (m.risk e) (Finset.mem_univ (0 : Fin (n + 1))))

theorem confounderOutcomeRR_one_le {n : ℕ} (m : FiniteRiskModel n) :
    1 ≤ m.confounderOutcomeRR :=
  (armConfounderOutcomeRR_one_le m true).trans (le_max_left _ _)

/-- In an arm-standardized confounding ratio, the other arm's risk kernel
is evaluated under the two confounder laws. -/
theorem armConfoundingRR_eq_ratio {n : ℕ} (m : FiniteRiskModel n) (e : Bool) :
    m.armConfoundingRR e =
      (∑ u, m.risk (!e) u * m.mass true u) / ∑ u, m.risk (!e) u * m.mass false u := by
  have ht := (m.observedRisk_pos true).ne'
  have hf := (m.observedRisk_pos false).ne'
  have hc := (crossRisk_pos m true false).ne'
  have hd := (crossRisk_pos m false true).ne'
  cases e <;>
    simp only [armConfoundingRR, observedRR, armStandardizedRR, Bool.not_false,
      Bool.not_true] <;>
    unfold observedRisk at ht hf ⊢ <;> field_simp

/-- The contribution of the exposed arm to the standardized control risk. -/
noncomputable def standardizationWeight {n : ℕ} (m : FiniteRiskModel n) : ℝ :=
  m.exposureProb * (∑ u, m.risk false u * m.mass true u) / m.standardizedRisk false

/-- The population-standardized RR is a weighted mean of the two arm RRs. -/
theorem standardizedRR_eq_weighted {n : ℕ} (m : FiniteRiskModel n) :
    m.standardizedRR = m.standardizationWeight * m.armStandardizedRR true +
      (1 - m.standardizationWeight) * m.armStandardizedRR false := by
  have hc := (crossRisk_pos m false true).ne'
  have hd := (crossRisk_pos m false false).ne'
  have hs := (m.standardizedRisk_pos false).ne'
  have he := standardizedRisk_eq m false
  unfold standardizedRR standardizationWeight armStandardizedRR
  rw [standardizedRisk_eq m true]
  field_simp
  rw [he]
  ring

/-- The reciprocal confounding RR has the corresponding weighted decomposition. -/
theorem inv_confoundingRR_eq_weighted {n : ℕ} (m : FiniteRiskModel n) :
    1 / m.confoundingRR = m.standardizationWeight / m.armConfoundingRR true +
      (1 - m.standardizationWeight) / m.armConfoundingRR false := by
  have ho := (observedRR_pos m).ne'
  have hs := (standardizedRR_pos m).ne'
  have ht := (armStandardizedRR_pos m true).ne'
  have hf := (armStandardizedRR_pos m false).ne'
  have hw := standardizedRR_eq_weighted m
  unfold confoundingRR armConfoundingRR
  field_simp
  nlinarith [hw]

/-- The decomposition weights are in the unit interval. -/
theorem standardizationWeight_mem {n : ℕ} (m : FiniteRiskModel n) :
    m.standardizationWeight ∈ Set.Icc 0 1 := by
  have hp := m.exposureProb_mem.1.le
  have hc := (crossRisk_pos m false true).le
  have hs := m.standardizedRisk_pos false
  constructor
  · exact div_nonneg (mul_nonneg hp hc) hs.le
  · apply (div_le_one hs).mpr
    rw [standardizedRisk_eq]
    have h := mul_nonneg (sub_nonneg.mpr m.exposureProb_mem.2.le)
      (crossRisk_pos m false false).le
    linarith

end FiniteRiskModel

/-- The Ding–VanderWeele bounding factor, used for `x, y ≥ 1`. -/
noncomputable def confoundingBoundingFactor (x y : ℝ) : ℝ :=
  x * y / (x + y - 1)

theorem confoundingBoundingFactor_pos {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    0 < confoundingBoundingFactor x y := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hd : 0 < x + y - 1 := by linarith
  exact div_pos (mul_pos hx0 hy0) hd

theorem confoundingBoundingFactor_mono_right {x a b : ℝ}
    (hx : 1 ≤ x) (ha : 1 ≤ a) (hab : a ≤ b) :
    confoundingBoundingFactor x a ≤ confoundingBoundingFactor x b := by
  have hda : 0 < x + a - 1 := by linarith
  have hdb : 0 < x + b - 1 := by linarith
  apply (div_le_div_iff₀ hda hdb).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hab)
    (mul_nonneg (by linarith : 0 ≤ x) (sub_nonneg.mpr hx))]

/-- With a unit exposure-confounder parameter, the bounding factor is one. -/
theorem confoundingBoundingFactor_one_left {y : ℝ} (hy : 1 ≤ y) :
    confoundingBoundingFactor 1 y = 1 := by
  simp [confoundingBoundingFactor, ne_of_gt (zero_lt_one.trans_le hy)]

/-- With a unit confounder-outcome parameter, the bounding factor is one. -/
theorem confoundingBoundingFactor_one_right {x : ℝ} (hx : 1 ≤ x) :
    confoundingBoundingFactor x 1 = 1 := by
  simp [confoundingBoundingFactor, ne_of_gt (zero_lt_one.trans_le hx)]

/-- The bounding factor is strictly increasing in its first argument above one. -/
theorem confoundingBoundingFactor_strictMonoOn_left {y : ℝ} (hy : 1 < y) :
    StrictMonoOn (fun x => confoundingBoundingFactor x y) (Set.Ioi 1) := by
  intro a ha b hb hab
  change 1 < a at ha
  change 1 < b at hb
  have hda : 0 < a + y - 1 := by linarith [ha]
  have hdb : 0 < b + y - 1 := by linarith [hb]
  unfold confoundingBoundingFactor
  apply (div_lt_div_iff₀ hda hdb).mpr
  nlinarith [mul_pos (sub_pos.mpr hab) (mul_pos (by linarith : 0 < y)
    (sub_pos.mpr hy))]

/-- The bounding factor is strictly increasing in its second argument above one. -/
theorem confoundingBoundingFactor_strictMonoOn_right {x : ℝ} (hx : 1 < x) :
    StrictMonoOn (confoundingBoundingFactor x) (Set.Ioi 1) := by
  intro a ha b hb hab
  change 1 < a at ha
  change 1 < b at hb
  have hda : 0 < x + a - 1 := by linarith [ha]
  have hdb : 0 < x + b - 1 := by linarith [hb]
  unfold confoundingBoundingFactor
  apply (div_lt_div_iff₀ hda hdb).mpr
  nlinarith [mul_pos (sub_pos.mpr hab) (mul_pos (by linarith : 0 < x)
    (sub_pos.mpr hx))]

/-- The bounding factor does not exceed the weaker association. -/
theorem confoundingBoundingFactor_le_min {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    confoundingBoundingFactor x y ≤ min x y := by
  have hd : 0 < x + y - 1 := by linarith
  unfold confoundingBoundingFactor
  apply le_min
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ x) (by linarith : 0 ≤ x - 1)]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ y) (by linarith : 0 ≤ y - 1)]

/-- For two finite parameters above one the low threshold is strict. -/
theorem confoundingBoundingFactor_lt_min {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
    confoundingBoundingFactor x y < min x y := by
  have hd : 0 < x + y - 1 := by linarith
  unfold confoundingBoundingFactor
  apply lt_min
  · apply (div_lt_iff₀ hd).mpr
    nlinarith [mul_pos (by linarith : 0 < x) (by linarith : 0 < x - 1)]
  · apply (div_lt_iff₀ hd).mpr
    nlinarith [mul_pos (by linarith : 0 < y) (by linarith : 0 < y - 1)]

namespace FiniteRiskModel

/-- Arm-standardized confounding bound. Standardizing to arm `e` uses
the within-arm confounder-outcome parameter from the other arm. -/
theorem armConfoundingRR_le_boundingFactor {n : ℕ} (m : FiniteRiskModel n)
    (e : Bool) :
    m.armConfoundingRR e ≤
      confoundingBoundingFactor m.exposureConfounderRR (m.armConfounderOutcomeRR (!e)) := by
  rw [armConfoundingRR_eq_ratio]
  let x := m.exposureConfounderRR
  let b := Finset.univ.inf' Finset.univ_nonempty (m.risk (!e))
  let B := Finset.univ.sup' Finset.univ_nonempty (m.risk (!e))
  let t := ∑ u, m.risk (!e) u * m.mass true u
  let c := ∑ u, m.risk (!e) u * m.mass false u
  have hx : 1 ≤ x := exposureConfounderRR_one_le m
  have hb : 0 < b := riskMin_pos m (!e)
  have hc : 0 < c := crossRisk_pos m (!e) false
  have hB : b ≤ B := by
    exact (Finset.inf'_le (m.risk (!e)) (Finset.mem_univ (0 : Fin (n + 1)))).trans
      (Finset.le_sup' (m.risk (!e)) (Finset.mem_univ (0 : Fin (n + 1))))
  have htB : t ≤ B := by
    have h := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_right (Finset.le_sup' (m.risk (!e)) (Finset.mem_univ u))
        ((m.confounderLaw true).weights_nonneg u))
    change (∑ u, m.risk (!e) u * m.mass true u) ≤ ∑ u, B * m.mass true u at h
    simpa only [← Finset.mul_sum, mass_sum, mul_one] using h
  have hdiff : b * (x - 1) ≤ x * c - t := by
    have h := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_right (Finset.inf'_le (m.risk (!e)) (Finset.mem_univ u))
        (sub_nonneg.mpr (mass_le m u)))
    change (∑ u, b * (x * m.mass false u - m.mass true u)) ≤
      ∑ u, m.risk (!e) u * (x * m.mass false u - m.mass true u) at h
    have heq : (∑ u, m.risk (!e) u * (x * m.mass false u - m.mass true u)) =
        x * c - t := by
      calc
        _ = ∑ u, (x * (m.risk (!e) u * m.mass false u) -
            m.risk (!e) u * m.mass true u) := by
          apply Finset.sum_congr rfl
          intro u _
          ring
        _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [heq] at h
    simpa only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, mass_sum,
      mul_one, sub_mul, mul_assoc] using h
  have hden : 0 < x + B / b - 1 := by
    have hratio : 1 ≤ B / b := (le_div_iff₀ hb).mpr (by simpa only [one_mul] using hB)
    linarith
  change t / c ≤ x * (B / b) / (x + B / b - 1)
  apply (div_le_div_iff₀ hc hden).mpr
  apply (mul_le_mul_iff_right₀ hb).mp
  field_simp
  nlinarith [mul_nonneg (by linarith : 0 ≤ B) (sub_nonneg.mpr hdiff),
    mul_nonneg (sub_nonneg.mpr htB) (mul_nonneg hb.le (sub_nonneg.mpr hx))]

/-- Bounding by the larger within-arm outcome parameter gives a common factor. -/
theorem armBoundingFactor_le_boundingFactor {n : ℕ} (m : FiniteRiskModel n)
    (e : Bool) :
    confoundingBoundingFactor m.exposureConfounderRR (m.armConfounderOutcomeRR e) ≤
      confoundingBoundingFactor m.exposureConfounderRR m.confounderOutcomeRR := by
  apply confoundingBoundingFactor_mono_right (exposureConfounderRR_one_le m)
    (armConfounderOutcomeRR_one_le m e)
  cases e
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- Ding–VanderWeele Result 1 for finite categorical confounding. -/
theorem confoundingRR_le_boundingFactor {n : ℕ} (m : FiniteRiskModel n) :
    m.observedRR / m.standardizedRR ≤
      confoundingBoundingFactor m.exposureConfounderRR m.confounderOutcomeRR := by
  let F := confoundingBoundingFactor m.exposureConfounderRR m.confounderOutcomeRR
  have ht := (armConfoundingRR_le_boundingFactor m true).trans
    (armBoundingFactor_le_boundingFactor m false)
  have hf := (armConfoundingRR_le_boundingFactor m false).trans
    (armBoundingFactor_le_boundingFactor m true)
  have ht' : m.observedRR ≤ F * m.armStandardizedRR true :=
    (div_le_iff₀ (armStandardizedRR_pos m true)).mp ht
  have hf' : m.observedRR ≤ F * m.armStandardizedRR false :=
    (div_le_iff₀ (armStandardizedRR_pos m false)).mp hf
  have hw := standardizationWeight_mem m
  apply (div_le_iff₀ (standardizedRR_pos m)).mpr
  rw [standardizedRR_eq_weighted]
  have h1 := mul_le_mul_of_nonneg_left ht' hw.1
  have h2 := mul_le_mul_of_nonneg_left hf' (sub_nonneg.mpr hw.2)
  dsimp [F] at h1 h2
  nlinarith [h1, h2]

/-- Result 1 in the form of a lower bound on the standardized risk ratio. -/
theorem observedRR_div_boundingFactor_le_standardizedRR {n : ℕ} (m : FiniteRiskModel n) :
    m.observedRR / confoundingBoundingFactor m.exposureConfounderRR m.confounderOutcomeRR ≤
      m.standardizedRR := by
  have hF := confoundingBoundingFactor_pos (exposureConfounderRR_one_le m)
    (confounderOutcomeRR_one_le m)
  apply (div_le_iff₀ hF).mpr
  have h := (div_le_iff₀ (standardizedRR_pos m)).mp
    (confoundingRR_le_boundingFactor m)
  simpa only [mul_comm] using h

/-- Required outcome-confounder strength for the indicated reduction in risk ratio. -/
theorem required_confounderOutcomeRR {n : ℕ} (m : FiniteRiskModel n)
    (h : m.observedRR < m.exposureConfounderRR * m.standardizedRR) :
    (m.exposureConfounderRR * m.observedRR - m.observedRR) /
      (m.exposureConfounderRR * m.standardizedRR - m.observedRR) ≤
        m.confounderOutcomeRR := by
  have hd : 0 < m.exposureConfounderRR + m.confounderOutcomeRR - 1 := by
    linarith [exposureConfounderRR_one_le m, confounderOutcomeRR_one_le m]
  have hb := (div_le_iff₀ (standardizedRR_pos m)).mp
    (confoundingRR_le_boundingFactor m)
  unfold confoundingBoundingFactor at hb
  rw [div_mul_eq_mul_div] at hb
  have hb' := (le_div_iff₀ hd).mp hb
  apply (div_le_iff₀ (sub_pos.mpr h)).mpr
  nlinarith [hb']

/-- The generalized Cornfield low threshold. -/
theorem cornfield_low_threshold {n : ℕ} (m : FiniteRiskModel n) :
    m.confoundingRR ≤ min m.exposureConfounderRR m.confounderOutcomeRR := by
  exact (confoundingRR_le_boundingFactor m).trans
    (confoundingBoundingFactor_le_min (exposureConfounderRR_one_le m)
      (confounderOutcomeRR_one_le m))

/-- Cornfield et al. (1959), Appendix A. Level 1 is the higher-risk agent.
Exposure leaves the two level-specific risks unchanged. -/
theorem cornfield_binary {m : FiniteRiskModel 1}
    (hRisk : m.risk true = m.risk false) (hAgent : m.risk false 0 < m.risk false 1)
    (hObs : 1 < m.observedRR) :
    m.observedRR < m.mass true 1 / m.mass false 1 := by
  have hsT := mass_sum m true
  have hsF := mass_sum m false
  rw [Fin.sum_univ_two] at hsT hsF
  have hT : m.mass true 0 = 1 - m.mass true 1 := by linarith
  have hF : m.mass false 0 = 1 - m.mass false 1 := by linarith
  have hmean := (one_lt_div (m.observedRisk_pos false)).mp hObs
  unfold observedRisk at hmean
  rw [hRisk, Fin.sum_univ_two, Fin.sum_univ_two, hT, hF] at hmean
  have ht : m.mass false 1 < m.mass true 1 := by
    by_contra! ht
    have hd := mul_nonneg (sub_nonneg.mpr hAgent.le) (sub_nonneg.mpr ht)
    nlinarith [hd]
  unfold observedRR
  have hc : 0 < m.mass false 1 := m.control_mass_pos 1
  apply (div_lt_div_iff₀ (m.observedRisk_pos false) hc).mpr
  unfold observedRisk
  rw [hRisk, Fin.sum_univ_two, Fin.sum_univ_two, hT, hF]
  nlinarith [mul_pos (m.risk_mem false 0).1 (sub_pos.mpr ht)]

/-- The preventive-exposure bound uses the opposite exposure orientation.
Positive exposed masses make its reversed mass ratios finite. -/
theorem standardizedRR_le_observedRR_mul_boundingFactor {n : ℕ} (m : FiniteRiskModel n)
    (h : ∀ u, 0 < m.mass true u) :
    m.standardizedRR ≤ m.observedRR *
      confoundingBoundingFactor
        (Finset.univ.sup' Finset.univ_nonempty fun u => m.mass false u / m.mass true u)
        m.confounderOutcomeRR := by
  let mr : FiniteRiskModel n := {
    exposureProb := 1 - m.exposureProb
    exposureProb_mem := ⟨by linarith [m.exposureProb_mem.2],
      by linarith [m.exposureProb_mem.1]⟩
    confounderLaw := fun e => m.confounderLaw (!e)
    control_mass_pos := h
    risk := fun e => m.risk (!e)
    risk_mem := fun e u => m.risk_mem (!e) u }
  have hmarg (u : Fin (n + 1)) : mr.marginalMass u = m.marginalMass u := by
    simp only [marginalMass, mass, mr, Bool.not_true, Bool.not_false]
    ring
  have hstd (e : Bool) : mr.standardizedRisk e = m.standardizedRisk (!e) := by
    simp only [standardizedRisk, hmarg]
    rfl
  have hout : mr.confounderOutcomeRR = m.confounderOutcomeRR := by
    change max (m.armConfounderOutcomeRR false) (m.armConfounderOutcomeRR true) = _
    exact max_comm _ _
  have hb := confoundingRR_le_boundingFactor mr
  rw [hout] at hb
  change (m.observedRisk false / m.observedRisk true) /
    (mr.standardizedRisk true / mr.standardizedRisk false) ≤ _ at hb
  rw [hstd true, hstd false] at hb
  simp only [Bool.not_true, Bool.not_false] at hb
  have ht := m.observedRisk_pos true
  have hf := m.observedRisk_pos false
  have hst := m.standardizedRisk_pos true
  have hsf := m.standardizedRisk_pos false
  have he : mr.exposureConfounderRR =
      Finset.univ.sup' Finset.univ_nonempty (fun u => m.mass false u / m.mass true u) := rfl
  rw [he] at hb
  field_simp at hb
  unfold standardizedRR observedRR
  rw [div_le_iff₀ hsf, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hf]
  nlinarith [hb]

end FiniteRiskModel

end MathlibExt.Probability.Causality
