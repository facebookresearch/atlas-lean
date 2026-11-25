/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.PatternCoding
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Tests for deterministic pattern coding

The anti-correlated law on two items (mass one half on each of the
patterns 10 and 01) has monotone coordinate curves, coordinate means
one half, product mean zero, and coordinate-indicator covariance
-1/4; it also violates the lattice inequality for positive
association. Deterministic coding reproduces it.
-/

@[expose] public section

open MeasureTheory
open MathlibExt.Probability.Statistics.Measurement

namespace MathlibExt.Probability.Statistics.Measurement

/-- Pattern `10` on two items: item `0` true, item `1` false. -/
private def pattern10 : Fin 2 → Bool :=
  fun i => if i = 0 then true else false

/-- Pattern `01` on two items: item `0` false, item `1` true. -/
private def pattern01 : Fin 2 → Bool :=
  fun i => if i = 1 then true else false

open scoped Classical in
/-- The anti-correlated law on two items: mass `1 / 2` on each of patterns
`10` and `01`, and mass `0` on patterns `00` and `11`. -/
private noncomputable def antiCorrelatedPMF : PMF (Fin 2 → Bool) :=
  PMF.ofFintype
    (fun x => if x = pattern10 ∨ x = pattern01
      then ENNReal.ofReal (1 / 2 : ℝ) else 0)
    (by
      have hne : pattern10 ≠ pattern01 := by decide
      have hfun : ∀ x : Fin 2 → Bool,
          (if x = pattern10 ∨ x = pattern01 then ENNReal.ofReal (1 / 2 : ℝ) else 0)
            = (if x = pattern10 then ENNReal.ofReal (1 / 2 : ℝ) else 0)
              + (if x = pattern01 then ENNReal.ofReal (1 / 2 : ℝ) else 0) := by
        intro x
        by_cases hx10 : x = pattern10
        · by_cases hx01 : x = pattern01
          · exfalso
            apply hne
            rw [← hx10, hx01]
          · simp [hx10, hx01, hne]
        · by_cases hx01 : x = pattern01
          · simp [hx10, hx01, Ne.symm hne]
          · simp [hx10, hx01]
      simp_rw [hfun]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq' Finset.univ pattern10
        (fun _ => ENNReal.ofReal (1 / 2 : ℝ))]
      rw [Finset.sum_ite_eq' Finset.univ pattern01
        (fun _ => ENNReal.ofReal (1 / 2 : ℝ))]
      simp only [Finset.mem_univ, ite_true]
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      have h12 : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
      rw [h12, ENNReal.ofReal_one])

/-! ## Boundary example helpers -/

/-- The two supporting patterns differ. -/
private theorem pattern10_ne_pattern01 : pattern10 ≠ pattern01 := by decide

/-- Value of pattern `10` at item `0`. -/
private theorem pattern10_apply_zero : pattern10 0 = true := by
  simp [pattern10]

/-- Value of pattern `10` at item `1`. -/
private theorem pattern10_apply_one : pattern10 1 = false := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [pattern10, h]

/-- Value of pattern `01` at item `0`. -/
private theorem pattern01_apply_zero : pattern01 0 = false := by
  have h : (0 : Fin 2) ≠ 1 := by decide
  simp [pattern01, h]

/-- Value of pattern `01` at item `1`. -/
private theorem pattern01_apply_one : pattern01 1 = true := by
  simp [pattern01]

/-- Real mass of a pattern under the anti-correlated law. -/
private theorem antiCorrelated_toReal (x : Fin 2 → Bool) :
    (antiCorrelatedPMF x).toReal
      = (if x = pattern10 ∨ x = pattern01 then (1 / 2 : ℝ) else 0) := by
  have hx : antiCorrelatedPMF x
      = (if x = pattern10 ∨ x = pattern01 then ENNReal.ofReal (1 / 2 : ℝ) else 0) := by
    simp [antiCorrelatedPMF]
  rw [hx]
  by_cases h : x = pattern10 ∨ x = pattern01
  · simp only [ite_eq_left h]
    exact ENNReal.toReal_ofReal (by norm_num)
  · simp only [ite_eq_right h]
    simp

/-- Mass of pattern `10` under the anti-correlated law. -/
private theorem antiCorrelated_mass10 :
    antiCorrelatedPMF pattern10 = ENNReal.ofReal (1 / 2 : ℝ) := by
  simp [antiCorrelatedPMF]

/-- Mass of pattern `01` under the anti-correlated law. -/
private theorem antiCorrelated_mass01 :
    antiCorrelatedPMF pattern01 = ENNReal.ofReal (1 / 2 : ℝ) := by
  simp [antiCorrelatedPMF]

/-- masses, coordinate means, product mean, and covariance of
the anti-correlated law. Mass `1 / 2` sits on each of patterns `10` and
`01`; both coordinate means are `1 / 2`; the product mean is `0`; the
covariance of the two coordinate indicators, as
`ProbabilityTheory.covariance` under `PMF.toMeasure`, is `-1 / 4`. -/
private theorem test_antiCorrelated_moments :
    (antiCorrelatedPMF pattern10 = ENNReal.ofReal (1 / 2 : ℝ))
    ∧ (antiCorrelatedPMF pattern01 = ENNReal.ofReal (1 / 2 : ℝ))
    ∧ ((antiCorrelatedPMF pattern10).toReal = 1 / 2)
    ∧ ((antiCorrelatedPMF pattern01).toReal = 1 / 2)
    ∧ (∑ x, (antiCorrelatedPMF x).toReal = 1)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂antiCorrelatedPMF.toMeasure = 1 / 2)
    ∧ (∫ x, (if x 1 then (1 : ℝ) else 0)
        ∂antiCorrelatedPMF.toMeasure = 1 / 2)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
        ∂antiCorrelatedPMF.toMeasure = 0)
    ∧ (ProbabilityTheory.covariance
        (fun x : Fin 2 → Bool => if x 0 then (1 : ℝ) else 0)
        (fun x : Fin 2 → Bool => if x 1 then (1 : ℝ) else 0)
        antiCorrelatedPMF.toMeasure = -1 / 4) := by
  have hmass10 : antiCorrelatedPMF pattern10 = ENNReal.ofReal (1 / 2 : ℝ) :=
    antiCorrelated_mass10
  have hmass01 : antiCorrelatedPMF pattern01 = ENNReal.ofReal (1 / 2 : ℝ) :=
    antiCorrelated_mass01
  have hreal10 : (antiCorrelatedPMF pattern10).toReal = 1 / 2 := by
    rw [hmass10]
    exact ENNReal.toReal_ofReal (by norm_num)
  have hreal01 : (antiCorrelatedPMF pattern01).toReal = 1 / 2 := by
    rw [hmass01]
    exact ENNReal.toReal_ofReal (by norm_num)
  have hsum : ∑ x, (antiCorrelatedPMF x).toReal = 1 := by
    simp_rw [antiCorrelated_toReal]
    have hfun : ∀ x : Fin 2 → Bool,
        (if x = pattern10 ∨ x = pattern01 then (1 / 2 : ℝ) else 0)
          = (if x = pattern10 then (1 / 2 : ℝ) else 0)
            + (if x = pattern01 then (1 / 2 : ℝ) else 0) := by
      intro x
      by_cases hx10 : x = pattern10
      · by_cases hx01 : x = pattern01
        · exfalso
          apply pattern10_ne_pattern01
          rw [← hx10, hx01]
        · simp [hx10, hx01, pattern10_ne_pattern01]
      · by_cases hx01 : x = pattern01
        · simp [hx10, hx01, Ne.symm pattern10_ne_pattern01]
        · simp [hx10, hx01]
    simp_rw [hfun]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq' Finset.univ pattern10 (fun _ => (1 / 2 : ℝ))]
    rw [Finset.sum_ite_eq' Finset.univ pattern01 (fun _ => (1 / 2 : ℝ))]
    simp only [Finset.mem_univ, ite_true]
    norm_num
  have hmean0 : ∫ x, (if x 0 then (1 : ℝ) else 0)
      ∂antiCorrelatedPMF.toMeasure = 1 / 2 := by
    rw [PMF.integral_eq_sum]
    simp only [smul_eq_mul]
    have hterm : ∀ x : Fin 2 → Bool,
        (antiCorrelatedPMF x).toReal * (if x 0 then (1 : ℝ) else 0)
          = (if x = pattern10 then (1 / 2 : ℝ) else 0) := by
      intro x
      rw [antiCorrelated_toReal x]
      by_cases hx10 : x = pattern10
      · subst hx10
        simp [pattern10_apply_zero]
      · by_cases hx01 : x = pattern01
        · subst hx01
          simp [pattern01_apply_zero, hx10]
        · simp [hx10, hx01]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq' Finset.univ pattern10 (fun _ => (1 / 2 : ℝ))]
    simp
  have hmean1 : ∫ x, (if x 1 then (1 : ℝ) else 0)
      ∂antiCorrelatedPMF.toMeasure = 1 / 2 := by
    rw [PMF.integral_eq_sum]
    simp only [smul_eq_mul]
    have hterm : ∀ x : Fin 2 → Bool,
        (antiCorrelatedPMF x).toReal * (if x 1 then (1 : ℝ) else 0)
          = (if x = pattern01 then (1 / 2 : ℝ) else 0) := by
      intro x
      rw [antiCorrelated_toReal x]
      by_cases hx10 : x = pattern10
      · subst hx10
        simp [pattern10_apply_one, pattern10_ne_pattern01]
      · by_cases hx01 : x = pattern01
        · subst hx01
          simp [pattern01_apply_one, hx10]
        · simp [hx10, hx01]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq' Finset.univ pattern01 (fun _ => (1 / 2 : ℝ))]
    simp
  have hprod : ∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
      ∂antiCorrelatedPMF.toMeasure = 0 := by
    rw [PMF.integral_eq_sum]
    simp only [smul_eq_mul]
    have hterm : ∀ x : Fin 2 → Bool,
        (antiCorrelatedPMF x).toReal
          * ((if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)) = 0 := by
      intro x
      rw [antiCorrelated_toReal x]
      by_cases hx10 : x = pattern10
      · subst hx10
        simp [pattern10_apply_zero, pattern10_apply_one]
      · by_cases hx01 : x = pattern01
        · subst hx01
          simp [pattern01_apply_zero, pattern01_apply_one]
        · simp [hx10, hx01]
    simp_rw [hterm]
    simp
  have hcov : ProbabilityTheory.covariance
      (fun x : Fin 2 → Bool => if x 0 then (1 : ℝ) else 0)
      (fun x : Fin 2 → Bool => if x 1 then (1 : ℝ) else 0)
      antiCorrelatedPMF.toMeasure = -1 / 4 := by
    unfold ProbabilityTheory.covariance
    rw [hmean0, hmean1]
    rw [PMF.integral_eq_sum]
    simp only [smul_eq_mul]
    have hterm : ∀ x : Fin 2 → Bool,
        (antiCorrelatedPMF x).toReal
          * (((if x 0 then (1 : ℝ) else 0) - 1 / 2)
            * ((if x 1 then (1 : ℝ) else 0) - 1 / 2))
          = (if x = pattern10 then (-1 / 8 : ℝ) else 0)
            + (if x = pattern01 then (-1 / 8 : ℝ) else 0) := by
      intro x
      rw [antiCorrelated_toReal x]
      by_cases hx10 : x = pattern10
      · subst hx10
        simp [pattern10_apply_zero, pattern10_apply_one,
          pattern10_ne_pattern01]
        norm_num
      · by_cases hx01 : x = pattern01
        · subst hx01
          simp [pattern01_apply_zero, pattern01_apply_one, hx10]
          norm_num
        · simp [hx10, hx01]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq' Finset.univ pattern10 (fun _ => (-1 / 8 : ℝ))]
    rw [Finset.sum_ite_eq' Finset.univ pattern01 (fun _ => (-1 / 8 : ℝ))]
    simp only [Finset.mem_univ, ite_true]
    norm_num
  exact ⟨hmass10, hmass01, hreal10, hreal01, hsum, hmean0, hmean1, hprod, hcov⟩

/-- monotone coordinate curves, with failure of the lattice
inequality at the explicit pair `10`, `01`. For each item the coordinate
curve `s ↦ if s i then 1 else 0` over the pattern lattice is monotone.
Writing `w x` for the real mass of pattern `x`, the lattice product at
`10` and `01` is `1 / 4`, the product at their join and meet is `0`, the
difference is `1 / 4`, and the inequality `w a * w b ≤ w (a ⊔ b) * w (a ⊓ b)`
does not hold for all patterns `a` and `b`. The last negation is backed
by the explicit instance before it, not stated alone. -/
private theorem test_antiCorrelated_monotone_not_lattice :
    (∀ i, Monotone (fun s : Fin 2 → Bool => if s i then (1 : ℝ) else 0))
    ∧ ((antiCorrelatedPMF pattern10).toReal
        * (antiCorrelatedPMF pattern01).toReal = 1 / 4)
    ∧ ((antiCorrelatedPMF (pattern10 ⊔ pattern01)).toReal
        * (antiCorrelatedPMF (pattern10 ⊓ pattern01)).toReal = 0)
    ∧ ((antiCorrelatedPMF pattern10).toReal
        * (antiCorrelatedPMF pattern01).toReal
        - (antiCorrelatedPMF (pattern10 ⊔ pattern01)).toReal
          * (antiCorrelatedPMF (pattern10 ⊓ pattern01)).toReal = 1 / 4)
    ∧ ((antiCorrelatedPMF pattern10).toReal
        * (antiCorrelatedPMF pattern01).toReal
        > (antiCorrelatedPMF (pattern10 ⊔ pattern01)).toReal
          * (antiCorrelatedPMF (pattern10 ⊓ pattern01)).toReal)
    ∧ ¬ (∀ a b : Fin 2 → Bool,
        (antiCorrelatedPMF a).toReal * (antiCorrelatedPMF b).toReal
          ≤ (antiCorrelatedPMF (a ⊔ b)).toReal
            * (antiCorrelatedPMF (a ⊓ b)).toReal) := by
  have hmono : ∀ i, Monotone (fun s : Fin 2 → Bool => if s i then (1 : ℝ) else 0) := by
    intro i a b hab
    have hi : a i ≤ b i := hab i
    cases ha : a i <;> cases hb : b i
    · simp [ha, hb]
    · simp [ha, hb]
    · exfalso
      have hcontra : ¬ ((true : Bool) ≤ false) := by decide
      rw [ha, hb] at hi
      exact hcontra hi
    · simp [ha, hb]
  have hreal10 : (antiCorrelatedPMF pattern10).toReal = 1 / 2 := by
    rw [antiCorrelated_mass10]
    exact ENNReal.toReal_ofReal (by norm_num)
  have hreal01 : (antiCorrelatedPMF pattern01).toReal = 1 / 2 := by
    rw [antiCorrelated_mass01]
    exact ENNReal.toReal_ofReal (by norm_num)
  have hprod10_01 : (antiCorrelatedPMF pattern10).toReal
      * (antiCorrelatedPMF pattern01).toReal = 1 / 4 := by
    rw [hreal10, hreal01]
    norm_num
  have hjoin0 : (pattern10 ⊔ pattern01) 0 = true := by
    simp only [Pi.sup_apply]
    rw [pattern10_apply_zero, pattern01_apply_zero]
    decide
  have hjoin1 : (pattern10 ⊔ pattern01) 1 = true := by
    simp only [Pi.sup_apply]
    rw [pattern10_apply_one, pattern01_apply_one]
    decide
  have hmeet0 : (pattern10 ⊓ pattern01) 0 = false := by
    simp only [Pi.inf_apply]
    rw [pattern10_apply_zero, pattern01_apply_zero]
    decide
  have hmeet1 : (pattern10 ⊓ pattern01) 1 = false := by
    simp only [Pi.inf_apply]
    rw [pattern10_apply_one, pattern01_apply_one]
    decide
  have hjoin_ne10 : (pattern10 ⊔ pattern01) ≠ pattern10 := by
    intro h
    have h1 := congrFun h 1
    rw [hjoin1, pattern10_apply_one] at h1
    exact absurd h1 (by decide)
  have hjoin_ne01 : (pattern10 ⊔ pattern01) ≠ pattern01 := by
    intro h
    have h0 := congrFun h 0
    rw [hjoin0, pattern01_apply_zero] at h0
    exact absurd h0 (by decide)
  have hmeet_ne10 : (pattern10 ⊓ pattern01) ≠ pattern10 := by
    intro h
    have h0 := congrFun h 0
    rw [hmeet0, pattern10_apply_zero] at h0
    exact absurd h0 (by decide)
  have hmeet_ne01 : (pattern10 ⊓ pattern01) ≠ pattern01 := by
    intro h
    have h1 := congrFun h 1
    rw [hmeet1, pattern01_apply_one] at h1
    exact absurd h1 (by decide)
  have hjoin_real : (antiCorrelatedPMF (pattern10 ⊔ pattern01)).toReal = 0 := by
    simp [antiCorrelated_toReal, hjoin_ne10, hjoin_ne01]
  have hmeet_real : (antiCorrelatedPMF (pattern10 ⊓ pattern01)).toReal = 0 := by
    simp [antiCorrelated_toReal, hmeet_ne10, hmeet_ne01]
  have hprod_join : (antiCorrelatedPMF (pattern10 ⊔ pattern01)).toReal
      * (antiCorrelatedPMF (pattern10 ⊓ pattern01)).toReal = 0 := by
    rw [hjoin_real, hmeet_real]
    norm_num
  have hdiff : (antiCorrelatedPMF pattern10).toReal
      * (antiCorrelatedPMF pattern01).toReal
      - (antiCorrelatedPMF (pattern10 ⊔ pattern01)).toReal
        * (antiCorrelatedPMF (pattern10 ⊓ pattern01)).toReal = 1 / 4 := by
    rw [hprod10_01, hprod_join]
    norm_num
  have hgt : (antiCorrelatedPMF pattern10).toReal
      * (antiCorrelatedPMF pattern01).toReal
      > (antiCorrelatedPMF (pattern10 ⊔ pattern01)).toReal
        * (antiCorrelatedPMF (pattern10 ⊓ pattern01)).toReal := by
    rw [hprod10_01, hprod_join]
    norm_num
  have hneg : ¬ (∀ a b : Fin 2 → Bool,
      (antiCorrelatedPMF a).toReal * (antiCorrelatedPMF b).toReal
        ≤ (antiCorrelatedPMF (a ⊔ b)).toReal
          * (antiCorrelatedPMF (a ⊓ b)).toReal) := by
    intro hall
    have h := hall pattern10 pattern01
    rw [hprod10_01, hprod_join] at h
    have hcontra : ¬ ((1 / 4 : ℝ) ≤ 0) := by norm_num
    exact hcontra h
  exact ⟨hmono, hprod10_01, hprod_join, hdiff, hgt, hneg⟩

/-- deterministic coding reproduces the anti-correlated law
itself. This instantiates the production theorem at the boundary example,
so the example is inside the scope of the coding identity rather than an
unrelated law. -/
private theorem test_deterministic_coding_antiCorrelated :
    antiCorrelatedPMF.bind
        (fun s => localIndepPMF (fun i => if s i then (1 : ℝ) else 0)
          (fun i => by by_cases h : s i <;> simp [h])
          (fun i => by by_cases h : s i <;> simp [h]))
      = antiCorrelatedPMF := by
  exact deterministic_pattern_coding antiCorrelatedPMF

end MathlibExt.Probability.Statistics.Measurement
