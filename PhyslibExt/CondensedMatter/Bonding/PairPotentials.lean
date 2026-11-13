/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Topology.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.Basic
public import MathlibExt.Analysis.SpecialFunctions.Log.AlternatingHarmonic

/-!
# Interatomic pair potentials

Equilibrium spacing, bond stiffness, modulus estimates, and Madelung sums for
bonding models.

## i. Overview

A pair potential is a function `φ : ℝ → ℝ` of interatomic separation (used on
`r > 0`). An equilibrium spacing `r₀` satisfies `φ'(r₀) = 0` and the bond
stiffness is `S₀ = φ''(r₀)`. The Lennard-Jones potential
`φ(r) = 4 * ε * ((σ / r) ^ 12 - (σ / r) ^ 6)` has equilibrium spacing
`r₀ = 2 ^ (1 / 6) * σ`, energy `φ(r₀) = -ε`, and stiffness
`S₀ = 72 * ε / (2 ^ (1 / 3) * σ ^ 2)`.

The simple-cubic estimate `E ~ S₀ / r₀` is recorded as a MODEL estimate
(`bondModulusEstimate`), never as a theorem about real solids. The 1D
alternating-ion Madelung constant `2 * log 2` is the limit of explicitly
ordered finite partial sums (conditional convergence forbids an unconditional
`tsum`). The Born-Lande lattice energy takes the empirical Born exponent `n`
as an explicit input parameter (MODEL+EMP).

Reuse-verified against Mathlib/Physlib/ATLAS main; no ATLAS-50 prerequisite PR
dependency.

## ii. Key results

- `PairPotentials.lennardJones_eq_at_min` : `φ(r₀) = -ε`.
- `PairPotentials.lennardJones_deriv_at_min` : `φ'(r₀) = 0`.
- `PairPotentials.lennardJones_second_deriv_at_min` : `S₀ = φ''(r₀)`.
- `PairPotentials.madelung_one_dim` : the 1D Madelung constant as an ordered limit.
- `PairPotentials.bondModulusEstimate` : the `S₀ / r₀` model estimate.
- `PairPotentials.bondModulusEstimate_lennardJones` : its Lennard-Jones evaluation.
- `PairPotentials.bornLandeEnergy` : Born-Lande energy with empirical exponent `n`.
- `PairPotentials.bornLandeEnergy_neg_of_pos` : it is negative.
- `PairPotentials.bornLandeEnergy_factor_mem` : the factor `1 - 1 / n` lies in `(0, 1)`.

## iii. Table of contents

- A. Lennard-Jones pair potential
- B. One-dimensional Madelung constant
- C. Bond modulus estimate
- D. Born-Lande lattice energy

## iv. References

* N. W. Ashcroft and N. D. Mermin, *Solid State Physics*, Holt, Rinehart and Winston (1976),
  Chapters 3 and 20, for bonding, elastic moduli, and Madelung energies.
* C. Kittel, *Introduction to Solid State Physics*, 8th ed., Wiley (2005),
  Chapter 3, for the Lennard-Jones potential and the Born-Lande energy.

-/

@[expose] public section

open scoped Topology

namespace PairPotentials

/-! ## A. Lennard-Jones pair potential -/

-- `(2 ^ (1/6)) ^ 6 = 2`.

private lemma rpow_two_one_six_pow_six : ((2:ℝ) ^ (1/6 : ℝ)) ^ 6 = 2 := by
  have h6 : ((6 : ℕ) : ℝ) = 6 := by norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), h6]
  have h16 : (1/6 : ℝ) * 6 = 1 := by norm_num
  rw [h16, Real.rpow_one]

-- `(2 ^ (1/6)) ^ 2 = 2 ^ (1/3)`.

private lemma rpow_two_one_six_sq : ((2:ℝ) ^ (1/6 : ℝ)) ^ 2 = (2:ℝ) ^ (1/3 : ℝ) := by
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), h2]
  have h13 : (1/6 : ℝ) * 2 = 1/3 := by norm_num
  rw [h13]

-- `r₀ ^ 6 = 2 * σ ^ 6`.

private lemma lj_r0_pow_six (σ r₀ : ℝ) (hr₀ : r₀ = Real.rpow 2 (1/6) * σ) :
    r₀ ^ 6 = 2 * σ ^ 6 := by
  have hr₀' : r₀ = (2:ℝ) ^ (1/6 : ℝ) * σ := hr₀
  rw [hr₀', mul_pow, rpow_two_one_six_pow_six]

-- `r₀ ^ 2 = 2 ^ (1/3) * σ ^ 2`.

private lemma lj_r0_pow_two (σ r₀ : ℝ) (hr₀ : r₀ = Real.rpow 2 (1/6) * σ) :
    r₀ ^ 2 = Real.rpow 2 (1/3) * σ ^ 2 := by
  have hr₀' : r₀ = (2:ℝ) ^ (1/6 : ℝ) * σ := hr₀
  have hB : Real.rpow 2 (1/3) = (2:ℝ) ^ (1/3 : ℝ) := rfl
  rw [hr₀', mul_pow, rpow_two_one_six_sq, ← hB]

-- `r₀ > 0`.

private lemma lj_r0_pos (σ r₀ : ℝ) (hσ : 0 < σ)
    (hr₀ : r₀ = Real.rpow 2 (1/6) * σ) : 0 < r₀ := by
  rw [hr₀]
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hσ

-- `(σ / r₀) ^ 6 = 1 / 2`.

private lemma lj_upow_six (σ r₀ : ℝ) (hσ : 0 < σ)
    (hr₀ : r₀ = Real.rpow 2 (1/6) * σ) : (σ / r₀) ^ 6 = 1 / 2 := by
  rw [div_pow, lj_r0_pow_six σ r₀ hr₀]
  rw [div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero 6 (ne_of_gt hσ)))]
  ring

-- `(σ / r₀) ^ 12 = 1 / 4`.

private lemma lj_upow_twelve (σ r₀ : ℝ) (hσ : 0 < σ)
    (hr₀ : r₀ = Real.rpow 2 (1/6) * σ) : (σ / r₀) ^ 12 = 1 / 4 := by
  have h12 : (σ / r₀) ^ 12 = ((σ / r₀) ^ 6) ^ 2 := by ring
  rw [h12, lj_upow_six σ r₀ hσ hr₀]
  norm_num

/-- Lennard-Jones energy at its minimum: `φ(r₀) = -ε`. -/

lemma lennardJones_eq_at_min (ε σ r₀ : ℝ) (hε : 0 < ε) (hσ : 0 < σ)
    (hr₀ : r₀ = Real.rpow 2 (1/6) * σ) :
    4 * ε * ((σ / r₀) ^ 12 - (σ / r₀) ^ 6) = -ε := by
  rw [lj_upow_twelve σ r₀ hσ hr₀, lj_upow_six σ r₀ hσ hr₀]
  ring

-- First-derivative helper with the exact combinator-produced value.
private lemma lj_hasDerivAt (ε σ r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun r => 4 * ε * ((σ / r) ^ 12 - (σ / r) ^ 6))
      ((4 * ε) * ((((12 : ℕ) : ℝ) * (σ / r) ^ 11 * ((0 * r - σ * 1) / r ^ 2)) -
        (((6 : ℕ) : ℝ) * (σ / r) ^ 5 * ((0 * r - σ * 1) / r ^ 2)))) r := by
  have hbase : HasDerivAt (fun r => σ / r) ((0 * r - σ * 1) / r ^ 2) r :=
    (hasDerivAt_const r σ).div (hasDerivAt_id' r) hr
  exact ((hbase.pow 12).sub (hbase.pow 6)).const_mul (4 * ε)

/-- Lennard-Jones equilibrium condition: `φ'(r₀) = 0`. -/

lemma lennardJones_deriv_at_min (ε σ r₀ : ℝ) (hε : 0 < ε) (hσ : 0 < σ)
    (hr₀ : r₀ = Real.rpow 2 (1/6) * σ) :
    HasDerivAt (fun r => 4 * ε * ((σ / r) ^ 12 - (σ / r) ^ 6)) 0 r₀ := by
  have hr0 : r₀ ≠ 0 := ne_of_gt (lj_r0_pos σ r₀ hσ hr₀)
  have h := lj_hasDerivAt ε σ r₀ hr0
  have hD : ((4 * ε) * ((((12 : ℕ) : ℝ) * (σ / r₀) ^ 11 * ((0 * r₀ - σ * 1) / r₀ ^ 2)) -
      (((6 : ℕ) : ℝ) * (σ / r₀) ^ 5 * ((0 * r₀ - σ * 1) / r₀ ^ 2)))) = 0 := by
    have hu6 := lj_upow_six σ r₀ hσ hr₀
    have hu11 : (σ / r₀) ^ 11 = (σ / r₀) ^ 5 * (σ / r₀) ^ 6 := by ring
    rw [hu11, hu6]
    push_cast
    ring
  rw [hD] at h
  exact h

/-- Lennard-Jones stiffness: `S₀ = φ''(r₀)`. -/

lemma lennardJones_second_deriv_at_min (ε σ r₀ : ℝ) (hε : 0 < ε) (hσ : 0 < σ)
    (hr₀ : r₀ = Real.rpow 2 (1/6) * σ) :
    HasDerivAt (deriv (fun r => 4 * ε * ((σ / r) ^ 12 - (σ / r) ^ 6)))
      (72 * ε / (Real.rpow 2 (1 / 3) * σ ^ 2)) r₀ := by
  have hr0pos := lj_r0_pos σ r₀ hσ hr₀
  have hr0 : r₀ ≠ 0 := ne_of_gt hr0pos
  have hr02 : r₀ ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  -- Step 1: differentiate the explicit first-derivative function at r₀.
  have hD1 : HasDerivAt
      (fun r => (4 * ε) * ((((12 : ℕ) : ℝ) * (σ / r) ^ 11 * ((0 * r - σ * 1) / r ^ 2)) -
        (((6 : ℕ) : ℝ) * (σ / r) ^ 5 * ((0 * r - σ * 1) / r ^ 2))))
      (72 * ε / (Real.rpow 2 (1 / 3) * σ ^ 2)) r₀ := by
    have hbase0 : HasDerivAt (fun r => σ / r) ((0 * r₀ - σ * 1) / r₀ ^ 2) r₀ :=
      (hasDerivAt_const r₀ σ).div (hasDerivAt_id' r₀) hr0
    have h_u11 : HasDerivAt (fun r => (σ / r) ^ 11)
        ((((11 : ℕ) : ℝ)) * (σ / r₀) ^ 10 * ((0 * r₀ - σ * 1) / r₀ ^ 2)) r₀ :=
      hbase0.pow 11
    have h_u5 : HasDerivAt (fun r => (σ / r) ^ 5)
        ((((5 : ℕ) : ℝ)) * (σ / r₀) ^ 4 * ((0 * r₀ - σ * 1) / r₀ ^ 2)) r₀ :=
      hbase0.pow 5
    have h_c11 : HasDerivAt (fun r => ((12 : ℕ) : ℝ) * (σ / r) ^ 11)
        (((12 : ℕ) : ℝ) * ((((11 : ℕ) : ℝ)) * (σ / r₀) ^ 10 * ((0 * r₀ - σ * 1) / r₀ ^ 2))) r₀ :=
      h_u11.const_mul ((12 : ℕ) : ℝ)
    have h_c5 : HasDerivAt (fun r => ((6 : ℕ) : ℝ) * (σ / r) ^ 5)
        (((6 : ℕ) : ℝ) * ((((5 : ℕ) : ℝ)) * (σ / r₀) ^ 4 * ((0 * r₀ - σ * 1) / r₀ ^ 2))) r₀ :=
      h_u5.const_mul ((6 : ℕ) : ℝ)
    have h0r : HasDerivAt (fun r => 0 * r) (0 * 1) r₀ :=
      (hasDerivAt_id' r₀).const_mul 0
    have hσ1 : HasDerivAt (fun _ => σ * 1) 0 r₀ := hasDerivAt_const r₀ (σ * 1)
    have hN : HasDerivAt (fun r => 0 * r - σ * 1) (0 * 1 - 0) r₀ := h0r.sub hσ1
    have hDden : HasDerivAt (fun r => r ^ 2) ((((2 : ℕ) : ℝ)) * r₀ ^ (2 - 1) * 1) r₀ :=
      (hasDerivAt_id' r₀).pow 2
    have hF : HasDerivAt (fun r => (0 * r - σ * 1) / r ^ 2)
        (((0 * 1 - 0) * r₀ ^ 2 - (0 * r₀ - σ * 1) * ((((2 : ℕ) : ℝ)) * r₀ ^ (2 - 1) * 1)) /
          (r₀ ^ 2) ^ 2) r₀ :=
      hN.div hDden hr02

    have h_T1 : HasDerivAt
        (fun r => (((12 : ℕ) : ℝ) * (σ / r) ^ 11) * ((0 * r - σ * 1) / r ^ 2))
        ((((12 : ℕ) : ℝ) * ((((11 : ℕ) : ℝ)) * (σ / r₀) ^ 10 * ((0 * r₀ - σ * 1) / r₀ ^ 2))) *
            ((0 * r₀ - σ * 1) / r₀ ^ 2) +
          (((12 : ℕ) : ℝ) * (σ / r₀) ^ 11) *
            ((((0 * 1 - 0) * r₀ ^ 2 - (0 * r₀ - σ * 1) * ((((2 : ℕ) : ℝ)) * r₀ ^ (2 - 1) * 1)) /
              (r₀ ^ 2) ^ 2))) r₀ :=
      h_c11.mul hF
    have h_T2 : HasDerivAt
        (fun r => (((6 : ℕ) : ℝ) * (σ / r) ^ 5) * ((0 * r - σ * 1) / r ^ 2))
        ((((6 : ℕ) : ℝ) * ((((5 : ℕ) : ℝ)) * (σ / r₀) ^ 4 * ((0 * r₀ - σ * 1) / r₀ ^ 2))) *
            ((0 * r₀ - σ * 1) / r₀ ^ 2) +
          (((6 : ℕ) : ℝ) * (σ / r₀) ^ 5) *
            ((((0 * 1 - 0) * r₀ ^ 2 - (0 * r₀ - σ * 1) * ((((2 : ℕ) : ℝ)) * r₀ ^ (2 - 1) * 1)) /
              (r₀ ^ 2) ^ 2))) r₀ :=
      h_c5.mul hF
    have h2 : HasDerivAt
        (fun r => (4 * ε) * ((((12 : ℕ) : ℝ) * (σ / r) ^ 11 * ((0 * r - σ * 1) / r ^ 2)) -
          (((6 : ℕ) : ℝ) * (σ / r) ^ 5 * ((0 * r - σ * 1) / r ^ 2))))
        ((4 * ε) * (((((12 : ℕ) : ℝ) * ((((11 : ℕ) : ℝ)) * (σ / r₀) ^ 10 * ((0 * r₀ - σ * 1) / r₀ ^ 2))) *
              ((0 * r₀ - σ * 1) / r₀ ^ 2) +
            (((12 : ℕ) : ℝ) * (σ / r₀) ^ 11) *
              ((((0 * 1 - 0) * r₀ ^ 2 - (0 * r₀ - σ * 1) * ((((2 : ℕ) : ℝ)) * r₀ ^ (2 - 1) * 1)) /
                (r₀ ^ 2) ^ 2))) -
          ((((6 : ℕ) : ℝ) * ((((5 : ℕ) : ℝ)) * (σ / r₀) ^ 4 * ((0 * r₀ - σ * 1) / r₀ ^ 2))) *
              ((0 * r₀ - σ * 1) / r₀ ^ 2) +
            (((6 : ℕ) : ℝ) * (σ / r₀) ^ 5) *
              ((((0 * 1 - 0) * r₀ ^ 2 - (0 * r₀ - σ * 1) * ((((2 : ℕ) : ℝ)) * r₀ ^ (2 - 1) * 1)) /
                (r₀ ^ 2) ^ 2))))) r₀ :=
      (h_T1.sub h_T2).const_mul (4 * ε)
    have hD2 : ((4 * ε) * (((((12 : ℕ) : ℝ) * ((((11 : ℕ) : ℝ)) * (σ / r₀) ^ 10 * ((0 * r₀ - σ * 1) / r₀ ^ 2))) *
            ((0 * r₀ - σ * 1) / r₀ ^ 2) +
          (((12 : ℕ) : ℝ) * (σ / r₀) ^ 11) *
            ((((0 * 1 - 0) * r₀ ^ 2 - (0 * r₀ - σ * 1) * ((((2 : ℕ) : ℝ)) * r₀ ^ (2 - 1) * 1)) /
              (r₀ ^ 2) ^ 2))) -
        ((((6 : ℕ) : ℝ) * ((((5 : ℕ) : ℝ)) * (σ / r₀) ^ 4 * ((0 * r₀ - σ * 1) / r₀ ^ 2))) *
            ((0 * r₀ - σ * 1) / r₀ ^ 2) +
          (((6 : ℕ) : ℝ) * (σ / r₀) ^ 5) *
            ((((0 * 1 - 0) * r₀ ^ 2 - (0 * r₀ - σ * 1) * ((((2 : ℕ) : ℝ)) * r₀ ^ (2 - 1) * 1)) /
              (r₀ ^ 2) ^ 2))))) = 72 * ε / (Real.rpow 2 (1 / 3) * σ ^ 2) := by
      have hu6 := lj_upow_six σ r₀ hσ hr₀
      have hu10 : (σ / r₀) ^ 10 = (σ / r₀) ^ 4 * (σ / r₀) ^ 6 := by ring
      have hu11 : (σ / r₀) ^ 11 = (σ / r₀) ^ 5 * (σ / r₀) ^ 6 := by ring
      have hD2red : ((4 * ε) * (((((12 : ℕ) : ℝ) * ((((11 : ℕ) : ℝ)) * (σ / r₀) ^ 10 * ((0 * r₀ - σ * 1) / r₀ ^ 2))) *
              ((0 * r₀ - σ * 1) / r₀ ^ 2) +
            (((12 : ℕ) : ℝ) * (σ / r₀) ^ 11) *
              ((((0 * 1 - 0) * r₀ ^ 2 - (0 * r₀ - σ * 1) * ((((2 : ℕ) : ℝ)) * r₀ ^ (2 - 1) * 1)) /
                (r₀ ^ 2) ^ 2))) -
          ((((6 : ℕ) : ℝ) * ((((5 : ℕ) : ℝ)) * (σ / r₀) ^ 4 * ((0 * r₀ - σ * 1) / r₀ ^ 2))) *
              ((0 * r₀ - σ * 1) / r₀ ^ 2) +
            (((6 : ℕ) : ℝ) * (σ / r₀) ^ 5) *
              ((((0 * 1 - 0) * r₀ ^ 2 - (0 * r₀ - σ * 1) * ((((2 : ℕ) : ℝ)) * r₀ ^ (2 - 1) * 1)) /
                (r₀ ^ 2) ^ 2))))) =
          144 * ε * ((σ / r₀) ^ 4 * ((0 * r₀ - σ * 1) / r₀ ^ 2) ^ 2) := by
        set F0v := ((0 * r₀ - σ * 1) / r₀ ^ 2)
        set QF0v := ((((0 * 1 - 0) * r₀ ^ 2 - (0 * r₀ - σ * 1) * ((((2 : ℕ) : ℝ)) * r₀ ^ (2 - 1) * 1)) /
          (r₀ ^ 2) ^ 2))
        rw [hu10, hu11, hu6]
        push_cast
        ring

      have hF0simp : ((0 * r₀ - σ * 1) / r₀ ^ 2) = -σ / r₀ ^ 2 := by
        rw [div_eq_div_iff hr02 hr02]
        ring
      have hcore : (σ / r₀) ^ 4 * ((0 * r₀ - σ * 1) / r₀ ^ 2) ^ 2 = σ ^ 6 / r₀ ^ 8 := by
        rw [hF0simp, div_pow, div_pow, neg_sq]
        rw [show (r₀ ^ 2) ^ 2 = r₀ ^ 4 from by ring]
        have e1 : (4 + 2 : ℕ) = 6 := rfl
        have e2 : (4 + 4 : ℕ) = 8 := rfl
        rw [div_mul_div_comm, ← pow_add, ← pow_add, e1, e2]
      have hr08 : r₀ ^ 8 = 2 * Real.rpow 2 (1 / 3) * σ ^ 8 := by
        have e : r₀ ^ 8 = r₀ ^ 6 * r₀ ^ 2 := by ring
        rw [e, lj_r0_pow_six σ r₀ hr₀, lj_r0_pow_two σ r₀ hr₀]
        ring
      have hBpos : 0 < Real.rpow 2 (1 / 3) := Real.rpow_pos_of_pos (by norm_num) _
      have hσ' : σ ≠ 0 := ne_of_gt hσ
      have hBσ2 : Real.rpow 2 (1 / 3) * σ ^ 2 ≠ 0 :=
        mul_ne_zero (ne_of_gt hBpos) (pow_ne_zero 2 hσ')
      have h8 : (2 : ℝ) * Real.rpow 2 (1 / 3) * σ ^ 8 ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hBpos)) (pow_ne_zero 8 hσ')
      have h2d : (2 : ℝ) * Real.rpow 2 (1 / 3) * σ ^ 2 ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hBpos)) (pow_ne_zero 2 hσ')
      have hinner : σ ^ 6 / (2 * Real.rpow 2 (1 / 3) * σ ^ 8) =
          1 / (2 * Real.rpow 2 (1 / 3) * σ ^ 2) := by
        rw [div_eq_div_iff h8 h2d]
        ring
      rw [hD2red, hcore, hr08, hinner, mul_one_div, div_eq_div_iff h2d hBσ2]
      ring
    rw [hD2] at h2
    exact h2
  -- Step 2: `deriv φ` agrees with the explicit function near `r₀`.
  have heq : (deriv (fun r => 4 * ε * ((σ / r) ^ 12 - (σ / r) ^ 6))) =ᶠ[nhds r₀]
      (fun r => (4 * ε) * ((((12 : ℕ) : ℝ) * (σ / r) ^ 11 * ((0 * r - σ * 1) / r ^ 2)) -
        (((6 : ℕ) : ℝ) * (σ / r) ^ 5 * ((0 * r - σ * 1) / r ^ 2)))) := by
    have hpos : ∀ᶠ r in nhds r₀, (0 : ℝ) < r := eventually_gt_nhds hr0pos
    exact hpos.mono fun r hr => HasDerivAt.deriv (lj_hasDerivAt ε σ r (ne_of_gt hr))
  exact hD1.congr_of_eventuallyEq heq

/-! ## B. One-dimensional Madelung constant -/

/-- The 1D Madelung constant `2 * log 2` as an ordered partial-sum limit: twice the
alternating harmonic limit `Real.tendsto_sum_alternating_harmonic`. -/
lemma madelung_one_dim :
    Filter.Tendsto (fun N : ℕ => 2 * ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k / (k + 1))
      Filter.atTop (𝓝 (2 * Real.log 2)) :=
  Real.tendsto_sum_alternating_harmonic.const_mul 2

/-! ## C. Bond modulus estimate -/

/-- Model estimate of an elastic modulus from bond stiffness, not a theorem about real solids. -/
noncomputable def bondModulusEstimate (S₀ r₀ : ℝ) : ℝ := S₀ / r₀

/-- The bond-model estimate at Lennard-Jones stiffness and spacing. -/

lemma bondModulusEstimate_lennardJones (ε σ : ℝ) (hε : 0 < ε) (hσ : 0 < σ) :
    bondModulusEstimate (72 * ε / (Real.rpow 2 (1 / 3) * σ ^ 2)) (Real.rpow 2 (1 / 6) * σ) =
      72 * ε / (Real.sqrt 2 * σ ^ 3) := by
  have hBA : Real.rpow 2 (1 / 3) * Real.rpow 2 (1 / 6) = Real.sqrt 2 := by
    have h : (2 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (1 / 6 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by
      have h13 : (1 / 3 : ℝ) + (1 / 6 : ℝ) = 1 / 2 := by norm_num
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), h13]
    have h2 : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
    have hB : Real.rpow 2 (1 / 3) = (2 : ℝ) ^ (1 / 3 : ℝ) := rfl
    have hA : Real.rpow 2 (1 / 6) = (2 : ℝ) ^ (1 / 6 : ℝ) := rfl
    rw [hB, hA, h, h2]
  simp only [bondModulusEstimate]
  rw [div_div]
  have hden : (Real.rpow 2 (1 / 3) * σ ^ 2) * (Real.rpow 2 (1 / 6) * σ) =
      Real.sqrt 2 * σ ^ 3 := by
    have hring : (Real.rpow 2 (1 / 3) * σ ^ 2) * (Real.rpow 2 (1 / 6) * σ) =
        (Real.rpow 2 (1 / 3) * Real.rpow 2 (1 / 6)) * σ ^ 3 := by ring
    rw [hring, hBA]
  rw [hden]

/-! ## D. Born-Lande lattice energy -/

/-- Born-Lande lattice energy: `N_A` Avogadro number, `M` Madelung constant, `zPlus`/`zMinus`
cation/anion charge numbers, `e` elementary charge, `eps0` vacuum permittivity, `r₀` equilibrium
spacing, `n` the empirical Born exponent. Attractive lattice energy is negative. -/
noncomputable def bornLandeEnergy (N_A M zPlus zMinus e eps0 r₀ n : ℝ) : ℝ :=
  -(N_A * M * zPlus * zMinus * e ^ 2 / (4 * Real.pi * eps0 * r₀)) * (1 - 1 / n)

/-- The Born-Lande lattice energy is negative when all parameters are positive and `1 < n`. -/

lemma bornLandeEnergy_neg_of_pos (N_A M zPlus zMinus e eps0 r₀ n : ℝ)
    (hNA : 0 < N_A) (hM : 0 < M) (hZp : 0 < zPlus) (hZm : 0 < zMinus)
    (he : 0 < e) (heps : 0 < eps0) (hr : 0 < r₀) (hn : 1 < n) :
    bornLandeEnergy N_A M zPlus zMinus e eps0 r₀ n < 0 := by
  have hfac : 0 < 1 - 1 / n := by
    have hnpos : (0 : ℝ) < n := by linarith
    rw [sub_pos, div_lt_one hnpos]
    exact hn
  have hmain : 0 < N_A * M * zPlus * zMinus * e ^ 2 / (4 * Real.pi * eps0 * r₀) := by
    apply div_pos _ _
    · positivity
    · positivity
  simp only [bornLandeEnergy]
  rw [neg_mul]
  exact neg_lt_zero.mpr (mul_pos hmain hfac)

/-- The Born-Lande factor `1 - 1 / n` lies strictly between `0` and `1`. -/

lemma bornLandeEnergy_factor_mem (n : ℝ) (hn : 1 < n) : 0 < 1 - 1 / n ∧ 1 - 1 / n < 1 := by
  have hnpos : (0 : ℝ) < n := by linarith
  constructor
  · rw [sub_pos, div_lt_one hnpos]
    exact hn
  · have h1n : (0 : ℝ) < 1 / n := div_pos one_pos hnpos
    linarith


end PairPotentials
