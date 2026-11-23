/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.Q2
public import PhyslibExt.CondensedMatter.IsingModel.Magnetization
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint

/-!
# The Potts critical temperature and the FK critical parameter

The correspondence `β ↔ p = 1 - e^{-qβ/(q-1)}` between the inverse temperature of the
`q`-state Potts model and the FK edge parameter, and the identification of the critical inverse
temperature with the image of the FK critical point.

## i. Overview

For `q > 1` the maps `pToBeta q` and `betaToP q` are mutually inverse increasing bijections
between `[0, 1)` and `[0, ∞)`. The critical inverse temperature of a spontaneous magnetization
`m*` is `betaC m* = sup {β > 0 : m*(β) = 0}`. If `m* ≥ 0` and, for `β > 0`, `m*(β) > 0` exactly
when `β > pToBeta q p_c`, then `betaC m* = pToBeta q p_c`. For the Ising model (`q = 2`) this
gives `β_c = -(1/2) log (1 - p_c)` in terms of the FK critical point `p_c`.

## ii. Key results

- `pToBeta`, `betaToP` : the FK parametrization for general `q`.
- `betaToP_bijOn` : `betaToP q` is a bijection from `[0, ∞)` onto `[0, 1)` for `q > 1`.
- `betaC` : the critical inverse temperature of a magnetization curve.
- `betaC_eq` : `betaC m* = pToBeta q p_c` when positivity of `m*` switches at `pToBeta q p_c`.
- `isingBetaC_eq` : the Ising critical inverse temperature is `pToBeta 2 (fkPc d 2)` under the
  same hypotheses.

## iii. Table of contents

- A. The FK parametrization
- B. Critical inverse temperatures

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Sections 1.4 and 4.3.
- H. Duminil-Copin, *Lectures on the Ising and Potts models on the hypercubic lattice*, PIMS–CRM
  Summer School in Probability (2017).
-/

@[expose] public section

open Real

namespace StatMech

namespace IsingFK

/-! ## A. The FK parametrization -/

/-- The Potts inverse temperature `-((q - 1)/q) log (1 - p)` corresponding to the FK edge parameter
`p`. -/
noncomputable def pToBeta (q p : ℝ) : ℝ := -((q - 1) / q) * Real.log (1 - p)

/-- The FK edge parameter `1 - e^{-qβ/(q-1)}` of the `q`-state Potts model at inverse temperature
`β`. -/
noncomputable def betaToP (q β : ℝ) : ℝ := 1 - Real.exp (-(q / (q - 1)) * β)

lemma pToBeta_two (p : ℝ) : pToBeta 2 p = -(1 / 2) * Real.log (1 - p) := by
  unfold pToBeta; norm_num

lemma betaToP_two (β : ℝ) : betaToP 2 β = 1 - Real.exp (-2 * β) := by
  unfold betaToP; norm_num

/-- At `q = 2` the general parametrization `pToBeta` is `betaOfP`. -/
lemma pToBeta_two_eq_betaOfP (p : ℝ) : pToBeta 2 p = betaOfP p := by
  rw [pToBeta_two, betaOfP]

/-- At `q = 2` the general parametrization `betaToP` is `pOfBeta`. -/
lemma betaToP_two_eq_pOfBeta (β : ℝ) : betaToP 2 β = pOfBeta β := by
  rw [betaToP_two, pOfBeta]

lemma betaToP_pToBeta (q p : ℝ) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hp : p < 1) :
    betaToP q (pToBeta q p) = p := by
  unfold betaToP pToBeta
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hqm1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  rw [show -(q / (q - 1)) * (-((q - 1) / q) * Real.log (1 - p)) = Real.log (1 - p) by
    field_simp]
  rw [Real.exp_log h1p]; ring

lemma pToBeta_betaToP (q β : ℝ) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    pToBeta q (betaToP q β) = β := by
  unfold pToBeta betaToP
  have hqm1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  rw [show (1 - (1 - Real.exp (-(q / (q - 1)) * β))) = Real.exp (-(q / (q - 1)) * β) by ring]
  rw [Real.log_exp]; field_simp

lemma strictMonoOn_pToBeta (q : ℝ) (hq : 1 < q) :
    StrictMonoOn (pToBeta q) (Set.Iio 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  unfold pToBeta
  have hcoef : 0 < (q - 1) / q := by positivity
  have hlb : (0 : ℝ) < 1 - b := by linarith
  have hlog : Real.log (1 - b) < Real.log (1 - a) :=
    Real.log_lt_log hlb (by linarith)
  exact mul_lt_mul_of_neg_left hlog (by linarith [hcoef])

lemma strictMono_betaToP (q : ℝ) (hq : 1 < q) : StrictMono (betaToP q) := by
  intro a b hab
  unfold betaToP
  have hcoef : 0 < q / (q - 1) := by positivity
  have : Real.exp (-(q / (q - 1)) * b) < Real.exp (-(q / (q - 1)) * a) := by
    rw [Real.exp_lt_exp]
    nlinarith [hcoef]
  linarith

lemma betaToP_mem (q β : ℝ) (hq : 1 < q) (hβ : 0 ≤ β) :
    betaToP q β ∈ Set.Ico (0 : ℝ) 1 := by
  unfold betaToP
  refine ⟨?_, ?_⟩
  · have : Real.exp (-(q / (q - 1)) * β) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hc : 0 ≤ q / (q - 1) := by positivity
      nlinarith [mul_nonneg hc hβ]
    linarith
  · have : 0 < Real.exp (-(q / (q - 1)) * β) := Real.exp_pos _
    linarith

lemma pToBeta_mem (q p : ℝ) (hq : 1 < q) (hp : p ∈ Set.Ico (0 : ℝ) 1) :
    pToBeta q p ∈ Set.Ici (0 : ℝ) := by
  obtain ⟨hp0, hp1⟩ := hp
  rw [Set.mem_Ici]
  unfold pToBeta
  have hcoef : 0 ≤ (q - 1) / q := by positivity
  have hlog : Real.log (1 - p) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  nlinarith [mul_nonneg hcoef (neg_nonneg.mpr hlog)]

@[simp]
lemma pToBeta_zero (q : ℝ) : pToBeta q 0 = 0 := by unfold pToBeta; simp

@[simp]
lemma betaToP_zero (q : ℝ) : betaToP q 0 = 0 := by unfold betaToP; simp

lemma betaToP_bijOn (q : ℝ) (hq : 1 < q) :
    Set.BijOn (betaToP q) (Set.Ici 0) (Set.Ico 0 1) := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q ≠ 1 := by linarith
  refine ⟨fun β hβ => betaToP_mem q β hq hβ, ?_, ?_⟩
  · intro a _ b _ hab
    rw [← pToBeta_betaToP q a hq0 hq1, ← pToBeta_betaToP q b hq0 hq1, hab]
  · intro p hp
    exact ⟨pToBeta q p, pToBeta_mem q p hq hp, betaToP_pToBeta q p hq0 hq1 hp.2⟩

lemma pToBeta_bijOn (q : ℝ) (hq : 1 < q) :
    Set.BijOn (pToBeta q) (Set.Ico 0 1) (Set.Ici 0) := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q ≠ 1 := by linarith
  refine ⟨fun p hp => pToBeta_mem q p hq hp, ?_, ?_⟩
  · intro a ha b hb hab
    rw [← betaToP_pToBeta q a hq0 hq1 ha.2, ← betaToP_pToBeta q b hq0 hq1 hb.2, hab]
  · intro β hβ
    exact ⟨betaToP q β, betaToP_mem q β hq hβ, pToBeta_betaToP q β hq0 hq1⟩

/-! ## B. Critical inverse temperatures -/

/-- The critical inverse temperature `sup {β > 0 : m*(β) = 0}` of a spontaneous-magnetization curve
`m*`. See also `Ising.betaC`, the infimum of the inverse temperatures with positive
magnetization. -/
noncomputable def betaC (mStar : ℝ → ℝ) : ℝ :=
  sSup {β : ℝ | 0 < β ∧ mStar β = 0}

lemma betaC_eq (mStar : ℝ → ℝ) (q pc : ℝ)
    (hnonneg : ∀ β, 0 ≤ mStar β)
    (hpos_iff : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta q pc < β))
    (hpos : 0 < pToBeta q pc) :
    betaC mStar = pToBeta q pc := by
  unfold betaC
  have hset : {β : ℝ | 0 < β ∧ mStar β = 0} = Set.Ioc 0 (pToBeta q pc) := by
    ext β
    simp only [Set.mem_ofPred_eq, Set.mem_Ioc]
    refine and_congr_right fun hβ => ?_
    have hzero_iff : mStar β = 0 ↔ ¬ (0 < mStar β) := by
      constructor
      · intro h; rw [h]; exact lt_irrefl 0
      · intro h; exact le_antisymm (not_lt.mp h) (hnonneg β)
    rw [hzero_iff, hpos_iff β hβ, not_lt]
  rw [hset, csSup_Ioc hpos]

lemma betaC_eq_log (mStar : ℝ → ℝ) (q pc : ℝ)
    (hnonneg : ∀ β, 0 ≤ mStar β)
    (hpos_iff : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta q pc < β))
    (hpos : 0 < pToBeta q pc) :
    betaC mStar = -((q - 1) / q) * Real.log (1 - pc) :=
  betaC_eq mStar q pc hnonneg hpos_iff hpos

lemma magnetization_pos_iff (mStar : ℝ → ℝ) (q pc p : ℝ) (hq : 1 < q)
    (hp : p ∈ Set.Ico (0 : ℝ) 1) (hpc : pc ∈ Set.Ico (0 : ℝ) 1)
    (hβpos : 0 < pToBeta q p)
    (hpos_iff : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta q pc < β)) :
    0 < mStar (pToBeta q p) ↔ pc < p := by
  rw [hpos_iff _ hβpos]
  exact (strictMonoOn_pToBeta q hq).lt_iff_lt (Set.mem_Iio.mpr hpc.2) (Set.mem_Iio.mpr hp.2)

/-- The critical inverse temperature of the `d`-dimensional Ising model, `sup {β > 0 : m*(β) =
0}`. -/
noncomputable def isingBetaC (d : ℕ) : ℝ :=
  betaC (Ising.magnetization d)

lemma isingBetaC_eq (d : ℕ)
    (hnonneg : ∀ β, 0 ≤ Ising.magnetization d β)
    (hpos_iff : ∀ β, 0 < β →
      (0 < Ising.magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
    (hpos : 0 < pToBeta 2 (FK.fkPc d 2)) :
    isingBetaC d = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
  unfold isingBetaC
  rw [betaC_eq (Ising.magnetization d) 2 (FK.fkPc d 2) hnonneg hpos_iff hpos, pToBeta_two]

end IsingFK

end StatMech
