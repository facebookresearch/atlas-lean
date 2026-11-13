/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.FK.CriticalPoint
import Code.Ising.Magnetization

open Real

namespace StatMech

namespace IsingFK






noncomputable def pToBeta (q p : ℝ) : ℝ := -((q - 1) / q) * Real.log (1 - p)





noncomputable def betaToP (q β : ℝ) : ℝ := 1 - Real.exp (-(q / (q - 1)) * β)



theorem pToBeta_two (p : ℝ) : pToBeta 2 p = -(1 / 2) * Real.log (1 - p) := by
  unfold pToBeta; norm_num



theorem betaToP_two (β : ℝ) : betaToP 2 β = 1 - Real.exp (-2 * β) := by
  unfold betaToP; norm_num





theorem betaToP_pToBeta (q p : ℝ) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hp : p < 1) :
    betaToP q (pToBeta q p) = p := by
  unfold betaToP pToBeta
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hqm1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  rw [show -(q / (q - 1)) * (-((q - 1) / q) * Real.log (1 - p)) = Real.log (1 - p) by
    field_simp]
  rw [Real.exp_log h1p]; ring



theorem pToBeta_betaToP (q β : ℝ) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    pToBeta q (betaToP q β) = β := by
  unfold pToBeta betaToP
  have hqm1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  rw [show (1 - (1 - Real.exp (-(q / (q - 1)) * β))) = Real.exp (-(q / (q - 1)) * β) by ring]
  rw [Real.log_exp]; field_simp





theorem strictMonoOn_pToBeta (q : ℝ) (hq : 1 < q) :
    StrictMonoOn (pToBeta q) (Set.Iio 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  unfold pToBeta
  have hcoef : 0 < (q - 1) / q := by positivity
  have hlb : (0 : ℝ) < 1 - b := by linarith
  have hlog : Real.log (1 - b) < Real.log (1 - a) :=
    Real.log_lt_log hlb (by linarith)
  exact mul_lt_mul_of_neg_left hlog (by linarith [hcoef])



theorem strictMono_betaToP (q : ℝ) (hq : 1 < q) : StrictMono (betaToP q) := by
  intro a b hab
  unfold betaToP
  have hcoef : 0 < q / (q - 1) := by positivity
  have : Real.exp (-(q / (q - 1)) * b) < Real.exp (-(q / (q - 1)) * a) := by
    rw [Real.exp_lt_exp]
    nlinarith [hcoef]
  linarith


theorem betaToP_mem (q β : ℝ) (hq : 1 < q) (hβ : 0 ≤ β) :
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


theorem pToBeta_mem (q p : ℝ) (hq : 1 < q) (hp : p ∈ Set.Ico (0 : ℝ) 1) :
    pToBeta q p ∈ Set.Ici (0 : ℝ) := by
  obtain ⟨hp0, hp1⟩ := hp
  rw [Set.mem_Ici]
  unfold pToBeta
  have hcoef : 0 ≤ (q - 1) / q := by positivity
  have hlog : Real.log (1 - p) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  nlinarith [mul_nonneg hcoef (neg_nonneg.mpr hlog)]


@[simp]
theorem pToBeta_zero (q : ℝ) : pToBeta q 0 = 0 := by unfold pToBeta; simp



@[simp]
theorem betaToP_zero (q : ℝ) : betaToP q 0 = 0 := by unfold betaToP; simp






theorem betaToP_bijOn (q : ℝ) (hq : 1 < q) :
    Set.BijOn (betaToP q) (Set.Ici 0) (Set.Ico 0 1) := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q ≠ 1 := by linarith
  refine ⟨fun β hβ => betaToP_mem q β hq hβ, ?_, ?_⟩
  · intro a _ b _ hab
    rw [← pToBeta_betaToP q a hq0 hq1, ← pToBeta_betaToP q b hq0 hq1, hab]
  · intro p hp
    exact ⟨pToBeta q p, pToBeta_mem q p hq hp, betaToP_pToBeta q p hq0 hq1 hp.2⟩



theorem pToBeta_bijOn (q : ℝ) (hq : 1 < q) :
    Set.BijOn (pToBeta q) (Set.Ico 0 1) (Set.Ici 0) := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q ≠ 1 := by linarith
  refine ⟨fun p hp => pToBeta_mem q p hq hp, ?_, ?_⟩
  · intro a ha b hb hab
    rw [← betaToP_pToBeta q a hq0 hq1 ha.2, ← betaToP_pToBeta q b hq0 hq1 hb.2, hab]
  · intro β hβ
    exact ⟨betaToP q β, betaToP_mem q β hq hβ, pToBeta_betaToP q β hq0 hq1⟩







noncomputable def betaC (mStar : ℝ → ℝ) : ℝ :=
  sSup {β : ℝ | 0 < β ∧ mStar β = 0}

@[simp]
theorem mem_zeroMagnetizationSet {mStar : ℝ → ℝ} {β : ℝ} :
    β ∈ {β : ℝ | 0 < β ∧ mStar β = 0} ↔ 0 < β ∧ mStar β = 0 :=
  Iff.rfl

















theorem betaC_eq (mStar : ℝ → ℝ) (q pc : ℝ)
    (hnonneg : ∀ β, 0 ≤ mStar β)
    (hpos_iff : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta q pc < β))
    (hpos : 0 < pToBeta q pc) :
    betaC mStar = pToBeta q pc := by
  unfold betaC
  have hset : {β : ℝ | 0 < β ∧ mStar β = 0} = Set.Ioc 0 (pToBeta q pc) := by
    ext β
    simp only [Set.mem_setOf_eq, Set.mem_Ioc]
    refine and_congr_right fun hβ => ?_
    
    have hzero_iff : mStar β = 0 ↔ ¬ (0 < mStar β) := by
      constructor
      · intro h; rw [h]; exact lt_irrefl 0
      · intro h; exact le_antisymm (not_lt.mp h) (hnonneg β)
    rw [hzero_iff, hpos_iff β hβ, not_lt]
  rw [hset, csSup_Ioc hpos]




theorem betaC_eq_log (mStar : ℝ → ℝ) (q pc : ℝ)
    (hnonneg : ∀ β, 0 ≤ mStar β)
    (hpos_iff : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta q pc < β))
    (hpos : 0 < pToBeta q pc) :
    betaC mStar = -((q - 1) / q) * Real.log (1 - pc) :=
  betaC_eq mStar q pc hnonneg hpos_iff hpos







theorem magnetization_pos_iff (mStar : ℝ → ℝ) (q pc p : ℝ) (hq : 1 < q)
    (hp : p ∈ Set.Ico (0 : ℝ) 1) (hpc : pc ∈ Set.Ico (0 : ℝ) 1)
    (hβpos : 0 < pToBeta q p)
    (hpos_iff : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta q pc < β)) :
    0 < mStar (pToBeta q p) ↔ pc < p := by
  rw [hpos_iff _ hβpos]
  exact (strictMonoOn_pToBeta q hq).lt_iff_lt (Set.mem_Iio.mpr hpc.2) (Set.mem_Iio.mpr hp.2)








noncomputable def isingBetaC (d : ℕ) : ℝ :=
  betaC (Ising.magnetization d)












theorem isingBetaC_eq (d : ℕ)
    (hnonneg : ∀ β, 0 ≤ Ising.magnetization d β)
    (hpos_iff : ∀ β, 0 < β →
      (0 < Ising.magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
    (hpos : 0 < pToBeta 2 (FK.fkPc d 2)) :
    isingBetaC d = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
  unfold isingBetaC
  rw [betaC_eq (Ising.magnetization d) 2 (FK.fkPc d 2) hnonneg hpos_iff hpos, pToBeta_two]

end IsingFK

end StatMech
