/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.Universality.STT

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace StatMech

namespace Universality











noncomputable def stt_triLocalMeasure (p0 p1 p2 : ℝ) : Measure LocalConfig :=
  ∑ ω : LocalConfig, ENNReal.ofReal (localWeight p0 p1 p2 ω) • Measure.dirac ω





def stt_triConn (ω : LocalConfig) : Bool × Bool × Bool := (triAB ω, triAC ω, triBC ω)




def stt_starConn (ω : LocalConfig) : Bool × Bool × Bool := (starAB ω, starAC ω, starBC ω)





theorem stt_localWeight_nonneg (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h0' : p0 ≤ 1) (h1 : 0 ≤ p1) (h1' : p1 ≤ 1) (h2 : 0 ≤ p2) (h2' : p2 ≤ 1)
    (ω : LocalConfig) : 0 ≤ localWeight p0 p1 p2 ω := by
  unfold localWeight edgeWeight
  apply mul_nonneg; apply mul_nonneg
  · cases ω.1 <;> simp <;> linarith
  · cases ω.2.1 <;> simp <;> linarith
  · cases ω.2.2 <;> simp <;> linarith



theorem stt_sum_weighted_dirac_singleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [DecidableEq α]
    (g : LocalConfig → ℝ≥0∞) (f : LocalConfig → α) (a : α) :
    (∑ ω : LocalConfig, g ω • Measure.dirac (f ω)) {a}
      = ∑ ω : LocalConfig, if f ω = a then g ω else 0 := by
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton a)]
  by_cases h : f ω = a <;> simp [Set.indicator, h]




theorem stt_map_triLocalMeasure (p0 p1 p2 : ℝ) (f : LocalConfig → Bool × Bool × Bool) :
    Measure.map f (stt_triLocalMeasure p0 p1 p2)
      = ∑ ω : LocalConfig, ENNReal.ofReal (localWeight p0 p1 p2 ω) • Measure.dirac (f ω) := by
  have hf : Measurable f := measurable_of_countable f
  ext s hs
  rw [Measure.map_apply hf hs]
  unfold stt_triLocalMeasure
  rw [Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      Measure.dirac_apply' _ (hf hs), Measure.dirac_apply' _ hs]
  congr 1



theorem stt_triLocalMeasure_univ (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h0' : p0 ≤ 1) (h1 : 0 ≤ p1) (h1' : p1 ≤ 1) (h2 : 0 ≤ p2) (h2' : p2 ≤ 1) :
    stt_triLocalMeasure p0 p1 p2 Set.univ = 1 := by
  unfold stt_triLocalMeasure
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  have : ∀ ω : LocalConfig,
      (ENNReal.ofReal (localWeight p0 p1 p2 ω) • Measure.dirac ω) Set.univ
        = ENNReal.ofReal (localWeight p0 p1 p2 ω) := by
    intro ω
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ]
    simp
  rw [Finset.sum_congr rfl (fun ω _ => this ω)]
  rw [← ENNReal.ofReal_sum_of_nonneg
      (fun ω _ => stt_localWeight_nonneg p0 p1 p2 h0 h0' h1 h1' h2 h2' ω)]
  rw [sum_localWeight]
  simp



theorem stt_isProbabilityMeasure_triLocalMeasure (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h0' : p0 ≤ 1) (h1 : 0 ≤ p1) (h1' : p1 ≤ 1) (h2 : 0 ≤ p2) (h2' : p2 ≤ 1) :
    IsProbabilityMeasure (stt_triLocalMeasure p0 p1 p2) :=
  ⟨stt_triLocalMeasure_univ p0 p1 p2 h0 h0' h1 h1' h2 h2'⟩













theorem stt_connWeight_eq (p0 p1 p2 : ℝ) (h : IsCriticalTri p0 p1 p2) (c : Bool × Bool × Bool) :
    (∑ ω : LocalConfig, if stt_triConn ω = c then localWeight p0 p1 p2 ω else 0)
      = ∑ ω : LocalConfig, if stt_starConn ω = c then localWeight (1-p0) (1-p1) (1-p2) ω else 0 := by
  unfold IsCriticalTri kappaTri at h
  obtain ⟨c1, c2, c3⟩ := c
  simp only [stt_triConn, stt_starConn, localWeight, edgeWeight, triAB, triAC, triBC,
    starAB, starAC, starBC, Fintype.sum_prod_type, Fintype.sum_bool, Prod.mk.injEq]
  cases c1 <;> cases c2 <;> cases c3 <;> norm_num <;> nlinarith [h]



theorem stt_ennreal_sum_ofReal_indicator (g : LocalConfig → ℝ) (P : LocalConfig → Prop)
    [DecidablePred P] (hg : ∀ ω, 0 ≤ g ω) :
    (∑ ω : LocalConfig, if P ω then ENNReal.ofReal (g ω) else 0)
      = ENNReal.ofReal (∑ ω : LocalConfig, if P ω then g ω else 0) := by
  rw [ENNReal.ofReal_sum_of_nonneg (by intro ω _; by_cases h : P ω <;> simp [h, hg ω])]
  apply Finset.sum_congr rfl
  intro ω _; by_cases h : P ω <;> simp [h]













theorem stt_map_conn_eq (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h0' : p0 ≤ 1) (h1 : 0 ≤ p1) (h1' : p1 ≤ 1) (h2 : 0 ≤ p2) (h2' : p2 ≤ 1)
    (h : IsCriticalTri p0 p1 p2) :
    Measure.map stt_triConn (stt_triLocalMeasure p0 p1 p2)
      = Measure.map stt_starConn (stt_triLocalMeasure (1 - p0) (1 - p1) (1 - p2)) := by
  rw [stt_map_triLocalMeasure, stt_map_triLocalMeasure]
  apply Measure.ext_of_singleton
  intro c
  rw [stt_sum_weighted_dirac_singleton, stt_sum_weighted_dirac_singleton,
      stt_ennreal_sum_ofReal_indicator _ _
        (stt_localWeight_nonneg p0 p1 p2 h0 h0' h1 h1' h2 h2'),
      stt_ennreal_sum_ofReal_indicator _ _
        (stt_localWeight_nonneg (1 - p0) (1 - p1) (1 - p2) (by linarith) (by linarith)
          (by linarith) (by linarith) (by linarith) (by linarith))]
  rw [stt_connWeight_eq p0 p1 p2 h c]

















noncomputable abbrev stt_triW (p0 p1 p2 : ℝ) (ω : LocalConfig) : ℝ≥0∞ :=
  ENNReal.ofReal (localWeight p0 p1 p2 ω)



noncomputable def stt_starMass (p0 p1 p2 : ℝ) (c : Bool × Bool × Bool) : ℝ≥0∞ :=
  ∑ ω : LocalConfig, if stt_starConn ω = c then stt_triW p0 p1 p2 ω else 0



noncomputable def stt_triMass (p0 p1 p2 : ℝ) (c : Bool × Bool × Bool) : ℝ≥0∞ :=
  ∑ ω : LocalConfig, if stt_triConn ω = c then stt_triW p0 p1 p2 ω else 0


theorem stt_starMass_ne_top (p0 p1 p2 : ℝ) (c : Bool × Bool × Bool) :
    stt_starMass p0 p1 p2 c ≠ ⊤ := by
  unfold stt_starMass stt_triW
  rw [← lt_top_iff_ne_top]
  apply ENNReal.sum_lt_top.2
  intro ω _
  by_cases h : stt_starConn ω = c <;> simp [h]




theorem stt_mass_eq (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h0' : p0 ≤ 1) (h1 : 0 ≤ p1) (h1' : p1 ≤ 1) (h2 : 0 ≤ p2) (h2' : p2 ≤ 1)
    (h : IsCriticalTri p0 p1 p2) (c : Bool × Bool × Bool) :
    stt_triMass p0 p1 p2 c = stt_starMass (1 - p0) (1 - p1) (1 - p2) c := by
  unfold stt_triMass stt_starMass stt_triW
  rw [stt_ennreal_sum_ofReal_indicator (localWeight p0 p1 p2) (fun ω => stt_triConn ω = c)
        (stt_localWeight_nonneg p0 p1 p2 h0 h0' h1 h1' h2 h2'),
      stt_ennreal_sum_ofReal_indicator (localWeight (1 - p0) (1 - p1) (1 - p2))
        (fun ω => stt_starConn ω = c)
        (stt_localWeight_nonneg (1 - p0) (1 - p1) (1 - p2) (by linarith) (by linarith)
          (by linarith) (by linarith) (by linarith) (by linarith))]
  rw [stt_connWeight_eq p0 p1 p2 h c]


theorem stt_triLocalMeasure_singleton (p0 p1 p2 : ℝ) (ω0 : LocalConfig) :
    stt_triLocalMeasure p0 p1 p2 {ω0} = stt_triW p0 p1 p2 ω0 := by
  unfold stt_triLocalMeasure stt_triW
  rw [Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single ω0]
  · rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton ω0)]
    simp
  · intro ω _ hne
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton ω0)]
    simp [Set.indicator, hne]
  · intro hns; exact absurd (Finset.mem_univ ω0) hns





noncomputable def stt_coupling (p0 p1 p2 : ℝ) : Measure (LocalConfig × LocalConfig) :=
  ∑ ωt : LocalConfig, ∑ ωs : LocalConfig,
    (if stt_triConn ωt = stt_starConn ωs
      then stt_triW p0 p1 p2 ωt * stt_triW (1 - p0) (1 - p1) (1 - p2) ωs
            / stt_starMass (1 - p0) (1 - p1) (1 - p2) (stt_starConn ωs)
      else 0) • Measure.dirac (ωt, ωs)


theorem stt_const_mul_sum_ite (a : ℝ≥0∞) (g : LocalConfig → ℝ≥0∞) (P : LocalConfig → Prop)
    [DecidablePred P] :
    (∑ ω : LocalConfig, if P ω then a * g ω else 0)
      = a * ∑ ω : LocalConfig, if P ω then g ω else 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro ω _; by_cases hh : P ω <;> simp [hh]




theorem stt_coupling_supported (p0 p1 p2 : ℝ) (ωt ωs : LocalConfig)
    (hne : stt_triConn ωt ≠ stt_starConn ωs) :
    stt_coupling p0 p1 p2 {(ωt, ωs)} = 0 := by
  unfold stt_coupling
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton (ωt, ωs))]
  by_cases hab : (a, b) = (ωt, ωs)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hab
    rw [if_neg hne]; simp
  · simp [Set.indicator, hab]



theorem stt_coupling_snd (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h0' : p0 ≤ 1) (h1 : 0 ≤ p1) (h1' : p1 ≤ 1) (h2 : 0 ≤ p2) (h2' : p2 ≤ 1)
    (h : IsCriticalTri p0 p1 p2) :
    Measure.map Prod.snd (stt_coupling p0 p1 p2)
      = stt_triLocalMeasure (1 - p0) (1 - p1) (1 - p2) := by
  apply Measure.ext_of_singleton
  intro ωs0
  rw [stt_triLocalMeasure_singleton,
      Measure.map_apply measurable_snd (measurableSet_singleton ωs0)]
  unfold stt_coupling
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  have step : ∀ ωt : LocalConfig,
      (∑ ωs : LocalConfig,
        (if stt_triConn ωt = stt_starConn ωs
          then stt_triW p0 p1 p2 ωt * stt_triW (1 - p0) (1 - p1) (1 - p2) ωs
                / stt_starMass (1 - p0) (1 - p1) (1 - p2) (stt_starConn ωs)
          else 0) • Measure.dirac (ωt, ωs)) (Prod.snd ⁻¹' {ωs0})
      = (if stt_triConn ωt = stt_starConn ωs0
          then stt_triW p0 p1 p2 ωt * stt_triW (1 - p0) (1 - p1) (1 - p2) ωs0
                / stt_starMass (1 - p0) (1 - p1) (1 - p2) (stt_starConn ωs0)
          else 0) := by
    intro ωt
    rw [Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single ωs0]
    · rw [Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply' _ (measurable_snd (measurableSet_singleton ωs0))]
      simp [Set.indicator, Set.mem_preimage]
    · intro ωs _ hne
      rw [Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply' _ (measurable_snd (measurableSet_singleton ωs0))]
      have : (ωt, ωs).snd ∉ ({ωs0} : Set LocalConfig) := by simp [hne]
      simp [Set.indicator, Set.mem_preimage, this]
    · intro hns; exact absurd (Finset.mem_univ ωs0) hns
  rw [Finset.sum_congr rfl (fun ωt _ => step ωt)]
  
  set c := stt_starConn ωs0 with hc
  have factored :
      (∑ ωt : LocalConfig, if stt_triConn ωt = c
          then stt_triW p0 p1 p2 ωt * stt_triW (1 - p0) (1 - p1) (1 - p2) ωs0
                / stt_starMass (1 - p0) (1 - p1) (1 - p2) c else 0)
        = (∑ ωt : LocalConfig, if stt_triConn ωt = c then stt_triW p0 p1 p2 ωt else 0)
            * (stt_triW (1 - p0) (1 - p1) (1 - p2) ωs0
                / stt_starMass (1 - p0) (1 - p1) (1 - p2) c) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ωt _
    by_cases hh : stt_triConn ωt = c <;> simp [hh, mul_div_assoc]
  rw [factored]
  show (∑ ωt : LocalConfig, if stt_triConn ωt = c then stt_triW p0 p1 p2 ωt else 0)
        * (stt_triW (1 - p0) (1 - p1) (1 - p2) ωs0
            / stt_starMass (1 - p0) (1 - p1) (1 - p2) c)
      = stt_triW (1 - p0) (1 - p1) (1 - p2) ωs0
  rw [show (∑ ωt : LocalConfig, if stt_triConn ωt = c then stt_triW p0 p1 p2 ωt else 0)
        = stt_triMass p0 p1 p2 c from rfl, stt_mass_eq p0 p1 p2 h0 h0' h1 h1' h2 h2' h c]
  set m := stt_starMass (1 - p0) (1 - p1) (1 - p2) c with hm
  set w := stt_triW (1 - p0) (1 - p1) (1 - p2) ωs0 with hw
  have hwzero : m = 0 → w = 0 := by
    intro hmz
    have hle : (if stt_starConn ωs0 = c then stt_triW (1 - p0) (1 - p1) (1 - p2) ωs0 else 0)
        ≤ stt_starMass (1 - p0) (1 - p1) (1 - p2) c := by
      unfold stt_starMass
      exact Finset.single_le_sum
        (f := fun ω => if stt_starConn ω = c then stt_triW (1 - p0) (1 - p1) (1 - p2) ω else 0)
        (by intro ω _; positivity) (Finset.mem_univ ωs0)
    rw [if_pos hc.symm] at hle
    rw [← hm, hmz] at hle
    exact le_antisymm hle bot_le
  by_cases hmz : m = 0
  · rw [hmz, hwzero hmz]; simp
  · rw [div_eq_mul_inv, ← mul_assoc, mul_comm m w, mul_assoc,
        ENNReal.mul_inv_cancel hmz (hm ▸ stt_starMass_ne_top (1 - p0) (1 - p1) (1 - p2) c),
        mul_one]



theorem stt_coupling_fst (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h0' : p0 ≤ 1) (h1 : 0 ≤ p1) (h1' : p1 ≤ 1) (h2 : 0 ≤ p2) (h2' : p2 ≤ 1)
    (h : IsCriticalTri p0 p1 p2) :
    Measure.map Prod.fst (stt_coupling p0 p1 p2)
      = stt_triLocalMeasure p0 p1 p2 := by
  apply Measure.ext_of_singleton
  intro ωt0
  rw [stt_triLocalMeasure_singleton,
      Measure.map_apply measurable_fst (measurableSet_singleton ωt0)]
  unfold stt_coupling
  rw [Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single ωt0]
  · rw [Measure.coe_finsetSum, Finset.sum_apply]
    have step : ∀ ωs : LocalConfig,
        ((if stt_triConn ωt0 = stt_starConn ωs
          then stt_triW p0 p1 p2 ωt0 * stt_triW (1 - p0) (1 - p1) (1 - p2) ωs
                / stt_starMass (1 - p0) (1 - p1) (1 - p2) (stt_starConn ωs)
          else 0) • Measure.dirac (ωt0, ωs)) (Prod.fst ⁻¹' {ωt0})
        = (if stt_triConn ωt0 = stt_starConn ωs
            then stt_triW p0 p1 p2 ωt0 * stt_triW (1 - p0) (1 - p1) (1 - p2) ωs
                  / stt_starMass (1 - p0) (1 - p1) (1 - p2) (stt_starConn ωs)
            else 0) := by
      intro ωs
      rw [Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply' _ (measurable_fst (measurableSet_singleton ωt0))]
      simp [Set.indicator, Set.mem_preimage]
    rw [Finset.sum_congr rfl (fun ωs _ => step ωs)]
    
    set c := stt_triConn ωt0 with hc
    have rew : ∀ ωs : LocalConfig,
        (if stt_triConn ωt0 = stt_starConn ωs
          then stt_triW p0 p1 p2 ωt0 * stt_triW (1 - p0) (1 - p1) (1 - p2) ωs
                / stt_starMass (1 - p0) (1 - p1) (1 - p2) (stt_starConn ωs)
          else 0)
        = (if stt_starConn ωs = c
            then (stt_triW p0 p1 p2 ωt0 / stt_starMass (1 - p0) (1 - p1) (1 - p2) c)
                  * stt_triW (1 - p0) (1 - p1) (1 - p2) ωs
            else 0) := by
      intro ωs
      by_cases hcase : stt_triConn ωt0 = stt_starConn ωs
      · have hcc : stt_starConn ωs = c := by rw [hc, hcase]
        rw [if_pos hcase, if_pos hcc, hcc, div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
      · have hcc : ¬ (stt_starConn ωs = c) := by rw [hc]; exact fun he => hcase he.symm
        rw [if_neg hcase, if_neg hcc]
    rw [Finset.sum_congr rfl (fun ωs _ => rew ωs), stt_const_mul_sum_ite]
    show (stt_triW p0 p1 p2 ωt0 / stt_starMass (1 - p0) (1 - p1) (1 - p2) c)
          * (∑ ωs : LocalConfig,
              if stt_starConn ωs = c then stt_triW (1 - p0) (1 - p1) (1 - p2) ωs else 0)
        = stt_triW p0 p1 p2 ωt0
    rw [show (∑ ωs : LocalConfig,
              if stt_starConn ωs = c then stt_triW (1 - p0) (1 - p1) (1 - p2) ωs else 0)
          = stt_starMass (1 - p0) (1 - p1) (1 - p2) c from rfl]
    set m := stt_starMass (1 - p0) (1 - p1) (1 - p2) c with hm
    set w := stt_triW p0 p1 p2 ωt0 with hw
    have hwzero : m = 0 → w = 0 := by
      intro hmz
      have hwm : stt_triMass p0 p1 p2 c = m := by
        rw [hm, stt_mass_eq p0 p1 p2 h0 h0' h1 h1' h2 h2' h c]
      have hle : (if stt_triConn ωt0 = c then stt_triW p0 p1 p2 ωt0 else 0)
          ≤ stt_triMass p0 p1 p2 c := by
        unfold stt_triMass
        exact Finset.single_le_sum
          (f := fun ω => if stt_triConn ω = c then stt_triW p0 p1 p2 ω else 0)
          (by intro ω _; positivity) (Finset.mem_univ ωt0)
      rw [if_pos hc.symm] at hle
      rw [hwm, hmz] at hle
      exact le_antisymm hle bot_le
    by_cases hmz : m = 0
    · rw [hmz, hwzero hmz]; simp
    · rw [div_eq_mul_inv, mul_assoc,
          ENNReal.inv_mul_cancel hmz (hm ▸ stt_starMass_ne_top (1 - p0) (1 - p1) (1 - p2) c),
          mul_one]
  · intro ωt _ hne
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro ωs _
    rw [Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply' _ (measurable_fst (measurableSet_singleton ωt0))]
    have : (ωt, ωs).fst ∉ ({ωt0} : Set LocalConfig) := by simp [hne]
    simp [Set.indicator, Set.mem_preimage, this]
  · intro hns; exact absurd (Finset.mem_univ ωt0) hns























theorem stt_exists_starTriangle_coupling (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h0' : p0 ≤ 1) (h1 : 0 ≤ p1) (h1' : p1 ≤ 1) (h2 : 0 ≤ p2) (h2' : p2 ≤ 1)
    (h : IsCriticalTri p0 p1 p2) :
    ∃ γ : Measure (LocalConfig × LocalConfig),
      Measure.map Prod.fst γ = stt_triLocalMeasure p0 p1 p2 ∧
      Measure.map Prod.snd γ = stt_triLocalMeasure (1 - p0) (1 - p1) (1 - p2) ∧
      ∀ ωt ωs : LocalConfig, stt_triConn ωt ≠ stt_starConn ωs → γ {(ωt, ωs)} = 0 :=
  ⟨stt_coupling p0 p1 p2,
   stt_coupling_fst p0 p1 p2 h0 h0' h1 h1' h2 h2' h,
   stt_coupling_snd p0 p1 p2 h0 h0' h1 h1' h2 h2' h,
   fun ωt ωs hne => stt_coupling_supported p0 p1 p2 ωt ωs hne⟩

end Universality

end StatMech
