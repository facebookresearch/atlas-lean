/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Code.Probability.EntropySubadditivity
import Code.Probability.KKLpBiased

open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


























theorem pkc_kkl_logGain_largeInfl {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    (hδlo : Real.exp (-(1 / (2 * (p * (1 - p)))))
      ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :
    2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  have hprob := OSSS.bernoulliWeight_isProbWeight (E := E) hp0.le hp1.le
  have hTnn : 0 ≤ T := kkl_totalInfl_nonneg hprob f
  have hδnn : 0 ≤ δ := kkl_maxInfl_nonneg hprob f
  set V := ∑ S ∈ (univ.erase (∅ : Finset E)), (ptn_coeff p f S) ^ 2 with hVdef
  have hvarV : OSSS.var (OSSS.bernoulliWeight p) f = V := ptn_var_eq_fourierWeight hp0 hp1 f
  rw [hvarV]
  rcases eq_or_lt_of_le (hvarV ▸ kkl_var_nonneg hprob f) with hV0 | hVpos
  · 
    rw [← hV0, mul_zero, zero_mul]; exact hTnn
  · 
    obtain ⟨hr0pos, _hr0lt1, hr0bal⟩ := esa_logBalance_threshold hp0 hp1
    set r := Real.exp (-(1 / (2 * (p * (1 - p))))) with hrdef
    
    set D := ∑ S ∈ (univ.erase (∅ : Finset E)), (ptn_coeff p f S) ^ 2 * r ^ S.card with hDdef
    have hDmass : pen_dampedMass p r f = D := rfl
    have hDpos : 0 < D := by rw [← hDmass]; exact pen_dampedMass_pos hr0pos f hVpos
    
    have hDampV : D ≤ δ * V := by
      have hr1 : r ≤ 1 := _hr0lt1.le
      have hle : pen_dampedMass p r f ≤ r * V := by
        have := esa_dampedMass_le (p := p) hr0pos hr1 f
        rwa [← hVdef] at this
      rw [hDmass] at hle
      have hVnn : 0 ≤ V := hVpos.le
      calc D ≤ r * V := hle
        _ ≤ δ * V := mul_le_mul_of_nonneg_right hδlo hVnn
    
    have hext := pen_degree_extraction (univ.erase (∅ : Finset E))
      (fun S => (ptn_coeff p f S) ^ 2) (fun S => S.card) r hr0pos
      (fun S _ => sq_nonneg _) hDpos
    simp only [] at hext
    set M := ∑ S ∈ (univ.erase (∅ : Finset E)), (S.card : ℝ) * (ptn_coeff p f S) ^ 2 with hMdef
    have hMeq : M = (p * (1 - p)) * T := by
      rw [hMdef, hT]; exact pen_degreeWeight_eq hp0 hp1 φ
    have hextVDM : V * Real.log (V / D) ≤ Real.log (1 / r) * M := hext
    
    have hLog : 4 * (p * (1 - p)) * Real.log (1 / r) ≤ 2 := le_of_eq hr0bal
    exact pen_logGain_assembly (V := V) (D := D) (T := T) (δ := δ)
      (L := Real.log (1 / r)) (pp := p * (1 - p)) (M := M)
      hVpos hDpos hTnn hδnn (by nlinarith [hp0, hp1] : (0:ℝ) ≤ p * (1 - p)) hMeq
      hextVDM hDampV hLog




theorem pkc_kkl_logGain_largeInfl' {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    (hδlo : Real.exp (-(1 / (2 * (p * (1 - p)))))
      ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :
    2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  pkc_kkl_logGain_largeInfl hp0 hp1 φ hδlo







theorem pkc_threshold_le_exp_neg_two {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Real.exp (-(1 / (2 * (p * (1 - p))))) ≤ Real.exp (-2) := by
  apply Real.exp_le_exp.mpr
  have hppos : 0 < p * (1 - p) := by nlinarith
  have hle : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - (1 - p))]
  have h2 : 0 < 2 * (p * (1 - p)) := by positivity
  have hge : (2 : ℝ) ≤ 1 / (2 * (p * (1 - p))) := by
    rw [le_div_iff₀ h2]; nlinarith [hle]
  linarith





theorem pkc_threshold_antitone_to_one {p p' : ℝ} (hp : 1 / 2 ≤ p) (hpp' : p < p') (hp'1 : p' < 1) :
    Real.exp (-(1 / (2 * (p' * (1 - p'))))) ≤ Real.exp (-(1 / (2 * (p * (1 - p))))) := by
  apply Real.exp_le_exp.mpr
  have hp1 : p < 1 := lt_trans hpp' hp'1
  have hp0 : 0 < p := by linarith
  have hp'0 : 0 < p' := by linarith
  have hpp : 0 < p * (1 - p) := by nlinarith
  have hp'p : 0 < p' * (1 - p') := by nlinarith
  
  have hprod : p' * (1 - p') ≤ p * (1 - p) := by nlinarith [hpp', hp, hp'1]
  
  have h2p : 0 < 2 * (p * (1 - p)) := by positivity
  have h2p' : 0 < 2 * (p' * (1 - p')) := by positivity
  have hinv : 1 / (2 * (p * (1 - p))) ≤ 1 / (2 * (p' * (1 - p'))) := by
    apply one_div_le_one_div_of_le h2p'
    linarith [hprod]
  linarith






theorem pkc_dampingWitness_of_hard {q : ℝ} (H : esa_DampingHard q) : pen_DampingWitness q :=
  esa_dampingWitness_of_hard H


theorem pkc_rhoOptimise_of_hard {q : ℝ} (H : esa_DampingHard q) : ptn_RhoOptimise q :=
  pen_rhoOptimise_of_damping (esa_dampingWitness_of_hard H)




theorem pkc_PBiasedHC_of_hard {q : ℝ} (hq : q ≤ 1) (H : esa_DampingHard q) :
    kpb_PBiasedHC q :=
  pen_PBiasedHC_of_damping hq (esa_dampingWitness_of_hard H)




theorem pkc_kklHC_of_hard {q : ℝ} (H : esa_DampingHard q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1) :
    KKLHypercontractive p 2 :=
  pen_kklHC_of_damping (esa_dampingWitness_of_hard H) hp hp1





theorem pkc_sharpThreshold_of_hard {q : ℝ} (hq1 : q ≤ 1) (H : esa_DampingHard q)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {v₀ L : ℝ} (hq : (1 : ℝ) / 2 ≤ q) (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      L ≤ StatMech.TwoDim.kklw_logMaxInfl p A) :
    1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A :=
  kpb_sharpThreshold A hA hq hv0 hL hhalf (pkc_PBiasedHC_of_hard hq1 H) hvar hLL'

end StatMech.Probability
