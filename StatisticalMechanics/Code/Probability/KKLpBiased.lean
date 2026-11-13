/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Code.TwoDim.KKLWire
import Code.Probability.RhoOptimiseClose2

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace StatMech

namespace Probability

open ConfigSpace Function Finset StatMech StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]










def kpb_flipAll (ω : ConfigSpace E) : ConfigSpace E := fun e => !(ω e)

omit [Fintype E] [DecidableEq E] in

lemma kpb_flipAll_involutive : Function.Involutive (kpb_flipAll (E := E)) := by
  intro ω; funext e; simp [kpb_flipAll]

omit [DecidableEq E] in


lemma kpb_weight_flip (p : ℝ) (ω : ConfigSpace E) :
    OSSS.weight (OSSS.bernoulliWeight (1 - p)) (kpb_flipAll ω)
      = OSSS.weight (OSSS.bernoulliWeight p) ω := by
  unfold OSSS.weight OSSS.bernoulliWeight kpb_flipAll
  apply Finset.prod_congr rfl
  intro e _
  cases ω e <;> simp



lemma kpb_expect_flip (p : ℝ) (g : ConfigSpace E → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight (1 - p)) g
      = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
  unfold OSSS.expect
  rw [Fintype.sum_bijective (kpb_flipAll) (kpb_flipAll_involutive.bijective)
        (fun ω => OSSS.weight (OSSS.bernoulliWeight p) ω * g (kpb_flipAll ω))
        (fun ω => OSSS.weight (OSSS.bernoulliWeight (1 - p)) ω * g ω)
        (fun ω => by simp only [kpb_weight_flip])]

omit [Fintype E] in

lemma kpb_flipAll_setOpen (e : E) (ω : ConfigSpace E) :
    kpb_flipAll (StatMech.setOpen e ω) = StatMech.setClosed e (kpb_flipAll ω) := by
  funext e'; unfold kpb_flipAll StatMech.setOpen StatMech.setClosed
  by_cases h : e' = e
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]

omit [Fintype E] in

lemma kpb_flipAll_setClosed (e : E) (ω : ConfigSpace E) :
    kpb_flipAll (StatMech.setClosed e ω) = StatMech.setOpen e (kpb_flipAll ω) := by
  funext e'; unfold kpb_flipAll StatMech.setOpen StatMech.setClosed
  by_cases h : e' = e
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]










lemma kpb_infl_flip (p : ℝ) (g : ConfigSpace E → ℝ) (e : E) :
    OSSS.infl (OSSS.bernoulliWeight (1 - p)) g e
      = OSSS.infl (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) e := by
  unfold OSSS.infl
  rw [kpb_expect_flip p]
  apply congrArg
  funext ω
  simp only [kpb_flipAll_setOpen, kpb_flipAll_setClosed]
  rw [abs_sub_comm]


lemma kpb_var_flip (p : ℝ) (g : ConfigSpace E → ℝ) :
    OSSS.var (OSSS.bernoulliWeight (1 - p)) g
      = OSSS.var (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
  unfold OSSS.var OSSS.cov
  rw [kpb_expect_flip p (fun ω => g ω * g ω), kpb_expect_flip p g]


lemma kpb_totalInfl_flip (p : ℝ) (g : ConfigSpace E → ℝ) :
    totalInfl (OSSS.bernoulliWeight (1 - p)) g
      = totalInfl (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
  unfold totalInfl
  exact Finset.sum_congr rfl (fun e _ => kpb_infl_flip p g e)


lemma kpb_maxInfl_flip [Nonempty E] (p : ℝ) (g : ConfigSpace E → ℝ) :
    maxInfl (OSSS.bernoulliWeight (1 - p)) g
      = maxInfl (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
  unfold maxInfl
  apply Finset.sup'_congr _ rfl
  intro e _
  exact kpb_infl_flip p g e











theorem kpb_kkl_reflect {p : ℝ} (H : KKLHypercontractive p 2) :
    KKLHypercontractive (1 - p) 2 := by
  intro E _ _ _ φ
  
  have hH := H (E := E) (fun ω => φ (kpb_flipAll ω))
  have he : (fun ω => if φ (kpb_flipAll ω) then (1 : ℝ) else 0)
      = (fun ω => (fun ω => if φ ω then (1 : ℝ) else 0) (kpb_flipAll ω)) := rfl
  rw [he] at hH
  rw [kpb_var_flip p, kpb_maxInfl_flip p, kpb_totalInfl_flip p]
  exact hH


















def kpb_PBiasedHC (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, KKLHypercontractive p 2





theorem kpb_residue_c0 {q : ℝ} (hq : q ≤ 1) :
    ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, KKLHypercontractive p 0 := by
  intro p hp
  exact kkl_hypercontractive_zero p (by linarith [hp.1]) (by linarith [hp.2])




theorem kpb_PBiasedHC_half_holds : KKLHypercontractive (1 / 2 : ℝ) 2 :=
  bph_KKL cro2_rhoOptimise






theorem kpb_residue_noncirc {p : ℝ} (H : KKLHypercontractive p 2)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p)
            (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  H φ






theorem kpb_kkl_pbiased {q : ℝ} (Hpb : kpb_PBiasedHC q) :
    ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, KKLHypercontractive p 2 :=
  Hpb




theorem kpb_Hbkkkl {q : ℝ} (Hpb : kpb_PBiasedHC q) :
    ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), KKLHypercontractive p 2 := by
  intro p hp
  rw [interior_Icc] at hp
  exact Hpb p hp


















theorem kpb_sharpThreshold {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {q v₀ L : ℝ} (hq : (1 : ℝ) / 2 ≤ q)
    (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (Hpb : kpb_PBiasedHC q)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      L ≤ StatMech.TwoDim.kklw_logMaxInfl p A) :
    1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A :=
  StatMech.TwoDim.kklw_sharpThreshold A hA hq hv0 hL hhalf (kpb_Hbkkkl Hpb) hvar hLL'







theorem kpb_sharpThreshold_window {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {q v₀ L ε : ℝ} (hq : (1 : ℝ) / 2 ≤ q)
    (hM : 0 < 2 * v₀ * L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (Hpb : kpb_PBiasedHC q)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      L ≤ StatMech.TwoDim.kklw_logMaxInfl p A)
    (hnotyet : StatMech.prob q A ≤ 1 - ε) :
    q - 1 / 2 ≤ (1 / 2 - ε) / (2 * v₀ * L) :=
  StatMech.TwoDim.kklw_sharpThreshold_window A hA hq hM hhalf hv0 hL (kpb_Hbkkkl Hpb)
    hvar hLL' hnotyet

end Probability

end StatMech
