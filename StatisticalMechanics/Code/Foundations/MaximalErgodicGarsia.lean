/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib

open MeasureTheory Filter Finset Function
open scoped Topology

namespace StatMech

namespace GarsiaMax

variable {α : Type*} {T : α → α} {f : α → ℝ}









noncomputable def maxPartialSum (T : α → α) (f : α → ℝ) (N : ℕ) (hN : 1 ≤ N) (x : α) : ℝ :=
  (Finset.Icc 1 N).sup' (by rw [Finset.nonempty_Icc]; exact hN)
    (fun n => birkhoffSum T f n x)


theorem birkhoffSum_le_maxPartialSum {N : ℕ} (hN : 1 ≤ N) {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ N)
    (x : α) : birkhoffSum T f n x ≤ maxPartialSum T f N hN x :=
  Finset.le_sup' (fun n => birkhoffSum T f n x) (Finset.mem_Icc.mpr ⟨hn1, hn2⟩)


theorem exists_eq_maxPartialSum {N : ℕ} (hN : 1 ≤ N) (x : α) :
    ∃ n, 1 ≤ n ∧ n ≤ N ∧ birkhoffSum T f n x = maxPartialSum T f N hN x := by
  obtain ⟨n, hn, hneq⟩ :=
    Finset.exists_mem_eq_sup' (s := Finset.Icc 1 N)
      (by rw [Finset.nonempty_Icc]; exact hN) (fun n => birkhoffSum T f n x)
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  exact ⟨n, hn1, hn2, hneq.symm⟩












theorem birkhoffSum_le_add_posPart_maxPartialSum {N : ℕ} (hN : 1 ≤ N) {n : ℕ}
    (hn1 : 1 ≤ n) (hn2 : n ≤ N) (x : α) :
    birkhoffSum T f n x ≤ f x + max (maxPartialSum T f N hN (T x)) 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
  
  simp only [Nat.zero_add] at hn2 ⊢
  rw [birkhoffSum_succ' T f m x]
  
  have key : birkhoffSum T f m (T x) ≤ max (maxPartialSum T f N hN (T x)) 0 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · 
      subst hm0
      rw [birkhoffSum_zero]
      exact le_max_right _ _
    · 
      have hmN : m ≤ N := Nat.le_of_succ_le_succ (Nat.le_succ_of_le hn2)
      calc birkhoffSum T f m (T x)
          ≤ maxPartialSum T f N hN (T x) :=
            birkhoffSum_le_maxPartialSum hN hmpos hmN (T x)
        _ ≤ max (maxPartialSum T f N hN (T x)) 0 := le_max_left _ _
  linarith




theorem maxPartialSum_le_add_posPart {N : ℕ} (hN : 1 ≤ N) (x : α) :
    maxPartialSum T f N hN x ≤ f x + max (maxPartialSum T f N hN (T x)) 0 := by
  obtain ⟨n, hn1, hn2, hneq⟩ := exists_eq_maxPartialSum hN x
  calc maxPartialSum T f N hN x = birkhoffSum T f n x := hneq.symm
    _ ≤ f x + max (maxPartialSum T f N hN (T x)) 0 :=
        birkhoffSum_le_add_posPart_maxPartialSum hN hn1 hn2 x



section MeasureTheory

variable [MeasurableSpace α] {μ : Measure α}


theorem integrable_comp_iterate (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (k : ℕ) :
    Integrable (fun x => f (T^[k] x)) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.comp_measurePreserving (hT.iterate k)


theorem integrable_birkhoffSum (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (fun x => birkhoffSum T f n x) μ := by
  simp only [birkhoffSum]
  exact integrable_finsetSum _ fun i _ => integrable_comp_iterate hT hf i

omit [MeasurableSpace α] in


theorem maxPartialSum_eq_sup'_fun {N : ℕ} (hN : 1 ≤ N) :
    (fun x => maxPartialSum T f N hN x) =
      (Finset.Icc 1 N).sup' (by rw [Finset.nonempty_Icc]; exact hN)
        (fun n => fun x => birkhoffSum T f n x) := by
  funext x
  rw [Finset.sup'_apply]
  rfl



theorem integrable_maxPartialSum (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) {N : ℕ}
    (hN : 1 ≤ N) : Integrable (fun x => maxPartialSum T f N hN x) μ := by
  rw [maxPartialSum_eq_sup'_fun hN]
  refine Finset.sup'_induction (p := fun g => Integrable g μ) _ _
    (fun _ hg _ hh => hg.sup hh) (fun n _ => ?_)
  exact integrable_birkhoffSum hT hf n


theorem integrable_posPart_maxPartialSum (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun x => max (maxPartialSum T f N hN x) 0) μ :=
  (integrable_maxPartialSum hT hf hN).pos_part


theorem integrable_posPart_maxPartialSum_comp (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun x => max (maxPartialSum T f N hN (T x)) 0) μ := by
  have h := integrable_posPart_maxPartialSum hT hf hN
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.comp_measurePreserving hT



theorem integral_comp_eq (hT : MeasurePreserving T μ μ) {g : α → ℝ}
    (hg : AEStronglyMeasurable g μ) :
    ∫ x, g (T x) ∂μ = ∫ x, g x ∂μ := by
  conv_rhs => rw [← hT.map_eq]
  rw [integral_map hT.measurable.aemeasurable (by rwa [hT.map_eq])]


theorem integral_posPart_maxPartialSum_comp (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    {N : ℕ} (hN : 1 ≤ N) :
    ∫ x, max (maxPartialSum T f N hN (T x)) 0 ∂μ
      = ∫ x, max (maxPartialSum T f N hN x) 0 ∂μ :=
  integral_comp_eq hT (integrable_posPart_maxPartialSum hT hf hN).aestronglyMeasurable














theorem garsia_maximal_inequality (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ ∫ x in {x | 0 < maxPartialSum T f N hN x}, f x ∂μ := by
  
  set Mp : α → ℝ := fun x => max (maxPartialSum T f N hN x) 0 with hMp
  set MpT : α → ℝ := fun x => max (maxPartialSum T f N hN (T x)) 0 with hMpT
  set E : Set α := {x | 0 < maxPartialSum T f N hN x} with hE
  
  have hMp_int : Integrable Mp μ := integrable_posPart_maxPartialSum hT hf hN
  have hMpT_int : Integrable MpT μ := integrable_posPart_maxPartialSum_comp hT hf hN
  have hMsub_int : Integrable (fun x => Mp x - MpT x) μ := hMp_int.sub hMpT_int
  
  have hM_int : Integrable (fun x => maxPartialSum T f N hN x) μ :=
    integrable_maxPartialSum hT hf hN
  have hE_meas : NullMeasurableSet E μ :=
    nullMeasurableSet_lt aemeasurable_const hM_int.aestronglyMeasurable.aemeasurable
  
  have step1 : ∫ x in E, (Mp x - MpT x) ∂μ ≤ ∫ x in E, f x ∂μ := by
    refine setIntegral_mono_ae_restrict hMsub_int.integrableOn hf.integrableOn ?_
    rw [EventuallyLE, ae_restrict_iff'₀ hE_meas]
    refine Eventually.of_forall fun x hx => ?_
    
    have hkey := maxPartialSum_le_add_posPart (T := T) (f := f) (N := N) hN x
    have hxpos : (0 : ℝ) < maxPartialSum T f N hN x := hx
    have hMp_x : Mp x = maxPartialSum T f N hN x := by
      simp only [hMp]; exact max_eq_left (le_of_lt hxpos)
    simp only [hMp, hMpT] at *
    rw [hMp_x]; linarith
  
  have step2 : ∫ x in E, (Mp x - MpT x) ∂μ = (∫ x in E, Mp x ∂μ) - ∫ x in E, MpT x ∂μ :=
    integral_sub hMp_int.integrableOn hMpT_int.integrableOn
  
  have hMp_off : ∀ x, x ∉ E → Mp x = 0 := by
    intro x hx
    simp only [hE, Set.mem_setOf_eq, not_lt] at hx
    simp only [hMp]; exact max_eq_right hx
  have step3 : ∫ x in E, Mp x ∂μ = ∫ x, Mp x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hMp_off
  
  have hMpT_nonneg : 0 ≤ᵐ[μ] MpT :=
    Eventually.of_forall fun x => le_max_right _ _
  have step4 : ∫ x in E, MpT x ∂μ ≤ ∫ x, MpT x ∂μ :=
    setIntegral_le_integral hMpT_int hMpT_nonneg
  
  have step5 : ∫ x, MpT x ∂μ = ∫ x, Mp x ∂μ := integral_posPart_maxPartialSum_comp hT hf hN
  
  calc (0 : ℝ) = (∫ x, Mp x ∂μ) - ∫ x, Mp x ∂μ := by ring
    _ = (∫ x, Mp x ∂μ) - ∫ x, MpT x ∂μ := by rw [step5]
    _ ≤ (∫ x in E, Mp x ∂μ) - ∫ x in E, MpT x ∂μ := by rw [step3]; linarith [step4]
    _ = ∫ x in E, (Mp x - MpT x) ∂μ := step2.symm
    _ ≤ ∫ x in E, f x ∂μ := step1

end MeasureTheory

end GarsiaMax

end StatMech
