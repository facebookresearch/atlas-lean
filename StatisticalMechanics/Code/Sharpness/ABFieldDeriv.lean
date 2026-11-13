/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Code.Inequalities.Russo
import Code.Sharpness.AizenmanBarskyUncond
import Code.Sharpness.BetaReparam

open MeasureTheory Set Finset Function
open scoped NNReal ENNReal

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace StatMech

namespace Sharpness

open ConfigSpace StatMech









variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def edgeWeightV (p : E → ℝ) (ω : ConfigSpace E) (e : E) : ℝ :=
  if ω e then p e else 1 - p e



noncomputable def configWeightV (p : E → ℝ) (ω : ConfigSpace E) : ℝ :=
  ∏ e, edgeWeightV p ω e


noncomputable def weightOffV (p : E → ℝ) (e : E) (ω : ConfigSpace E) : ℝ :=
  ∏ j ∈ univ.erase e, edgeWeightV p ω j



noncomputable def probV (p : E → ℝ) (A : Set (ConfigSpace E)) : ℝ :=
  ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * configWeightV p ω


noncomputable def pivotalProbV (p : E → ℝ) (A : Set (ConfigSpace E)) (e : E) : ℝ :=
  ∑ ω, (Set.indicator {ω | IsPivotal e A ω} (fun _ => (1 : ℝ)) ω) * configWeightV p ω




lemma configWeightV_eq (p : E → ℝ) (e : E) (ω : ConfigSpace E) :
    configWeightV p ω = edgeWeightV p ω e * weightOffV p e ω := by
  unfold configWeightV weightOffV
  rw [← Finset.mul_prod_erase univ _ (mem_univ e)]


lemma weightOffV_congr (p : E → ℝ) (e : E) {ω ω' : ConfigSpace E}
    (h : ∀ e', e' ≠ e → ω e' = ω' e') : weightOffV p e ω = weightOffV p e ω' := by
  unfold weightOffV
  apply Finset.prod_congr rfl
  intro j hj
  have hje : j ≠ e := (Finset.mem_erase.mp hj).1
  unfold edgeWeightV; rw [h j hje]



lemma weightOffV_update (p : E → ℝ) (e : E) (t : ℝ) (ω : ConfigSpace E) :
    weightOffV (Function.update p e t) e ω = weightOffV p e ω := by
  unfold weightOffV
  apply Finset.prod_congr rfl
  intro j hj
  have hje : j ≠ e := (Finset.mem_erase.mp hj).1
  unfold edgeWeightV
  rw [Function.update_of_ne hje]










lemma probV_update_eq (p : E → ℝ) (e₀ : E) (t : ℝ) (A : Set (ConfigSpace E)) :
    probV (Function.update p e₀ t) A
      = ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * ((if ω e₀ then t else 1 - t) * weightOffV p e₀ ω) := by
  unfold probV
  apply Finset.sum_congr rfl
  intro ω _
  rw [configWeightV_eq (Function.update p e₀ t) e₀ ω, weightOffV_update]
  congr 2
  unfold edgeWeightV
  rw [Function.update_self]

omit [Fintype E] [DecidableEq E] in


lemma hasDerivAt_singleEdgeFactor (ω : ConfigSpace E) (e₀ : E) (t : ℝ) :
    HasDerivAt (fun t => if ω e₀ then t else 1 - t) (if ω e₀ then (1 : ℝ) else -1) t := by
  by_cases h : ω e₀
  · simp only [h, if_true]; exact hasDerivAt_id t
  · simp only [h]
    simpa using (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)







lemma abfd_russo_per_eta (p : E → ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (e₀ : E) (ωt ωf : ConfigSpace E)
    (hwo : weightOffV p e₀ ωt = weightOffV p e₀ ωf)
    (hto : setOpen e₀ ωt = ωt) (htc : setClosed e₀ ωt = ωf)
    (ht : ωt e₀ = true) (hf : ωf e₀ = false) :
    {ω | IsPivotal e₀ A ω}.indicator (fun _ => (1 : ℝ)) ωt * configWeightV p ωt +
        {ω | IsPivotal e₀ A ω}.indicator (fun _ => (1 : ℝ)) ωf * configWeightV p ωf =
      A.indicator (fun _ => (1 : ℝ)) ωt
          * ((if ωt e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ωt) +
        A.indicator (fun _ => (1 : ℝ)) ωf
          * ((if ωf e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ωf) := by
  classical
  have hife : (if ωt e₀ then (1 : ℝ) else -1) = 1 := by rw [ht]; rfl
  have hiff : (if ωf e₀ then (1 : ℝ) else -1) = -1 := by rw [hf]; rfl
  rw [hife, hiff, configWeightV_eq p e₀ ωt, configWeightV_eq p e₀ ωf]
  have hewt : edgeWeightV p ωt e₀ = p e₀ := by unfold edgeWeightV; rw [ht]; rfl
  have hewf : edgeWeightV p ωf e₀ = 1 - p e₀ := by unfold edgeWeightV; rw [hf]; rfl
  rw [hewt, hewf, ← hwo]
  set w := weightOffV p e₀ ωt with hw
  have hpiv_eq : IsPivotal e₀ A ωt ↔ IsPivotal e₀ A ωf := by
    apply isPivotal_congr; intro e' he'; rw [← htc, setClosed_of_ne he']
  have hpiv_t : IsPivotal e₀ A ωt ↔ (ωf ∉ A ∧ ωt ∈ A) := by
    rw [isPivotal_iff_of_isIncreasing hA, hto, htc]
  have pivInd : ∀ ω, {ω | IsPivotal e₀ A ω}.indicator (fun _ => (1 : ℝ)) ω
      = if IsPivotal e₀ A ω then 1 else 0 := fun ω => by
    rw [Set.indicator_apply]; congr 1
  rw [pivInd ωt, pivInd ωf]
  by_cases hmt : ωt ∈ A <;> by_cases hmf : ωf ∈ A
  · have hnp : ¬ IsPivotal e₀ A ωt := by rw [hpiv_t]; tauto
    rw [Set.indicator_of_mem hmt, Set.indicator_of_mem hmf, if_neg hnp,
        if_neg (hpiv_eq.not.mp hnp)]; ring
  · have hp : IsPivotal e₀ A ωt := by rw [hpiv_t]; exact ⟨hmf, hmt⟩
    rw [Set.indicator_of_mem hmt, Set.indicator_of_notMem hmf, if_pos hp,
        if_pos (hpiv_eq.mp hp)]; ring
  · exfalso
    have hle : ωf ≤ ωt := by
      have := setClosed_le_setOpen e₀ ωt; rwa [htc, hto] at this
    exact hmt (hA hle hmf)
  · have hnp : ¬ IsPivotal e₀ A ωt := by rw [hpiv_t]; tauto
    rw [Set.indicator_of_notMem hmt, Set.indicator_of_notMem hmf, if_neg hnp,
        if_neg (hpiv_eq.not.mp hnp)]; ring









lemma abfd_russo_per_edge (p : E → ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (e₀ : E) :
    ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
        * ((if ω e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ω)
      = pivotalProbV p A e₀ := by
  
  rw [← Equiv.sum_comp (Equiv.funSplitAt e₀ Bool).symm
        (fun ω => A.indicator (fun _ => (1 : ℝ)) ω
          * ((if ω e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ω))]
  unfold pivotalProbV
  rw [← Equiv.sum_comp (Equiv.funSplitAt e₀ Bool).symm
        (fun ω => (Set.indicator {ω | IsPivotal e₀ A ω} (fun _ => (1 : ℝ)) ω)
          * configWeightV p ω)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro η _
  set ωt := (Equiv.funSplitAt e₀ Bool).symm (true, η) with hωt
  set ωf := (Equiv.funSplitAt e₀ Bool).symm (false, η) with hωf
  have ht : ωt e₀ = true := by rw [hωt]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hf : ωf e₀ = false := by rw [hωf]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hto : setOpen e₀ ωt = ωt := by
    funext j
    by_cases hj : j = e₀
    · subst hj; rw [setOpen_self, ht]
    · rw [setOpen_of_ne hj]
  have htc : setClosed e₀ ωt = ωf := by
    funext j
    by_cases hj : j = e₀
    · subst hj; rw [setClosed_self, hf]
    · rw [setClosed_of_ne hj, hωt, hωf]
      simp [Equiv.funSplitAt, Equiv.piSplitAt, hj]
  have hwo : weightOffV p e₀ ωt = weightOffV p e₀ ωf := by
    apply weightOffV_congr; intro e' he'
    rw [hωt, hωf]; simp [Equiv.funSplitAt, Equiv.piSplitAt, he']
  exact (abfd_russo_per_eta p A hA e₀ ωt ωf hwo hto htc ht hf).symm












theorem hasDerivAt_probV_single (p : E → ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (e₀ : E) :
    HasDerivAt (fun t => probV (Function.update p e₀ t) A) (pivotalProbV p A e₀) (p e₀) := by
  
  have hfun : (fun t => probV (Function.update p e₀ t) A)
      = fun t => ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * ((if ω e₀ then t else 1 - t) * weightOffV p e₀ ω) := by
    funext t; exact probV_update_eq p e₀ t A
  rw [hfun]
  
  have hderiv : HasDerivAt
      (fun t => ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * ((if ω e₀ then t else 1 - t) * weightOffV p e₀ ω))
      (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * ((if ω e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ω)) (p e₀) := by
    apply HasDerivAt.fun_sum
    intro ω _
    have h1 : HasDerivAt (fun t => (if ω e₀ then t else 1 - t) * weightOffV p e₀ ω)
        ((if ω e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ω) (p e₀) :=
      (hasDerivAt_singleEdgeFactor ω e₀ (p e₀)).mul_const _
    exact h1.const_mul (A.indicator (fun _ => (1 : ℝ)) ω)
  
  rw [← abfd_russo_per_edge p A hA e₀]
  exact hderiv
















noncomputable def paramOn (s : Finset E) (c : ℝ) (p : E → ℝ) : E → ℝ :=
  fun e => if e ∈ s then c else p e




lemma configWeightV_paramOn_factor (s : Finset E) (p : E → ℝ) (ω : ConfigSpace E) (c : ℝ) :
    configWeightV (paramOn s c p) ω
      = (∏ e ∈ s, (if ω e then c else 1 - c))
        * ∏ e ∈ univ \ s, (if ω e then p e else 1 - p e) := by
  unfold configWeightV edgeWeightV paramOn
  rw [← Finset.prod_filter_mul_prod_filter_not univ (· ∈ s)]
  congr 1
  · rw [show univ.filter (· ∈ s) = s by
          ext j; simp]
    apply Finset.prod_congr rfl
    intro e he; rw [if_pos he]
  · rw [show univ.filter (fun j => ¬ j ∈ s) = (univ \ s : Finset E) by
          ext j; simp]
    apply Finset.prod_congr rfl
    intro e he
    have : e ∉ s := (Finset.mem_sdiff.mp he).2
    rw [if_neg this]



lemma weightOffV_paramOn_mem (s : Finset E) (p : E → ℝ) (ω : ConfigSpace E) (c : ℝ)
    {e : E} (he : e ∈ s) :
    weightOffV (paramOn s c p) e ω
      = (∏ j ∈ s.erase e, (if ω j then c else 1 - c))
        * ∏ j ∈ univ \ s, (if ω j then p j else 1 - p j) := by
  unfold weightOffV edgeWeightV paramOn
  
  rw [← Finset.prod_filter_mul_prod_filter_not (univ.erase e) (· ∈ s)]
  congr 1
  · 
    rw [show (univ.erase e).filter (· ∈ s) = s.erase e by
          ext j
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ]
          tauto]
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_pos (Finset.mem_of_mem_erase hj)]
  · 
    rw [show (univ.erase e).filter (fun j => ¬ j ∈ s) = (univ \ s : Finset E) by
          ext j
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
            Finset.mem_sdiff]
          constructor
          · rintro ⟨_, hj⟩; exact ⟨trivial, hj⟩
          · rintro ⟨_, hj⟩
            refine ⟨⟨?_, trivial⟩, hj⟩
            rintro rfl; exact hj he]
    apply Finset.prod_congr rfl
    intro j hj
    have : j ∉ s := (Finset.mem_sdiff.mp hj).2
    rw [if_neg this]















theorem hasDerivAt_probV_paramOn (s : Finset E) (p : E → ℝ) (A : Set (ConfigSpace E))
    (hA : IsIncreasing A) (c : ℝ) :
    HasDerivAt (fun c => probV (paramOn s c p) A)
      (∑ e ∈ s, pivotalProbV (paramOn s c p) A e) c := by
  
  
  set off : ConfigSpace E → ℝ :=
    fun ω => ∏ e ∈ univ \ s, (if ω e then p e else 1 - p e) with hoff
  have hfun : (fun c => probV (paramOn s c p) A)
      = fun c => ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * ((∏ e ∈ s, (if ω e then c else 1 - c)) * off ω) := by
    funext c
    unfold probV
    apply Finset.sum_congr rfl
    intro ω _
    rw [configWeightV_paramOn_factor s p ω c]
  rw [hfun]
  
  
  have hderiv : HasDerivAt
      (fun c => ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * ((∏ e ∈ s, (if ω e then c else 1 - c)) * off ω))
      (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * ((∑ e ∈ s, (if ω e then (1 : ℝ) else -1)
              * ∏ j ∈ s.erase e, (if ω j then c else 1 - c)) * off ω)) c := by
    apply HasDerivAt.fun_sum
    intro ω _
    
    have hprod : HasDerivAt (fun c => ∏ e ∈ s, (if ω e then c else 1 - c))
        (∑ e ∈ s, (if ω e then (1 : ℝ) else -1)
            * ∏ j ∈ s.erase e, (if ω j then c else 1 - c)) c := by
      have h := HasDerivAt.finsetProd (u := s)
        (f := fun e c => if ω e then c else 1 - c)
        (f' := fun e => if ω e then (1 : ℝ) else -1)
        (fun e _ => hasDerivAt_singleEdgeFactor ω e c)
      simp only [smul_eq_mul] at h
      convert h using 1
      · funext q; simp [Finset.prod_apply]
      · apply Finset.sum_congr rfl
        intro e he
        by_cases hωe : ω e = true <;> simp [hωe]
    exact ((hprod.mul_const (off ω)).const_mul (A.indicator (fun _ => (1 : ℝ)) ω))
  
  convert hderiv using 1
  
  
  have hrewrite : (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
        * ((∑ e ∈ s, (if ω e then (1 : ℝ) else -1)
            * ∏ j ∈ s.erase e, (if ω j then c else 1 - c)) * off ω))
      = ∑ ω, ∑ e ∈ s, A.indicator (fun _ => (1 : ℝ)) ω
          * ((if ω e then (1 : ℝ) else -1) * weightOffV (paramOn s c p) e ω) := by
    apply Finset.sum_congr rfl
    intro ω _
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [weightOffV_paramOn_mem s p ω c he, hoff]
    ring
  rw [hrewrite, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  exact (abfd_russo_per_edge (paramOn s c p) A hA e).symm







omit [DecidableEq E] in


lemma configWeightV_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (ω : ConfigSpace E) :
    0 ≤ configWeightV p ω := by
  unfold configWeightV edgeWeightV
  apply Finset.prod_nonneg
  intro e _
  by_cases h : ω e = true
  · rw [if_pos h]; exact (hp e).1
  · rw [if_neg h]; linarith [(hp e).2]



lemma pivotalProbV_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (A : Set (ConfigSpace E)) (e : E) : 0 ≤ pivotalProbV p A e := by
  unfold pivotalProbV
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg _ (configWeightV_nonneg p hp ω)
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω













noncomputable def qField (h : ℝ) : ℝ := 1 - Real.exp (-h)


lemma hasDerivAt_qField (h : ℝ) : HasDerivAt qField (Real.exp (-h)) h := by
  unfold qField
  have h1 : HasDerivAt (fun h : ℝ => Real.exp (-h)) (Real.exp (-h) * (-1)) h :=
    (Real.hasDerivAt_exp (-h)).comp h (by simpa using (hasDerivAt_id h).neg)
  have h2 : HasDerivAt (fun h : ℝ => 1 - Real.exp (-h)) (-(Real.exp (-h) * (-1))) h := by
    simpa using (hasDerivAt_const h (1 : ℝ)).sub h1
  convert h2 using 1; ring


lemma qField_mem (h : ℝ) (hh : 0 ≤ h) : 0 ≤ qField h ∧ qField h ≤ 1 := by
  unfold qField
  have hle1 : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpos : 0 < Real.exp (-h) := Real.exp_pos _
  exact ⟨by linarith, by linarith⟩








theorem hasDerivAt_field_profile (s : Finset E) (p : E → ℝ) (A : Set (ConfigSpace E))
    (hA : IsIncreasing A) (h : ℝ) :
    HasDerivAt (fun h => probV (paramOn s (qField h) p) A)
      ((∑ e ∈ s, pivotalProbV (paramOn s (qField h) p) A e) * Real.exp (-h)) h := by
  have hcomp := (hasDerivAt_probV_paramOn s p A hA (qField h)).comp h (hasDerivAt_qField h)
  simpa [Function.comp] using hcomp


theorem deriv_field_profile (s : Finset E) (p : E → ℝ) (A : Set (ConfigSpace E))
    (hA : IsIncreasing A) (h : ℝ) :
    deriv (fun h => probV (paramOn s (qField h) p) A) h
      = ∑ e ∈ s, pivotalProbV (paramOn s (qField h) p) A e * Real.exp (-h) := by
  rw [(hasDerivAt_field_profile s p A hA h).deriv, Finset.sum_mul]










theorem abfd_field_influence_sum (s : Finset E) (p : E → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (h : ℝ) (hh : 0 ≤ h) :
    let infl := fun e => pivotalProbV (paramOn s (qField h) p) A e * Real.exp (-h)
    (∑ e ∈ s, infl e = deriv (fun h => probV (paramOn s (qField h) p) A) h) ∧
      (∀ e ∈ s, 0 ≤ infl e) ∧
      (0 ≤ deriv (fun h => probV (paramOn s (qField h) p) A) h) := by
  intro infl
  
  have hqmem := qField_mem h hh
  have hparam : ∀ e, 0 ≤ paramOn s (qField h) p e ∧ paramOn s (qField h) p e ≤ 1 := by
    intro e; unfold paramOn; by_cases he : e ∈ s
    · rw [if_pos he]; exact hqmem
    · rw [if_neg he]; exact hp e
  have hinfl_nn : ∀ e ∈ s, 0 ≤ infl e := by
    intro e _
    exact mul_nonneg (pivotalProbV_nonneg _ hparam A e) (le_of_lt (Real.exp_pos _))
  refine ⟨?_, hinfl_nn, ?_⟩
  · rw [deriv_field_profile s p A hA h]
  · rw [deriv_field_profile s p A hA h]
    exact Finset.sum_nonneg hinfl_nn
















end Sharpness










namespace Sharpness

open ConfigSpace StatMech

variable {E : Type} [Fintype E] [DecidableEq E]


























theorem abfd_aizenmanBarsky_of_core (s : Finset E) (p : ℝ → E → ℝ)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (J : ℝ) (hJ0 : 0 ≤ J) (Jcoef : E → ℝ)
    (hJnn : ∀ e ∈ s, 0 ≤ Jcoef e) (hJle : ∀ e ∈ s, Jcoef e ≤ J)
    (hJsum : ∑ e ∈ s, Jcoef e = J)
    (piv : ℝ → ℝ → E → ℝ)
    (M : ℝ → ℝ → ℝ)
    (hM : M = fun β h => probV (paramOn s (qField h) (p β)) A)
    (hMnn : ∀ β h, 0 ≤ M β h)
    (hβrusso : ∀ β h, deriv (fun β => M β h) β = ∑ e ∈ s, piv β h e)
    (hbk : ∀ β h, ∀ e ∈ s, piv β h e ≤
      Jcoef e * M β h * (pivotalProbV (paramOn s (qField h) (p β)) A e * Real.exp (-h)))
    (hfield_nn : ∀ β h,
      (∀ e ∈ s, 0 ≤ pivotalProbV (paramOn s (qField h) (p β)) A e * Real.exp (-h))
      ∧ (0 ≤ deriv (fun h => M β h) h)) :
    AizenmanBarskyInequality M J := by
  apply aizenmanBarsky_of_geometricCore_and_inputs M J hJ0
  intro β h
  obtain ⟨hinfl_nn, hdMdh_nn⟩ := hfield_nn β h
  
  have hMfield : (fun h => M β h) = fun h => probV (paramOn s (qField h) (p β)) A := by
    funext h'; rw [hM]
  have hinfl_eq : ∑ e ∈ s, pivotalProbV (paramOn s (qField h) (p β)) A e * Real.exp (-h)
      = deriv (fun h => M β h) h := by
    rw [hMfield, deriv_field_profile s (p β) A hA h]
  exact ⟨E, s, Jcoef,
    fun e => pivotalProbV (paramOn s (qField h) (p β)) A e * Real.exp (-h),
    fun e => piv β h e, hMnn β h, hJnn, hinfl_nn, hβrusso β h, hbk β h, hJsum,
    hinfl_eq, hJle, hdMdh_nn⟩










theorem abfd_hfield_nn_eq_M2 (s : Finset E) (p : ℝ → E → ℝ)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (hp : ∀ β e, 0 ≤ p β e ∧ p β e ≤ 1)
    (β h : ℝ) (hh : 0 ≤ h) :
    (∀ e ∈ s, 0 ≤ pivotalProbV (paramOn s (qField h) (p β)) A e * Real.exp (-h))
    ∧ (0 ≤ deriv (fun h => probV (paramOn s (qField h) (p β)) A) h) := by
  have hM2 := abfd_field_influence_sum s (p β) (hp β) A hA h hh
  simp only at hM2
  exact ⟨hM2.2.1, hM2.2.2⟩

end Sharpness

end StatMech
