/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































import Mathlib
import Code.Foundations.ConfigSpace
import Code.FK.RandomCluster
import Code.FK.FiniteEnergy
import Code.Inequalities.Pivotal

open scoped BigOperators

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]



















theorem fkWeight_setClosed_ge {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    cFE p q * (fkWeight G p q (setOpen e ω) + fkWeight G p q (setClosed e ω))
      ≤ fkWeight G p q (setClosed e ω) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  by_cases he : e ∈ G.edgeFinset
  · have hW1pos : 0 < fkWeight G p q (setOpen e ω) := fkWeight_pos G hp hp1 hq0 _
    have hW0pos : 0 < fkWeight G p q (setClosed e ω) := fkWeight_pos G hp hp1 hq0 _
    have hlo : (1 - p) * fkWeight G p q (setOpen e ω) ≤ p * fkWeight G p q (setClosed e ω) :=
      fkWeight_lo G hp hp1 hq he ω
    
    have hcfe : cFE p q ≤ 1 - p := min_le_right _ _
    have hkey : (1 - p) * (fkWeight G p q (setOpen e ω) + fkWeight G p q (setClosed e ω))
        ≤ fkWeight G p q (setClosed e ω) := by nlinarith
    have hsum : (0 : ℝ) ≤ fkWeight G p q (setOpen e ω) + fkWeight G p q (setClosed e ω) := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hcfe hsum]
  · 
    
    have hep : edgeProduct G p (setOpen e ω) = edgeProduct G p (setClosed e ω) := by
      unfold edgeProduct
      apply Finset.prod_congr rfl
      intro e' he'
      have hne : e' ≠ e := fun h => he (h ▸ he')
      rw [setOpen_of_ne hne, setClosed_of_ne hne]
    have hk : numClusters G (setOpen e ω) = numClusters G (setClosed e ω) :=
      numClusters_congr_openSub G (openSub_setOpen_eq_setClosed_of_notMem G he ω)
    have hweq : fkWeight G p q (setOpen e ω) = fkWeight G p q (setClosed e ω) := by
      unfold fkWeight; rw [hep, hk]
    have hcfe : cFE p q ≤ 1 / 2 := cFE_le_half hp hp1 hq
    have hW0pos : 0 < fkWeight G p q (setClosed e ω) := fkWeight_pos G hp hp1 hq0 _
    rw [hweq]
    nlinarith [mul_le_mul_of_nonneg_right hcfe
      (by linarith : (0 : ℝ) ≤ fkWeight G p q (setClosed e ω) + fkWeight G p q (setClosed e ω))]














noncomputable def closeAllOn (γ : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ConfigSpace (Sym2 V) := fun e => if e ∈ γ then false else ψ e

omit [Fintype V] in
@[simp] theorem closeAllOn_of_mem {γ : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ γ)
    (ψ : ConfigSpace (Sym2 V)) : closeAllOn γ ψ e = false := by simp [closeAllOn, he]

omit [Fintype V] in
theorem closeAllOn_of_not_mem {γ : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ γ)
    (ψ : ConfigSpace (Sym2 V)) : closeAllOn γ ψ e = ψ e := by simp [closeAllOn, he]

omit [Fintype V] in


theorem closeAllOn_setClosed {e : Sym2 V} {γ : Finset (Sym2 V)} (he : e ∉ γ)
    (ψ : ConfigSpace (Sym2 V)) :
    closeAllOn γ (setClosed e ψ) = setClosed e (closeAllOn γ ψ) := by
  funext x
  by_cases hx : x = e
  · subst hx; simp only [setClosed_self, closeAllOn, if_neg he]
  · rw [setClosed_of_ne hx]
    simp only [closeAllOn]
    by_cases hxg : x ∈ γ
    · simp [hxg]
    · rw [if_neg hxg, if_neg hxg, setClosed_of_ne hx]

omit [Fintype V] in


theorem closeAllOn_setOpen {e : Sym2 V} {γ : Finset (Sym2 V)} (he : e ∉ γ)
    (ψ : ConfigSpace (Sym2 V)) :
    closeAllOn γ (setOpen e ψ) = setOpen e (closeAllOn γ ψ) := by
  funext x
  by_cases hx : x = e
  · subst hx; simp only [setOpen_self, closeAllOn, if_neg he]
  · rw [setOpen_of_ne hx]
    simp only [closeAllOn]
    by_cases hxg : x ∈ γ
    · simp [hxg]
    · rw [if_neg hxg, if_neg hxg, setOpen_of_ne hx]





noncomputable def agreeWeightSum (p q : ℝ) (γ : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ℝ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : ConfigSpace (Sym2 V) => ∀ e' ∉ γ, σ e' = ψ e'),
    fkWeight G p q σ



theorem agreeWeightSum_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (γ : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    0 < agreeWeightSum G p q γ ψ := by
  unfold agreeWeightSum
  exact Finset.sum_pos (fun σ _ => fkWeight_pos G hp hp1 hq σ) ⟨ψ, by simp⟩








theorem agreeWeightSum_insert (p q : ℝ) {e : Sym2 V} {γ : Finset (Sym2 V)} (he : e ∉ γ)
    (ψ : ConfigSpace (Sym2 V)) :
    agreeWeightSum G p q (insert e γ) ψ
      = agreeWeightSum G p q γ (setClosed e ψ) + agreeWeightSum G p q γ (setOpen e ψ) := by
  classical
  unfold agreeWeightSum
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun σ => σ e = false)]
  congr 1
  · apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hfree, h0⟩
      intro e' he'
      by_cases hee : e' = e
      · subst hee; rw [h0, setClosed_self]
      · rw [setClosed_of_ne hee]; exact hfree e' (by simp [Finset.mem_insert, hee, he'])
    · intro hfree
      refine ⟨fun e' he' => ?_, ?_⟩
      · have hne : e' ≠ e := fun h => he' (h ▸ Finset.mem_insert_self e γ)
        have := hfree e' (fun hc => he' (Finset.mem_insert_of_mem hc))
        rwa [setClosed_of_ne hne] at this
      · have := hfree e (by simpa using he)
        rwa [setClosed_self] at this
  · apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_false]
    constructor
    · rintro ⟨hfree, h1⟩
      intro e' he'
      by_cases hee : e' = e
      · subst hee; rw [h1, setOpen_self]
      · rw [setOpen_of_ne hee]; exact hfree e' (by simp [Finset.mem_insert, hee, he'])
    · intro hfree
      refine ⟨fun e' he' => ?_, ?_⟩
      · have hne : e' ≠ e := fun h => he' (h ▸ Finset.mem_insert_self e γ)
        have := hfree e' (fun hc => he' (Finset.mem_insert_of_mem hc))
        rwa [setOpen_of_ne hne] at this
      · have := hfree e (by simpa using he)
        rwa [setOpen_self] at this



theorem agreeWeightSum_empty (p q : ℝ) (ψ : ConfigSpace (Sym2 V)) :
    agreeWeightSum G p q ∅ ψ = fkWeight G p q ψ := by
  classical
  unfold agreeWeightSum
  rw [show (Finset.univ.filter
      (fun σ : ConfigSpace (Sym2 V) => ∀ e' ∉ (∅ : Finset (Sym2 V)), σ e' = ψ e')) = {ψ}
      from ?_]
  · simp
  · ext σ
    simp only [Finset.notMem_empty, not_false_eq_true, forall_const, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; funext e'; exact h e'
    · rintro rfl; intro e'; rfl












theorem cFE_pow_mul_agreeWeightSum_le {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (γ : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    cFE p q ^ γ.card * agreeWeightSum G p q γ ψ ≤ fkWeight G p q (closeAllOn γ ψ) := by
  classical
  induction γ using Finset.induction generalizing ψ with
  | empty =>
    rw [Finset.card_empty, pow_zero, one_mul, agreeWeightSum_empty]
    
    have : closeAllOn (∅ : Finset (Sym2 V)) ψ = ψ := by funext x; simp [closeAllOn]
    rw [this]
  | @insert e γ he ih =>
    rw [Finset.card_insert_of_notMem he, pow_succ, agreeWeightSum_insert G p q he]
    have hcfe_nonneg : (0 : ℝ) ≤ cFE p q := (cFE_pos hp hp1 hq).le
    
    have ihc := ih (setClosed e ψ)
    have iho := ih (setOpen e ψ)
    
    have hc : fkWeight G p q (closeAllOn γ (setClosed e ψ))
        = fkWeight G p q (setClosed e (closeAllOn γ ψ)) := by rw [closeAllOn_setClosed he]
    have ho : fkWeight G p q (closeAllOn γ (setOpen e ψ))
        = fkWeight G p q (setOpen e (closeAllOn γ ψ)) := by rw [closeAllOn_setOpen he]
    
    have htarget : closeAllOn (insert e γ) ψ = setClosed e (closeAllOn γ ψ) := by
      funext x
      by_cases hx : x = e
      · subst hx; simp [closeAllOn, setClosed_self]
      · rw [setClosed_of_ne hx]
        simp only [closeAllOn, Finset.mem_insert, hx, false_or]
    rw [htarget]
    calc cFE p q ^ γ.card * cFE p q
            * (agreeWeightSum G p q γ (setClosed e ψ) + agreeWeightSum G p q γ (setOpen e ψ))
        = cFE p q * (cFE p q ^ γ.card * agreeWeightSum G p q γ (setClosed e ψ)
              + cFE p q ^ γ.card * agreeWeightSum G p q γ (setOpen e ψ)) := by ring
      _ ≤ cFE p q * (fkWeight G p q (closeAllOn γ (setClosed e ψ))
              + fkWeight G p q (closeAllOn γ (setOpen e ψ))) := by
            apply mul_le_mul_of_nonneg_left _ hcfe_nonneg
            exact add_le_add ihc iho
      _ = cFE p q * (fkWeight G p q (setClosed e (closeAllOn γ ψ))
              + fkWeight G p q (setOpen e (closeAllOn γ ψ))) := by rw [hc, ho]
      _ = cFE p q * (fkWeight G p q (setOpen e (closeAllOn γ ψ))
              + fkWeight G p q (setClosed e (closeAllOn γ ψ))) := by ring
      _ ≤ fkWeight G p q (setClosed e (closeAllOn γ ψ)) :=
            fkWeight_setClosed_ge G hp hp1 hq e (closeAllOn γ ψ)









theorem cFE_pow_le_condClosedOn {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (γ : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    cFE p q ^ γ.card ≤ fkWeight G p q (closeAllOn γ ψ) / agreeWeightSum G p q γ ψ := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  rw [le_div_iff₀ (agreeWeightSum_pos G hp hp1 hq0 γ ψ)]
  exact cFE_pow_mul_agreeWeightSum_le G hp hp1 hq γ ψ









noncomputable def closedMass (p q : ℝ) (γ : Finset (Sym2 V)) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ∀ e ∈ γ, ω e = false),
    fkProb G p q ω


theorem closedMass_empty {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    closedMass G p q ∅ = 1 := by
  classical
  unfold closedMass
  rw [show (Finset.univ.filter
      (fun ω : ConfigSpace (Sym2 V) => ∀ e ∈ (∅ : Finset (Sym2 V)), ω e = false))
      = Finset.univ from by ext ω; simp]
  exact fkProb_sum_eq_one G hp hp1 hq




noncomputable def cfib (e : Sym2 V) (γ : Finset (Sym2 V)) :
    Finset (ConfigSpace (Sym2 V)) :=
  Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false ∧ ∀ e' ∈ γ, ψ e' = false)






theorem closedMass_reindex {p q : ℝ} (e : Sym2 V) {γ : Finset (Sym2 V)} (he : e ∉ γ) :
    closedMass G p q γ
      = ∑ ψ ∈ cfib e γ,
          (fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ)) := by
  classical
  unfold closedMass cfib
  rw [Finset.sum_add_distrib]
  have hclosed : (∑ ψ ∈ Finset.univ.filter
        (fun ψ : ConfigSpace (Sym2 V) => ψ e = false ∧ ∀ e' ∈ γ, ψ e' = false),
        fkProb G p q (setClosed e ψ))
      = ∑ ω ∈ Finset.univ.filter
          (fun ω : ConfigSpace (Sym2 V) => (∀ e' ∈ γ, ω e' = false) ∧ ω e = false),
          fkProb G p q ω := by
    apply Finset.sum_nbij' (fun ψ => ψ) (fun ω => ω)
    · intro ψ hψ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢
      exact ⟨hψ.2, hψ.1⟩
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact ⟨hω.2, hω.1⟩
    · intro ψ _; rfl
    · intro ω _; rfl
    · intro ψ hψ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ
      congr 1
      funext x; by_cases hx : x = e
      · subst hx; simp [hψ.1]
      · rw [setClosed_of_ne hx]
  have hopen : (∑ ψ ∈ Finset.univ.filter
        (fun ψ : ConfigSpace (Sym2 V) => ψ e = false ∧ ∀ e' ∈ γ, ψ e' = false),
        fkProb G p q (setOpen e ψ))
      = ∑ ω ∈ Finset.univ.filter
          (fun ω : ConfigSpace (Sym2 V) => (∀ e' ∈ γ, ω e' = false) ∧ ω e = true),
          fkProb G p q ω := by
    apply Finset.sum_nbij' (fun ψ => setOpen e ψ) (fun ω => setClosed e ω)
    · intro ψ hψ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢
      refine ⟨fun e' he' => ?_, by simp⟩
      have hne : e' ≠ e := fun h => he (h ▸ he')
      rw [setOpen_of_ne hne]; exact hψ.2 e' he'
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      refine ⟨by simp, fun e' he' => ?_⟩
      have hne : e' ≠ e := fun h => he (h ▸ he')
      rw [setClosed_of_ne hne]; exact hω.1 e' he'
    · intro ψ hψ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ
      funext x; by_cases hx : x = e
      · subst hx; simp [hψ.1]
      · rw [setClosed_of_ne hx, setOpen_of_ne hx]
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      funext x; by_cases hx : x = e
      · subst hx; simp [hω.2]
      · rw [setOpen_of_ne hx, setClosed_of_ne hx]
    · intro ψ _; rfl
  rw [hopen, hclosed]
  have hset1 : (Finset.univ.filter
        (fun ω : ConfigSpace (Sym2 V) => (∀ e' ∈ γ, ω e' = false) ∧ ω e = true))
      = (Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ∀ e' ∈ γ, ω e' = false)).filter
          (fun ω => ¬ ω e = false) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_false]
  have hset0 : (Finset.univ.filter
        (fun ω : ConfigSpace (Sym2 V) => (∀ e' ∈ γ, ω e' = false) ∧ ω e = false))
      = (Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ∀ e' ∈ γ, ω e' = false)).filter
          (fun ω => ω e = false) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hset1, hset0, add_comm]
  exact (Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ∀ e' ∈ γ, ω e' = false))
        (fun ω => ω e = false) (fkProb G p q)).symm




theorem closedMass_insert_reindex {p q : ℝ} (e : Sym2 V) {γ : Finset (Sym2 V)} (he : e ∉ γ) :
    closedMass G p q (insert e γ)
      = ∑ ψ ∈ cfib e γ, fkProb G p q (setClosed e ψ) := by
  classical
  unfold closedMass cfib
  apply Finset.sum_nbij' (fun ω => ω) (fun ψ => ψ)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert] at hω ⊢
    exact ⟨hω.1, hω.2⟩
  · intro ψ hψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert] at hψ ⊢
    exact ⟨hψ.1, hψ.2⟩
  · intro ω _; rfl
  · intro ψ _; rfl
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert] at hω
    congr 1
    funext x; by_cases hx : x = e
    · subst hx; simp [hω.1]
    · rw [setClosed_of_ne hx]





theorem cFE_mul_closedMass_le_insert {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 V) {γ : Finset (Sym2 V)} (he : e ∉ γ) :
    cFE p q * closedMass G p q γ ≤ closedMass G p q (insert e γ) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  rw [closedMass_reindex G e he, closedMass_insert_reindex G e he, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ψ _
  
  have hZpos : 0 < fkZ G p q := fkZ_pos G hp hp1 hq0
  have hwt : cFE p q * (fkWeight G p q (setOpen e ψ) + fkWeight G p q (setClosed e ψ))
      ≤ fkWeight G p q (setClosed e ψ) := fkWeight_setClosed_ge G hp hp1 hq e ψ
  unfold fkProb
  rw [← add_div]
  rw [show cFE p q * ((fkWeight G p q (setOpen e ψ) + fkWeight G p q (setClosed e ψ)) / fkZ G p q)
      = (cFE p q * (fkWeight G p q (setOpen e ψ) + fkWeight G p q (setClosed e ψ))) / fkZ G p q
      from by ring]
  exact (div_le_div_iff_of_pos_right hZpos).mpr hwt















theorem cFE_pow_le_closedMass {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (γ : Finset (Sym2 V)) :
    cFE p q ^ γ.card ≤ closedMass G p q γ := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  classical
  induction γ using Finset.induction with
  | empty => rw [Finset.card_empty, pow_zero, closedMass_empty G hp hp1 hq0]
  | @insert e γ he ih =>
    rw [Finset.card_insert_of_notMem he, pow_succ]
    calc cFE p q ^ γ.card * cFE p q
        = cFE p q * cFE p q ^ γ.card := by ring
      _ ≤ cFE p q * closedMass G p q γ :=
          mul_le_mul_of_nonneg_left ih (cFE_pos hp hp1 hq).le
      _ ≤ closedMass G p q (insert e γ) := cFE_mul_closedMass_le_insert G hp hp1 hq e he











def closedEvent (γ : Finset (Sym2 V)) : Set (ConfigSpace (Sym2 V)) :=
  {ω | ∀ e ∈ γ, ω e = false}



theorem closedMass_eq_indicator_sum (p q : ℝ) (γ : Finset (Sym2 V)) :
    closedMass G p q γ
      = ∑ ω, (closedEvent γ).indicator (fun _ => (1 : ℝ)) ω * fkProb G p q ω := by
  classical
  unfold closedMass
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases hω : ∀ e ∈ γ, ω e = false
  · have hmem : ω ∈ closedEvent γ := hω
    rw [if_pos hω, Set.indicator_of_mem hmem, one_mul]
  · have hnmem : ω ∉ closedEvent γ := hω
    rw [if_neg hω, Set.indicator_of_notMem hnmem, zero_mul]








theorem cFE_pow_le_closedEventMass {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (γ : Finset (Sym2 V)) :
    cFE p q ^ γ.card
      ≤ ∑ ω, (closedEvent γ).indicator (fun _ => (1 : ℝ)) ω * fkProb G p q ω := by
  rw [← closedMass_eq_indicator_sum]
  exact cFE_pow_le_closedMass G hp hp1 hq γ

end FK

end StatMech
