/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Code.Walls.rc79toporbit

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace






variable {ι : Type*} [Fintype ι] [DecidableEq ι]



def rc80_occ (A : Finset (ConfigSpace ι)) (K : Finset ι) (w : ConfigSpace ι) : Bool :=
  decide (∀ w' : ConfigSpace ι, (∀ e ∈ K, w' e = w e) → w' ∈ A)


def rc80_disjOccG (A B : Finset (ConfigSpace ι)) : Finset (ConfigSpace ι) :=
  Finset.univ.filter (fun w =>
    ∃ K L : Finset ι, Disjoint K L ∧ rc80_occ A K w = true ∧ rc80_occ B L w = true)


def rc80_compl (w : ConfigSpace ι) : ConfigSpace ι := fun i => !w i


def rc80_reflInterG (A B : Finset (ConfigSpace ι)) : Finset (ConfigSpace ι) :=
  A.filter (fun a => rc80_compl a ∈ B)








def rc80_IsUpper (A : Finset (ConfigSpace ι)) : Prop :=
  ∀ a ∈ A, ∀ i : ι, (Function.update a i true) ∈ A


def rc80_IsLower (A : Finset (ConfigSpace ι)) : Prop :=
  ∀ a ∈ A, ∀ i : ι, (Function.update a i false) ∈ A


def rc80_minext (K : Finset ι) (w : ConfigSpace ι) : ConfigSpace ι :=
  fun i => if i ∈ K then w i else false


def rc80_maxext (L : Finset ι) (w : ConfigSpace ι) : ConfigSpace ι :=
  fun i => if i ∈ L then w i else true


theorem rc80_minext_agree (K : Finset ι) (w : ConfigSpace ι) {e : ι} (he : e ∈ K) :
    rc80_minext K w e = w e := by simp [rc80_minext, he]


theorem rc80_maxext_agree (L : Finset ι) (w : ConfigSpace ι) {e : ι} (he : e ∈ L) :
    rc80_maxext L w e = w e := by simp [rc80_maxext, he]


theorem rc80_minext_le (K : Finset ι) (w : ConfigSpace ι) (i : ι) :
    rc80_minext K w i = true → w i = true := by
  simp only [rc80_minext]
  split <;> simp_all


theorem rc80_le_maxext (L : Finset ι) (w : ConfigSpace ι) (i : ι) :
    w i = true → rc80_maxext L w i = true := by
  simp only [rc80_maxext]
  split <;> simp_all






theorem rc80_upper_mono {A : Finset (ConfigSpace ι)} (hA : rc80_IsUpper A)
    {a b : ConfigSpace ι} (hab : ∀ i, a i = true → b i = true) (ha : a ∈ A) : b ∈ A := by
  
  classical
  set D : Finset ι := Finset.univ.filter (fun i => a i = false ∧ b i = true) with hD
  
  suffices H : ∀ (S : Finset ι) (c : ConfigSpace ι), c ∈ A →
      (∀ i, i ∉ S → c i = b i) → (∀ i ∈ S, c i = false) → b ∈ A by
    
    refine H D a ha ?_ ?_
    · intro i hi
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hi
      
      cases hai : a i
      · 
        have hbi : b i ≠ true := hi hai
        have : b i = false := Bool.eq_false_iff.mpr hbi
        rw [this]
      · 
        rw [hab i hai]
    · intro i hi
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi.1
  intro S
  induction S using Finset.induction with
  | empty => intro c hc hoff _
             have : c = b := funext (fun i => hoff i (Finset.notMem_empty i)); rwa [this] at hc
  | @insert j S hj ih =>
      intro c hc hoff hon
      
      
      
      have hcj : c j = false := hon j (Finset.mem_insert_self j S)
      
      
      by_cases hbj : b j = true
      · set c' := Function.update c j true with hc'
        have hc'A : c' ∈ A := hA c hc j
        refine ih c' hc'A ?_ ?_
        · intro i hi
          rw [hc']
          by_cases hij : i = j
          · subst hij; rw [Function.update_self]; exact hbj.symm
          · rw [Function.update_of_ne hij]
            exact hoff i (fun hmem => (Finset.mem_insert.mp hmem).elim (fun h => hij h) (fun h => hi h))
        · intro i hi
          rw [hc']
          have hijne : i ≠ j := by rintro rfl; exact hj hi
          rw [Function.update_of_ne hijne]
          exact hon i (Finset.mem_insert_of_mem hi)
      · 
        have hbjf : b j = false := by
          cases hb : b j
          · rfl
          · exact absurd hb hbj
        refine ih c hc ?_ ?_
        · intro i hi
          by_cases hij : i = j
          · subst hij; rw [hcj, hbjf]
          · exact hoff i (fun hmem => (Finset.mem_insert.mp hmem).elim (fun h => hij h) (fun h => hi h))
        · intro i hi; exact hon i (Finset.mem_insert_of_mem hi)



theorem rc80_lower_mono {A : Finset (ConfigSpace ι)} (hA : rc80_IsLower A)
    {a b : ConfigSpace ι} (hab : ∀ i, b i = true → a i = true) (ha : a ∈ A) : b ∈ A := by
  classical
  set D : Finset ι := Finset.univ.filter (fun i => a i = true ∧ b i = false) with hD
  suffices H : ∀ (S : Finset ι) (c : ConfigSpace ι), c ∈ A →
      (∀ i, i ∉ S → c i = b i) → (∀ i ∈ S, c i = true) → b ∈ A by
    refine H D a ha ?_ ?_
    · intro i hi
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hi
      cases hai : a i
      · 
        have hbif : b i = false := by
          by_contra hbi
          have : b i = true := by
            cases hb : b i
            · exact absurd hb hbi
            · rfl
          rw [hab i this] at hai; exact Bool.noConfusion hai
        rw [hbif]
      · 
        have hbne : b i ≠ false := hi hai
        have : b i = true := by
          cases hbi : b i
          · exact absurd hbi hbne
          · rfl
        rw [this]
    · intro i hi
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi.1
  intro S
  induction S using Finset.induction with
  | empty => intro c hc hoff _
             have : c = b := funext (fun i => hoff i (Finset.notMem_empty i)); rwa [this] at hc
  | @insert j S hj ih =>
      intro c hc hoff hon
      have hcj : c j = true := hon j (Finset.mem_insert_self j S)
      by_cases hbj : b j = false
      · set c' := Function.update c j false with hc'
        have hc'A : c' ∈ A := hA c hc j
        refine ih c' hc'A ?_ ?_
        · intro i hi
          rw [hc']
          by_cases hij : i = j
          · subst hij; rw [Function.update_self]; exact hbj.symm
          · rw [Function.update_of_ne hij]
            exact hoff i (fun hmem => (Finset.mem_insert.mp hmem).elim (fun h => hij h) (fun h => hi h))
        · intro i hi
          rw [hc']
          have hijne : i ≠ j := by rintro rfl; exact hj hi
          rw [Function.update_of_ne hijne]
          exact hon i (Finset.mem_insert_of_mem hi)
      · have hbjt : b j = true := by
          cases hb : b j
          · exact absurd hb hbj
          · rfl
        refine ih c hc ?_ ?_
        · intro i hi
          by_cases hij : i = j
          · subst hij; rw [hcj, hbjt]
          · exact hoff i (fun hmem => (Finset.mem_insert.mp hmem).elim (fun h => hij h) (fun h => hi h))
        · intro i hi; exact hon i (Finset.mem_insert_of_mem hi)


theorem rc80_occ_upper_iff {A : Finset (ConfigSpace ι)} (hA : rc80_IsUpper A)
    (K : Finset ι) (w : ConfigSpace ι) :
    rc80_occ A K w = true ↔ rc80_minext K w ∈ A := by
  unfold rc80_occ
  rw [decide_eq_true_eq]
  constructor
  · intro h
    
    exact h (rc80_minext K w) (fun e he => rc80_minext_agree K w he)
  · intro hmin w' hw'
    
    refine rc80_upper_mono hA ?_ hmin
    intro i hi
    
    by_cases hiK : i ∈ K
    · rw [rc80_minext_agree K w hiK] at hi; rw [hw' i hiK]; exact hi
    · simp only [rc80_minext, hiK, if_false] at hi; exact absurd hi (by simp)


theorem rc80_occ_lower_iff {B : Finset (ConfigSpace ι)} (hB : rc80_IsLower B)
    (L : Finset ι) (w : ConfigSpace ι) :
    rc80_occ B L w = true ↔ rc80_maxext L w ∈ B := by
  unfold rc80_occ
  rw [decide_eq_true_eq]
  constructor
  · intro h
    exact h (rc80_maxext L w) (fun e he => rc80_maxext_agree L w he)
  · intro hmax w' hw'
    
    refine rc80_lower_mono hB ?_ hmax
    intro i hi
    by_cases hiL : i ∈ L
    · rw [rc80_maxext_agree L w hiL]; rw [hw' i hiL] at hi; exact hi
    · simp only [rc80_maxext, hiL, if_false]








theorem rc80_disjOcc_eq_inter_of_upper_lower {A B : Finset (ConfigSpace ι)}
    (hA : rc80_IsUpper A) (hB : rc80_IsLower B) :
    rc80_disjOccG A B = A ∩ B := by
  ext w
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨K, L, _, hK, hL⟩
    rw [rc80_occ_upper_iff hA] at hK
    rw [rc80_occ_lower_iff hB] at hL
    refine ⟨?_, ?_⟩
    · 
      refine rc80_upper_mono hA (fun i hi => rc80_minext_le K w i hi) hK
    · 
      refine rc80_lower_mono hB (fun i hi => rc80_le_maxext L w i hi) hL
  · rintro ⟨hwA, hwB⟩
    refine ⟨Finset.univ.filter (fun i => w i = true), Finset.univ.filter (fun i => w i = false),
      ?_, ?_, ?_⟩
    · 
      rw [Finset.disjoint_filter]
      intro i _ hi
      simp only [hi, Bool.true_eq_false, not_false_eq_true]
    · 
      rw [rc80_occ_upper_iff hA]
      have : rc80_minext (Finset.univ.filter (fun i => w i = true)) w = w := by
        funext i
        simp only [rc80_minext, Finset.mem_filter, Finset.mem_univ, true_and]
        cases hw : w i <;> simp
      rw [this]; exact hwA
    · 
      rw [rc80_occ_lower_iff hB]
      have : rc80_maxext (Finset.univ.filter (fun i => w i = false)) w = w := by
        funext i
        simp only [rc80_maxext, Finset.mem_filter, Finset.mem_univ, true_and]
        cases hw : w i <;> simp
      rw [this]; exact hwB





theorem rc80_wall_upper_lower_iff {A B : Finset (ConfigSpace ι)}
    (hA : rc80_IsUpper A) (hB : rc80_IsLower B) :
    (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card
      ↔ (A ∩ B).card ≤ (rc80_reflInterG A B).card := by
  rw [rc80_disjOcc_eq_inter_of_upper_lower hA hB]










variable {κ : Type*} [Fintype κ] [DecidableEq κ]


def rc80_restL (w : ConfigSpace (ι ⊕ κ)) : ConfigSpace ι := fun i => w (Sum.inl i)
def rc80_restR (w : ConfigSpace (ι ⊕ κ)) : ConfigSpace κ := fun j => w (Sum.inr j)


def rc80_prodFam (A₁ : Finset (ConfigSpace ι)) (A₂ : Finset (ConfigSpace κ)) :
    Finset (ConfigSpace (ι ⊕ κ)) :=
  Finset.univ.filter (fun w => rc80_restL w ∈ A₁ ∧ rc80_restR w ∈ A₂)

@[simp] theorem rc80_mem_prodFam {A₁ : Finset (ConfigSpace ι)} {A₂ : Finset (ConfigSpace κ)}
    (w : ConfigSpace (ι ⊕ κ)) :
    w ∈ rc80_prodFam A₁ A₂ ↔ rc80_restL w ∈ A₁ ∧ rc80_restR w ∈ A₂ := by
  simp [rc80_prodFam]


theorem rc80_restL_compl (w : ConfigSpace (ι ⊕ κ)) :
    rc80_restL (rc80_compl w) = rc80_compl (rc80_restL w) := rfl


theorem rc80_restR_compl (w : ConfigSpace (ι ⊕ κ)) :
    rc80_restR (rc80_compl w) = rc80_compl (rc80_restR w) := rfl





theorem rc80_reflInter_prod_card
    (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)) :
    (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
      = (rc80_reflInterG A₁ B₁).card * (rc80_reflInterG A₂ B₂).card := by
  rw [← Finset.card_product]
  apply Finset.card_bij (fun w _ => (rc80_restL w, rc80_restR w))
  · 
    intro w hw
    simp only [rc80_reflInterG, Finset.mem_filter, rc80_mem_prodFam] at hw
    obtain ⟨⟨hwA1, hwA2⟩, hcompl⟩ := hw
    rw [rc80_restL_compl, rc80_restR_compl] at hcompl
    rw [Finset.mem_product]
    exact ⟨by rw [rc80_reflInterG, Finset.mem_filter]; exact ⟨hwA1, hcompl.1⟩,
           by rw [rc80_reflInterG, Finset.mem_filter]; exact ⟨hwA2, hcompl.2⟩⟩
  · 
    intro w hw v hv h
    rw [Prod.mk.injEq] at h
    obtain ⟨hL, hR⟩ := h
    funext x
    cases x with
    | inl i => exact congrFun hL i
    | inr j => exact congrFun hR j
  · 
    intro q hq
    rw [Finset.mem_product] at hq
    obtain ⟨hqA, hqB⟩ := hq
    rw [rc80_reflInterG, Finset.mem_filter] at hqA hqB
    refine ⟨Sum.elim q.1 q.2, ?_, ?_⟩
    · simp only [rc80_reflInterG, Finset.mem_filter, rc80_mem_prodFam]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show (fun i => Sum.elim q.1 q.2 (Sum.inl i)) ∈ A₁; simpa using hqA.1
      · show (fun j => Sum.elim q.1 q.2 (Sum.inr j)) ∈ A₂; simpa using hqB.1
      · rw [rc80_restL_compl, rc80_restR_compl]
        refine ⟨?_, ?_⟩
        · show rc80_compl (fun i => Sum.elim q.1 q.2 (Sum.inl i)) ∈ B₁; simpa using hqA.2
        · show rc80_compl (fun j => Sum.elim q.1 q.2 (Sum.inr j)) ∈ B₂; simpa using hqB.2
    · rw [Prod.mk.injEq]
      exact ⟨by funext i; rfl, by funext j; rfl⟩




def rc80_projL (K : Finset (ι ⊕ κ)) : Finset ι := Finset.univ.filter (fun i => Sum.inl i ∈ K)

def rc80_projR (K : Finset (ι ⊕ κ)) : Finset κ := Finset.univ.filter (fun j => Sum.inr j ∈ K)

@[simp] theorem rc80_mem_projL (K : Finset (ι ⊕ κ)) (i : ι) :
    i ∈ rc80_projL K ↔ Sum.inl i ∈ K := by simp [rc80_projL]
@[simp] theorem rc80_mem_projR (K : Finset (ι ⊕ κ)) (j : κ) :
    j ∈ rc80_projR K ↔ Sum.inr j ∈ K := by simp [rc80_projR]





theorem rc80_occ_prodFam_iff (A₁ : Finset (ConfigSpace ι)) (A₂ : Finset (ConfigSpace κ))
    (K : Finset (ι ⊕ κ)) (w : ConfigSpace (ι ⊕ κ)) :
    rc80_occ (rc80_prodFam A₁ A₂) K w = true
      ↔ rc80_occ A₁ (rc80_projL K) (rc80_restL w) = true
        ∧ rc80_occ A₂ (rc80_projR K) (rc80_restR w) = true := by
  simp only [rc80_occ, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · 
      intro u' hu'
      have := h (Sum.elim u' (rc80_restR w)) ?_
      · rw [rc80_mem_prodFam] at this
        have hL : rc80_restL (Sum.elim u' (rc80_restR w)) = u' := by funext i; rfl
        rw [hL] at this; exact this.1
      · intro e he
        cases e with
        | inl i =>
            show u' i = rc80_restL w i
            exact hu' i (by rw [rc80_mem_projL]; exact he)
        | inr j => rfl
    · intro v' hv'
      have := h (Sum.elim (rc80_restL w) v') ?_
      · rw [rc80_mem_prodFam] at this
        have hR : rc80_restR (Sum.elim (rc80_restL w) v') = v' := by funext j; rfl
        rw [hR] at this; exact this.2
      · intro e he
        cases e with
        | inl i => rfl
        | inr j =>
            show v' j = rc80_restR w j
            exact hv' j (by rw [rc80_mem_projR]; exact he)
  · rintro ⟨h1, h2⟩ w' hw'
    rw [rc80_mem_prodFam]
    refine ⟨h1 (rc80_restL w') ?_, h2 (rc80_restR w') ?_⟩
    · intro i hi; exact hw' (Sum.inl i) (by rwa [rc80_mem_projL] at hi)
    · intro j hj; exact hw' (Sum.inr j) (by rwa [rc80_mem_projR] at hj)







theorem rc80_disjOcc_prod_card
    (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)) :
    (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
      = (rc80_disjOccG A₁ B₁).card * (rc80_disjOccG A₂ B₂).card := by
  rw [← Finset.card_product]
  apply Finset.card_bij (fun w _ => (rc80_restL w, rc80_restR w))
  · 
    intro w hw
    simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨K, L, hKL, hK, hL⟩ := hw
    rw [rc80_occ_prodFam_iff] at hK hL
    rw [Finset.mem_product]
    refine ⟨?_, ?_⟩
    · simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨rc80_projL K, rc80_projL L, ?_, hK.1, hL.1⟩
      rw [Finset.disjoint_left]
      intro i hiK hiL
      rw [rc80_mem_projL] at hiK hiL
      exact (Finset.disjoint_left.mp hKL hiK) hiL
    · simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨rc80_projR K, rc80_projR L, ?_, hK.2, hL.2⟩
      rw [Finset.disjoint_left]
      intro j hjK hjL
      rw [rc80_mem_projR] at hjK hjL
      exact (Finset.disjoint_left.mp hKL hjK) hjL
  · 
    intro w hw v hv h
    rw [Prod.mk.injEq] at h
    obtain ⟨hL, hR⟩ := h
    funext x
    cases x with
    | inl i => exact congrFun hL i
    | inr j => exact congrFun hR j
  · 
    intro q hq
    rw [Finset.mem_product] at hq
    obtain ⟨hqA, hqB⟩ := hq
    simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and] at hqA hqB
    obtain ⟨K₁, L₁, hKL₁, hK₁, hL₁⟩ := hqA
    obtain ⟨K₂, L₂, hKL₂, hK₂, hL₂⟩ := hqB
    refine ⟨Sum.elim q.1 q.2, ?_, ?_⟩
    · simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨K₁.image Sum.inl ∪ K₂.image Sum.inr, L₁.image Sum.inl ∪ L₂.image Sum.inr, ?_, ?_, ?_⟩
      · 
        rw [Finset.disjoint_left]
        intro e heK heL
        simp only [Finset.mem_union, Finset.mem_image] at heK heL
        rcases heK with ⟨i, hiK, rfl⟩ | ⟨j, hjK, rfl⟩
        · rcases heL with ⟨i', hiL, hii⟩ | ⟨j', hjL, hij⟩
          · rw [Sum.inl.injEq] at hii; subst hii; exact (Finset.disjoint_left.mp hKL₁ hiK) hiL
          · exact absurd hij (by simp)
        · rcases heL with ⟨i', hiL, hij⟩ | ⟨j', hjL, hjj⟩
          · exact absurd hij (by simp)
          · rw [Sum.inr.injEq] at hjj; subst hjj; exact (Finset.disjoint_left.mp hKL₂ hjK) hjL
      · 
        rw [rc80_occ_prodFam_iff]
        constructor
        · have hpL : rc80_projL (K₁.image Sum.inl ∪ K₂.image Sum.inr) = K₁ := by
            ext i; simp [rc80_projL]
          have hwL : rc80_restL (Sum.elim q.1 q.2) = q.1 := by funext i; rfl
          rw [hpL, hwL]; exact hK₁
        · have hpR : rc80_projR (K₁.image Sum.inl ∪ K₂.image Sum.inr) = K₂ := by
            ext j; simp [rc80_projR]
          have hwR : rc80_restR (Sum.elim q.1 q.2) = q.2 := by funext j; rfl
          rw [hpR, hwR]; exact hK₂
      · 
        rw [rc80_occ_prodFam_iff]
        constructor
        · have hpL : rc80_projL (L₁.image Sum.inl ∪ L₂.image Sum.inr) = L₁ := by
            ext i; simp [rc80_projL]
          have hwL : rc80_restL (Sum.elim q.1 q.2) = q.1 := by funext i; rfl
          rw [hpL, hwL]; exact hL₁
        · have hpR : rc80_projR (L₁.image Sum.inl ∪ L₂.image Sum.inr) = L₂ := by
            ext j; simp [rc80_projR]
          have hwR : rc80_restR (Sum.elim q.1 q.2) = q.2 := by funext j; rfl
          rw [hpR, hwR]; exact hL₂
    · rw [Prod.mk.injEq]; exact ⟨by funext i; rfl, by funext j; rfl⟩







theorem rc80_wall_product
    (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ))
    (h1 : (rc80_disjOccG A₁ B₁).card ≤ (rc80_reflInterG A₁ B₁).card)
    (h2 : (rc80_disjOccG A₂ B₂).card ≤ (rc80_reflInterG A₂ B₂).card) :
    (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
      ≤ (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card := by
  rw [rc80_reflInter_prod_card, rc80_disjOcc_prod_card]
  exact Nat.mul_le_mul h1 h2










theorem rc80_monoWitness_upper : rc80_IsUpper ({(fun _ => true)} : Finset (ConfigSpace (Fin 2))) := by
  intro a ha i
  rw [Finset.mem_singleton] at ha ⊢
  subst ha; funext j; simp [Function.update]

theorem rc80_monoWitness_lower : rc80_IsLower ({(fun _ => false)} : Finset (ConfigSpace (Fin 2))) := by
  intro a ha i
  rw [Finset.mem_singleton] at ha ⊢
  subst ha; funext j; simp [Function.update]


theorem rc80_monoWitness_reduces :
    rc80_disjOccG ({(fun _ => true)} : Finset (ConfigSpace (Fin 2))) {(fun _ => false)}
      = ({(fun _ => true)} : Finset (ConfigSpace (Fin 2))) ∩ {(fun _ => false)} :=
  rc80_disjOcc_eq_inter_of_upper_lower rc80_monoWitness_upper rc80_monoWitness_lower



theorem rc80_prodWitness_reflInter :
    (rc80_reflInterG
        (rc80_prodFam ({(fun _ => true)} : Finset (ConfigSpace (Fin 1)))
          ({(fun _ => true)} : Finset (ConfigSpace (Fin 1))))
        (rc80_prodFam ({(fun _ => false)} : Finset (ConfigSpace (Fin 1)))
          ({(fun _ => false)} : Finset (ConfigSpace (Fin 1))))).card
      = (rc80_reflInterG ({(fun _ => true)} : Finset (ConfigSpace (Fin 1))) {(fun _ => false)}).card
        * (rc80_reflInterG ({(fun _ => true)} : Finset (ConfigSpace (Fin 1))) {(fun _ => false)}).card :=
  rc80_reflInter_prod_card _ _ _ _

open Classical in



theorem rc80_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc79_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in 



























theorem rc80_status :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc80_IsUpper A → rc80_IsLower B → rc80_disjOccG A B = A ∩ B) ∧
    
    (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
        (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)),
        (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
          = (rc80_disjOccG A₁ B₁).card * (rc80_disjOccG A₂ B₂).card) ∧
    
    (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
        (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)),
        (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
          = (rc80_reflInterG A₁ B₁).card * (rc80_reflInterG A₂ B₂).card) ∧
    
    (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
        (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)),
        (rc80_disjOccG A₁ B₁).card ≤ (rc80_reflInterG A₁ B₁).card →
        (rc80_disjOccG A₂ B₂).card ≤ (rc80_reflInterG A₂ B₂).card →
        (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
          ≤ (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun _ _ hA hB => rc80_disjOcc_eq_inter_of_upper_lower hA hB,
   fun A₁ B₁ A₂ B₂ => rc80_disjOcc_prod_card A₁ B₁ A₂ B₂,
   fun A₁ B₁ A₂ B₂ => rc80_reflInter_prod_card A₁ B₁ A₂ B₂,
   fun A₁ B₁ A₂ B₂ => rc80_wall_product A₁ B₁ A₂ B₂,
   rc79_top_wall_fin2,
   rc80_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
