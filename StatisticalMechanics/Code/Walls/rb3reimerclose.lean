/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Code.Walls.rb2butterflyclose
import Code.Walls.rc86consolidation

open Finset
open scoped BigOperators NNReal

namespace StatMech.Walls.Reimer

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false







def rb3_toB {n : ℕ} (S : Finset (Fin n)) : rbt_Q n := fun i => decide (i ∈ S)


noncomputable def rb3_ofB {n : ℕ} (x : rbt_Q n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = true)

@[simp] lemma rb3_toB_apply {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    rb3_toB S i = decide (i ∈ S) := rfl

@[simp] lemma rb3_mem_ofB {n : ℕ} (x : rbt_Q n) (i : Fin n) :
    i ∈ rb3_ofB x ↔ x i = true := by
  simp [rb3_ofB]

lemma rb3_ofB_toB {n : ℕ} (S : Finset (Fin n)) : rb3_ofB (rb3_toB S) = S := by
  ext i; simp [rb3_mem_ofB, rb3_toB]

lemma rb3_toB_ofB {n : ℕ} (x : rbt_Q n) : rb3_toB (rb3_ofB x) = x := by
  funext i
  simp only [rb3_toB, rb3_mem_ofB]
  cases hx : x i <;> simp [hx]

lemma rb3_toB_injective {n : ℕ} : Function.Injective (rb3_toB (n := n)) := by
  intro S T h
  have := congrArg rb3_ofB h
  rwa [rb3_ofB_toB, rb3_ofB_toB] at this


lemma rb3_toB_compl {n : ℕ} (S : Finset (Fin n)) :
    rbt_antipode (rb3_toB S) = rb3_toB Sᶜ := by
  funext i
  simp only [rbt_antipode, rb3_toB]
  by_cases h : i ∈ S <;> simp [h, Finset.mem_compl]


lemma rb3_inter_eq_iff_agree {n : ℕ} (K S T : Finset (Fin n)) :
    T ∩ K = S ∩ K ↔ ∀ i ∈ K, rb3_toB T i = rb3_toB S i := by
  constructor
  · intro h i hiK
    simp only [rb3_toB, decide_eq_decide]
    constructor
    · intro hiT
      have : i ∈ T ∩ K := Finset.mem_inter.mpr ⟨hiT, hiK⟩
      rw [h] at this; exact (Finset.mem_inter.mp this).1
    · intro hiS
      have : i ∈ S ∩ K := Finset.mem_inter.mpr ⟨hiS, hiK⟩
      rw [← h] at this; exact (Finset.mem_inter.mp this).1
  · intro h
    ext i
    simp only [Finset.mem_inter]
    refine and_congr_left (fun hiK => ?_)
    have := h i hiK
    simp only [rb3_toB, decide_eq_decide] at this
    exact this










open Classical in



noncomputable def rb3_witK {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Fin n) := by
  classical
  exact if h : ∃ K L : Finset (Fin n), Disjoint K L ∧
      (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) ∧
      (∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ)
    then h.choose else ∅

open Classical in


lemma rb3_witK_spec {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    (∀ T : Finset (Fin n), T ∩ (rb3_witK 𝒜 ℬ S) = S ∩ (rb3_witK 𝒜 ℬ S) → T ∈ 𝒜) ∧
    (∀ T : Finset (Fin n), T ∩ (rb3_witK 𝒜 ℬ S)ᶜ = S ∩ (rb3_witK 𝒜 ℬ S)ᶜ → T ∈ ℬ) := by
  rw [rc20_famCylBox, Finset.mem_filter] at hS
  have hex : ∃ K L : Finset (Fin n), Disjoint K L ∧
      (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) ∧
      (∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) := hS.2
  have hK : rb3_witK 𝒜 ℬ S = hex.choose := by rw [rb3_witK, dif_pos hex]
  obtain ⟨L, hKL, hKA, hLB⟩ := hex.choose_spec
  rw [hK]
  refine ⟨hKA, ?_⟩
  
  intro T hT
  apply hLB
  
  have hLsub : L ⊆ hex.chooseᶜ := by
    intro i hiL
    rw [Finset.mem_compl]
    exact Finset.disjoint_right.mp hKL hiL
  
  rw [rb3_inter_eq_iff_agree] at hT ⊢
  exact fun i hiL => hT i (hLsub hiL)



noncomputable def rb3_body {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) (x : rbt_Q n) : rbt_Q n :=
  rb3_toB (rc36_R0 (rb3_ofB x) (rb3_witK 𝒜 ℬ (rb3_ofB x)) (rb3_witK 𝒜 ℬ (rb3_ofB x))ᶜ)














lemma rb3_body_apply {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) (i : Fin n) :
    rb3_body 𝒜 ℬ (rb3_toB S) i =
      (if i ∈ rb3_witK 𝒜 ℬ S then rb3_toB S i else !(rb3_toB S i)) := by
  classical
  simp only [rb3_body, rb3_ofB_toB, rb3_toB, rc36_R0, Finset.mem_union, Finset.mem_inter,
    Finset.mem_sdiff, Finset.mem_compl]
  by_cases hK : i ∈ rb3_witK 𝒜 ℬ S <;>
    by_cases hS : i ∈ S <;> simp [hK, hS]

open Classical in



lemma rb3_inRed_iff {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) (x : rbt_Q n) :
    rbt_inRed (rb3_body 𝒜 ℬ (rb3_toB S)) (rb3_toB S) x ↔
      (rb3_ofB x) ∩ (rb3_witK 𝒜 ℬ S) = S ∩ (rb3_witK 𝒜 ℬ S) := by
  rw [rb3_inter_eq_iff_agree, rb3_toB_ofB]
  rw [rbt_inRed, rbt_inCube]
  constructor
  · intro h i hiK
    rcases h i with hc | hy
    · rw [hc, rb3_body_apply, if_pos hiK]
    · exact hy
  · intro h i
    by_cases hiK : i ∈ rb3_witK 𝒜 ℬ S
    · exact Or.inr (h i hiK)
    · 
      by_cases hxi : x i = rb3_toB S i
      · exact Or.inr hxi
      · left
        rw [rb3_body_apply, if_neg hiK]
        cases hx : x i <;> cases hSi : rb3_toB S i <;> simp_all

open Classical in



lemma rb3_inYellow_iff {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) (x : rbt_Q n) :
    rbt_inYellow (rb3_body 𝒜 ℬ (rb3_toB S)) (rb3_toB S) x ↔
      (rb3_ofB x)ᶜ ∩ (rb3_witK 𝒜 ℬ S)ᶜ = S ∩ (rb3_witK 𝒜 ℬ S)ᶜ := by
  rw [rb3_inter_eq_iff_agree]
  
  have hcompl : ∀ i, rb3_toB (rb3_ofB x)ᶜ i = !(x i) := by
    intro i
    have := rb3_toB_compl (rb3_ofB x)
    have h2 := congrFun this i
    rw [rbt_antipode, rb3_toB_ofB] at h2
    rw [← h2]
  rw [rbt_inYellow, rbt_inCube]
  constructor
  · intro h i hiKc
    rw [hcompl i]
    rcases h i with hc | hy
    · 
      rw [hc, rb3_body_apply]
      
      have hiK : i ∉ rb3_witK 𝒜 ℬ S := by simpa [Finset.mem_compl] using hiKc
      rw [if_neg hiK]
      cases hSi : rb3_toB S i <;> simp_all
    · 
      rw [rbt_antipode] at hy
      rw [hy]; cases hSi : rb3_toB S i <;> simp_all
  · intro h i
    by_cases hiK : i ∈ rb3_witK 𝒜 ℬ S
    · 
      by_cases hxi : x i = rb3_toB S i
      · left; rw [hxi, rb3_body_apply, if_pos hiK]
      · right; rw [rbt_antipode]; cases hx : x i <;> cases hS : rb3_toB S i <;> simp_all
    · 
      have hiKc : i ∈ (rb3_witK 𝒜 ℬ S)ᶜ := by simpa [Finset.mem_compl] using hiK
      have := h i hiKc
      rw [hcompl i] at this
      
      right
      rw [rbt_antipode]
      cases hx : x i <;> cases hS : rb3_toB S i <;> simp_all












open Classical in



lemma rb3_red_mem_A {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n)))
    {x : rbt_Q n} (hx : x ∈ rbt_Red (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)) :
    rb3_ofB x ∈ 𝒜 := by
  rw [rbt_Red, Finset.mem_filter] at hx
  obtain ⟨y, hyT, hxy⟩ := hx.2
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hyT
  rw [rb3_inRed_iff] at hxy
  exact (rb3_witK_spec 𝒜 ℬ hS).1 _ hxy

open Classical in



lemma rb3_yellow_mem_B {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n)))
    {x : rbt_Q n} (hx : x ∈ rbt_Yellow (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)) :
    (rb3_ofB x)ᶜ ∈ ℬ := by
  rw [rbt_Yellow, Finset.mem_filter] at hx
  obtain ⟨y, hyT, hxy⟩ := hx.2
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hyT
  rw [rb3_inYellow_iff] at hxy
  exact (rb3_witK_spec 𝒜 ℬ hS).2 _ hxy

open Classical in



lemma rb3_redYellow_ofB_mem_reflInter {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n)))
    {x : rbt_Q n}
    (hx : x ∈ rbt_Red (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)
        ∩ rbt_Yellow (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)) :
    rb3_ofB x ∈ rc10_reflInter 𝒜 ℬ := by
  rw [Finset.mem_inter] at hx
  rw [rc20_mem_reflInter]
  exact ⟨rb3_red_mem_A 𝒜 ℬ hx.1, rb3_yellow_mem_B 𝒜 ℬ hx.2⟩

open Classical in


lemma rb3_card_redYellow_le_reflInter {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) :
    (rbt_Red (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)
        ∩ rbt_Yellow (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)).card
      ≤ (rc10_reflInter 𝒜 ℬ).card := by
  apply Finset.card_le_card_of_injOn rb3_ofB
  · intro x hx
    exact rb3_redYellow_ofB_mem_reflInter 𝒜 ℬ hx
  · intro a _ b _ hab
    have := congrArg rb3_toB hab
    rwa [rb3_toB_ofB, rb3_toB_ofB] at this

open Classical in


lemma rb3_card_tips {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) :
    ((rc20_famCylBox 𝒜 ℬ).image rb3_toB).card = (rc20_famCylBox 𝒜 ℬ).card :=
  Finset.card_image_of_injective _ rb3_toB_injective

open Classical in







theorem rb3_famCylBox_le_reflInter {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) :
    (rc20_famCylBox 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card := by
  rw [← rb3_card_tips 𝒜 ℬ]
  calc ((rc20_famCylBox 𝒜 ℬ).image rb3_toB).card
      ≤ (rbt_Red (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)
          ∩ rbt_Yellow (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)).card :=
        rb2_butterfly_thm n (rb3_body 𝒜 ℬ) ((rc20_famCylBox 𝒜 ℬ).image rb3_toB)
    _ ≤ (rc10_reflInter 𝒜 ℬ).card := rb3_card_redYellow_le_reflInter 𝒜 ℬ











theorem rb3_famCylBoxResidue : StatMech.Walls.rc20_FamCylBoxResidue :=
  fun _ 𝒜 ℬ => rb3_famCylBox_le_reflInter 𝒜 ℬ



theorem rb3_reimerWprobCore : StatMech.ReimerWprobCore :=
  StatMech.rc84_residue_is_famCylBox rb3_famCylBoxResidue











theorem rb3_thm_reimer {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    (A B : Set (StatMech.ConfigSpace E)) :
    (StatMech.bernoulliProductMeasure (E := E) p hp).real (StatMech.disjointOccurrence A B)
      ≤ (StatMech.bernoulliProductMeasure (E := E) p hp).real A
        * (StatMech.bernoulliProductMeasure (E := E) p hp).real B :=
  StatMech.reimer_inequality_of_core rb3_reimerWprobCore hp A B

end StatMech.Walls.Reimer
