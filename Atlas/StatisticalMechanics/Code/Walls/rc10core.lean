/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Code.Walls.rc9core
import Code.Inequalities.ReimerCompressLib
import Code.Inequalities.ReimerIterationClose

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]









open Classical in



theorem rc10_occursOn_iff_fin {A : Set (ConfigSpace α)} (hA : IsIncreasing A) (K : Finset α)
    (ω : ConfigSpace α) (hK : K ⊆ cfgSupport ω) : OccursOn A (↑K) ω ↔ supportCfg K ∈ A := by
  constructor
  · intro h
    apply h; intro e he; simp only [Finset.mem_coe] at he
    have : ω e = true := by rw [← mem_cfgSupport]; exact hK he
    simp only [supportCfg_apply, this]; simp [he]
  · intro h ω' hω'
    refine hA (fun a => ?_) h
    by_cases ha : a ∈ K
    · have : ω a = true := by rw [← mem_cfgSupport]; exact hK ha
      have hω'a : ω' a = ω a := hω' a (by simp [ha])
      simp only [supportCfg_apply, ha, decide_true]; rw [hω'a, this]
    · simp only [supportCfg_apply, ha, decide_false]; exact Bool.false_le _

open Classical in



theorem rc10_occursOn_restrict_mem {A : Set (ConfigSpace α)} (Kset : Set α) (ω : ConfigSpace α)
    (h : OccursOn A Kset ω) :
    supportCfg (cfgSupport ω ∩ {a | a ∈ Kset}.toFinset) ∈ A := by
  apply h
  intro e he
  simp only [supportCfg_apply, Finset.mem_inter, mem_cfgSupport, Set.mem_toFinset,
    Set.mem_setOf_eq]
  by_cases hω : ω e = true
  · simp [hω, he]
  · simp only [Bool.not_eq_true] at hω; rw [hω]; simp

open Classical in







theorem rc10_box_increasing_iff {A B : Set (ConfigSpace α)} (hA : IsIncreasing A)
    (hB : IsIncreasing B) (ω : ConfigSpace α) :
    ω ∈ disjointOccurrence A B ↔
      ∃ K L : Finset α, Disjoint K L ∧ K ⊆ cfgSupport ω ∧ L ⊆ cfgSupport ω ∧
        supportCfg K ∈ A ∧ supportCfg L ∈ B := by
  constructor
  · rintro ⟨Kset, Lset, hKL, hAK, hBL⟩
    refine ⟨cfgSupport ω ∩ {a | a ∈ Kset}.toFinset, cfgSupport ω ∩ {a | a ∈ Lset}.toFinset, ?_,
            Finset.inter_subset_left, Finset.inter_subset_left,
            rc10_occursOn_restrict_mem Kset ω hAK, rc10_occursOn_restrict_mem Lset ω hBL⟩
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_inter, Set.mem_toFinset, Set.mem_setOf_eq] at ha hb
    exact (Set.disjoint_left.mp hKL ha.2) hb.2
  · rintro ⟨K, L, hKL, hKsub, hLsub, hKA, hLB⟩
    refine ⟨↑K, ↑L, ?_, ?_, ?_⟩
    · rwa [Finset.disjoint_coe]
    · rw [rc10_occursOn_iff_fin hA K ω hKsub]; exact hKA
    · rw [rc10_occursOn_iff_fin hB L ω hLsub]; exact hLB





theorem rc10_cfgSupport_compl (ω : ConfigSpace α) :
    cfgSupport (rmr_compl ω) = (cfgSupport ω)ᶜ := by
  ext i
  simp only [mem_cfgSupport, rmr_compl, Finset.mem_compl]
  simp [Bool.not_eq_true]

open Classical in




theorem rc10_isUpperSet_eventFamily {A : Set (ConfigSpace α)} (hA : IsIncreasing A) :
    IsUpperSet ((eventFamily A) : Set (Finset α)) := by
  intro S T hST hS
  simp only [Finset.mem_coe, eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hS ⊢
  obtain ⟨ω, hω, hωS⟩ := hS
  refine ⟨supportCfg T, ?_, cfgSupport_supportCfg T⟩
  have hle : ω ≤ supportCfg T := by
    intro a
    rw [← hωS] at hST
    by_cases ha : ω a = true
    · have ha' : a ∈ cfgSupport ω := by rw [mem_cfgSupport]; exact ha
      have haT : a ∈ T := hST ha'
      simp only [supportCfg_apply, haT, decide_true, ha, le_refl]
    · simp only [Bool.not_eq_true] at ha; rw [ha]; exact Bool.false_le _
  exact hA hle hω

open Classical in



theorem rc10_eventFamily_familyEvent (𝒜 : Finset (Finset α)) :
    eventFamily (familyEvent 𝒜) = 𝒜 := by
  ext S
  simp only [eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_familyEvent]
  constructor
  · rintro ⟨ω, hω, rfl⟩; exact hω
  · intro hS; exact ⟨supportCfg S, by rw [cfgSupport_supportCfg]; exact hS, cfgSupport_supportCfg S⟩







open Classical in


theorem rc10_card_via_support (P : Finset α → Prop) [DecidablePred P]
    (Q : ConfigSpace α → Prop) [DecidablePred Q] (h : ∀ ω, Q ω ↔ P (cfgSupport ω)) :
    #(univ.filter Q) = #(univ.filter P) := by
  apply Finset.card_bij (fun ω _ => cfgSupport ω)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact (h ω).mp hω
  · intro a _ b _ hab
    have := congrArg supportCfg hab
    rwa [supportCfg_cfgSupport, supportCfg_cfgSupport] at this
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact ⟨supportCfg S, by rw [h, cfgSupport_supportCfg]; exact hS, cfgSupport_supportCfg S⟩







open Classical in



noncomputable def rc10_boxSupp (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  univ.filter (fun S => ∃ K L : Finset α, Disjoint K L ∧ K ⊆ S ∧ L ⊆ S ∧ K ∈ 𝒜 ∧ L ∈ ℬ)

open Classical in


noncomputable def rc10_reflInter (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  univ.filter (fun S => S ∈ 𝒜 ∧ Sᶜ ∈ ℬ)

open Classical in




theorem rc10_card_box_eq (A B : Set (ConfigSpace α)) (hA : IsIncreasing A) (hB : IsIncreasing B) :
    #(univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B))
      = #(rc10_boxSupp (eventFamily A) (eventFamily B)) := by
  classical
  rw [rc10_boxSupp]
  apply rc10_card_via_support
  intro ω
  rw [rc10_box_increasing_iff hA hB ω]
  constructor
  · rintro ⟨K, L, hKL, hKsub, hLsub, hKA, hLB⟩
    refine ⟨K, L, hKL, hKsub, hLsub, ?_, ?_⟩
    · simp only [eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨supportCfg K, hKA, cfgSupport_supportCfg K⟩
    · simp only [eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨supportCfg L, hLB, cfgSupport_supportCfg L⟩
  · rintro ⟨K, L, hKL, hKsub, hLsub, hKA, hLB⟩
    refine ⟨K, L, hKL, hKsub, hLsub, ?_, ?_⟩
    · simp only [eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hKA
      obtain ⟨ω', hω', hω'K⟩ := hKA
      rw [← hω'K, supportCfg_cfgSupport]; exact hω'
    · simp only [eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hLB
      obtain ⟨ω', hω', hω'L⟩ := hLB
      rw [← hω'L, supportCfg_cfgSupport]; exact hω'



theorem rc10_mem_iff_eventFamily (A : Set (ConfigSpace α)) (ω : ConfigSpace α) :
    ω ∈ A ↔ cfgSupport ω ∈ eventFamily A := by
  conv_lhs => rw [← rit_familyEvent_eventFamily A]
  rfl

open Classical in




theorem rc10_card_reflInter_eq (A B : Set (ConfigSpace α)) :
    #(univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B))
      = #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
  classical
  rw [rc10_reflInter]
  apply rc10_card_via_support
  intro ω
  simp only [Set.mem_inter_iff, rmr_mem_reflect]
  rw [rc10_mem_iff_eventFamily A ω, rc10_mem_iff_eventFamily B (rmr_compl ω),
    rc10_cfgSupport_compl]













def rc10_BKRSetFamily : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    IsUpperSet (𝒜 : Set (Finset (Fin n))) → IsUpperSet (ℬ : Set (Finset (Fin n))) →
      #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)

open Classical in




theorem rc10_deficit_incInc_of_bkr (h : rc10_BKRSetFamily) {n : ℕ}
    {A B : Set (ConfigSpace (Fin n))} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    rc5_deficit A B ≤ 0 := by
  rw [rc5_deficit, rc10_card_box_eq A B hA hB, rc10_card_reflInter_eq A B]
  have hbkr := h n (eventFamily A) (eventFamily B) (rc10_isUpperSet_eventFamily hA)
    (rc10_isUpperSet_eventFamily hB)
  have : (#(rc10_boxSupp (eventFamily A) (eventFamily B)) : ℤ)
      ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by exact_mod_cast hbkr
  omega












def rc10_DeficitBridgeIncInc : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), IsIncreasing A → IsIncreasing B →
    rc5_deficit A B ≤ 0




theorem rc10_deficitIncInc_of_bkr (h : rc10_BKRSetFamily) : rc10_DeficitBridgeIncInc :=
  fun _ _ _ hA hB => rc10_deficit_incInc_of_bkr h hA hB

open Classical in






theorem rc10_bkr_of_deficitIncInc (h : rc10_DeficitBridgeIncInc) : rc10_BKRSetFamily := by
  intro n 𝒜 ℬ h𝒜 hℬ
  
  set A := familyEvent 𝒜 with hA
  set B := familyEvent ℬ with hB
  have hAinc : IsIncreasing A := by
    intro ω ω' hωω' hω
    simp only [hA, mem_familyEvent] at hω ⊢
    exact h𝒜 (Finset.coe_subset.mpr (cfgSupport_subset_of_le hωω')) hω
  have hBinc : IsIncreasing B := by
    intro ω ω' hωω' hω
    simp only [hB, mem_familyEvent] at hω ⊢
    exact hℬ (Finset.coe_subset.mpr (cfgSupport_subset_of_le hωω')) hω
  have hdef := h n A B hAinc hBinc
  
  have hEA : eventFamily A = 𝒜 := rc10_eventFamily_familyEvent 𝒜
  have hEB : eventFamily B = ℬ := rc10_eventFamily_familyEvent ℬ
  rw [rc5_deficit, rc10_card_box_eq A B hAinc hBinc, rc10_card_reflInter_eq A B, hEA, hEB] at hdef
  have : (#(rc10_boxSupp 𝒜 ℬ) : ℤ) ≤ #(rc10_reflInter 𝒜 ℬ) := by linarith [hdef]
  exact_mod_cast this


theorem rc10_bkr_iff_deficitIncInc : rc10_BKRSetFamily ↔ rc10_DeficitBridgeIncInc :=
  ⟨rc10_deficitIncInc_of_bkr, rc10_bkr_of_deficitIncInc⟩














theorem rc10_deficitIncInc_of_deficitBridge (h : rc7_DeficitBridge) : rc10_DeficitBridgeIncInc :=
  fun n A B _ _ => h n A B









theorem rc10_deficitBridge_iff_incInc_and_nonmono :
    rc7_DeficitBridge ↔
      (rc10_DeficitBridgeIncInc
        ∧ ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))),
            (¬ IsIncreasing A ∧ ¬ IsDecreasing A) ∨ (¬ IsIncreasing B ∧ ¬ IsDecreasing B) →
              rc5_deficit A B ≤ 0) := by
  constructor
  · intro h
    exact ⟨rc10_deficitIncInc_of_deficitBridge h, fun n A B _ => h n A B⟩
  · rintro ⟨hII, hNM⟩ n A B
    by_cases hAi : IsIncreasing A
    · by_cases hBi : IsIncreasing B
      · exact hII n A B hAi hBi
      · by_cases hBd : IsDecreasing B
        · exact rc8_deficit_le_zero_inc_dec hAi hBd
        · exact hNM n A B (Or.inr ⟨hBi, hBd⟩)
    · by_cases hAd : IsDecreasing A
      · by_cases hBi : IsIncreasing B
        · exact rc8_deficit_le_zero_dec_inc hAd hBi
        · by_cases hBd : IsDecreasing B
          · exact rc9_decDec_of_incInc (fun {C D} hC hD => hII n C D hC hD) hAd hBd
          · exact hNM n A B (Or.inr ⟨hBi, hBd⟩)
      · exact hNM n A B (Or.inl ⟨hAi, hAd⟩)















theorem rc10_ad_product_bound {β : Type*} [DecidableEq β] (𝒜 ℬ : Finset (Finset β)) :
    #𝒜 * #ℬ ≤ #(𝒜 ⊼ ℬ) * #(𝒜 ⊻ ℬ) :=
  Finset.le_card_infs_mul_card_sups 𝒜 ℬ







open Classical in


theorem rc10_deficit_incInc_one (A B : Set (ConfigSpace (Fin 1)))
    (_ : IsIncreasing A) (_ : IsIncreasing B) : rc5_deficit A B ≤ 0 :=
  rc9_deficit_one A B

open Classical in




theorem rc10_boxSupp_univ {β : Type*} [Fintype β] [DecidableEq β] :
    rc10_boxSupp (univ : Finset (Finset β)) univ = univ := by
  classical
  ext S
  simp only [rc10_boxSupp, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact ⟨∅, ∅, Finset.disjoint_empty_left ∅, Finset.empty_subset S, Finset.empty_subset S, trivial⟩



























theorem rc10_cardform_setfamily_reduction :
    (rc10_BKRSetFamily ↔ rc10_DeficitBridgeIncInc)
      ∧ (rc7_DeficitBridge → rc10_DeficitBridgeIncInc)
      ∧ (rc7_DeficitBridge ↔
          (rc10_DeficitBridgeIncInc
            ∧ ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))),
                (¬ IsIncreasing A ∧ ¬ IsDecreasing A) ∨ (¬ IsIncreasing B ∧ ¬ IsDecreasing B) →
                  rc5_deficit A B ≤ 0)) :=
  ⟨rc10_bkr_iff_deficitIncInc,
    rc10_deficitIncInc_of_deficitBridge,
    rc10_deficitBridge_iff_incInc_and_nonmono⟩

end StatMech.Walls
