/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Code.Inequalities.ReimerSwapInjClose

open Finset MeasureTheory
open scoped NNReal FinsetFamily

namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]









def poc_flip (d : α → Bool) (ω : ConfigSpace α) : ConfigSpace α :=
  fun a => if d a then !ω a else ω a


def poc_keyFlip (k : ConfigSpace α × ConfigSpace α) : ConfigSpace α → ConfigSpace α :=
  poc_flip (fun a => decide (k.1 a ≠ k.2 a))

omit [Fintype α] [DecidableEq α] in


theorem poc_snd_eq (p : ConfigSpace α × ConfigSpace α) (k : ConfigSpace α × ConfigSpace α)
    (hk : orbitKey p = k) : p.2 = poc_keyFlip k p.1 := by
  funext a
  have hor := congrFun (congrArg Prod.fst hk) a
  have hand := congrFun (congrArg Prod.snd hk) a
  simp only [orbitKey] at hor hand
  simp only [poc_keyFlip, poc_flip, ← hor, ← hand]
  revert hor hand
  cases hp1 : p.1 a <;> cases hp2 : p.2 a <;> simp_all



open Classical in

noncomputable def poc_slabBox (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    Finset (ConfigSpace α) :=
  Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B ∧
    orbitKey (ω, poc_keyFlip k ω) = k)

open Classical in


noncomputable def poc_slabImg (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    Finset (ConfigSpace α) :=
  Finset.univ.filter (fun ω => ω ∈ A ∧ poc_keyFlip k ω ∈ B ∧
    orbitKey (ω, poc_keyFlip k ω) = k)



theorem poc_card_boxOrbit (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    #(boxOrbit A B k) = #(poc_slabBox A B k) := by
  classical
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    simp only [boxOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hbox, hk⟩ := hp
    have h2 := poc_snd_eq p k hk
    simp only [poc_slabBox, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hbox, ?_⟩
    rw [show (p.1, poc_keyFlip k p.1) = p from Prod.ext rfl h2.symm]; exact hk
  · intro p hp q hq hpq
    simp only [boxOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have h2p := poc_snd_eq p k hp.2
    have h2q := poc_snd_eq q k hq.2
    exact Prod.ext hpq (by rw [h2p, h2q, hpq])
  · intro ω hω
    simp only [poc_slabBox, Finset.mem_filter, Finset.mem_univ, true_and] at hω
    refine ⟨(ω, poc_keyFlip k ω), ?_, rfl⟩
    simp only [boxOrbit, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hω.1, hω.2⟩


theorem poc_card_imgOrbit (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    #(imgOrbit A B k) = #(poc_slabImg A B k) := by
  classical
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    simp only [imgOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hA, hB, hk⟩ := hp
    have h2 := poc_snd_eq p k hk
    simp only [poc_slabImg, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hA, ?_, ?_⟩
    · rw [← h2]; exact hB
    · rw [show (p.1, poc_keyFlip k p.1) = p from Prod.ext rfl h2.symm]; exact hk
  · intro p hp q hq hpq
    simp only [imgOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have h2p := poc_snd_eq p k hp.2.2
    have h2q := poc_snd_eq q k hq.2.2
    exact Prod.ext hpq (by rw [h2p, h2q, hpq])
  · intro ω hω
    simp only [poc_slabImg, Finset.mem_filter, Finset.mem_univ, true_and] at hω
    refine ⟨(ω, poc_keyFlip k ω), ?_, rfl⟩
    simp only [imgOrbit, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hω.1, hω.2.1, hω.2.2⟩





def poc_SlabCard (A B : Set (ConfigSpace α)) : Prop :=
  ∀ k : ConfigSpace α × ConfigSpace α, #(poc_slabBox A B k) ≤ #(poc_slabImg A B k)




theorem poc_perOrbitCard_iff_slabCard (A B : Set (ConfigSpace α)) :
    PerOrbitCard A B ↔ poc_SlabCard A B := by
  unfold PerOrbitCard poc_SlabCard
  constructor
  · intro h k; rw [← poc_card_boxOrbit, ← poc_card_imgOrbit]; exact h k
  · intro h k; rw [poc_card_boxOrbit, poc_card_imgOrbit]; exact h k








def poc_topKey : ConfigSpace α × ConfigSpace α := (fun _ => true, fun _ => false)

omit [Fintype α] [DecidableEq α] in

@[simp] theorem poc_keyFlip_top (ω : ConfigSpace α) :
    poc_keyFlip (poc_topKey : ConfigSpace α × ConfigSpace α) ω = fun a => !ω a := by
  funext a; simp only [poc_keyFlip, poc_flip, poc_topKey]; norm_num

omit [Fintype α] [DecidableEq α] in

@[simp] theorem poc_orbitKey_top (ω : ConfigSpace α) :
    orbitKey (ω, poc_keyFlip (poc_topKey : ConfigSpace α × ConfigSpace α) ω) = poc_topKey := by
  rw [poc_keyFlip_top]
  simp only [orbitKey, poc_topKey]
  apply Prod.ext <;> funext a <;> cases ω a <;> simp

open Classical in

theorem poc_slabBox_top (A B : Set (ConfigSpace α)) :
    poc_slabBox A B (poc_topKey) =
      Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B) := by
  apply Finset.filter_congr
  intro ω _
  simp only [poc_orbitKey_top, and_true]

open Classical in

theorem poc_slabImg_top (A B : Set (ConfigSpace α)) :
    poc_slabImg A B (poc_topKey) =
      Finset.univ.filter (fun ω => ω ∈ A ∧ (fun a => !ω a) ∈ B) := by
  apply Finset.filter_congr
  intro ω _
  rw [poc_orbitKey_top, poc_keyFlip_top]
  simp only [and_true]

open Classical in



def poc_ReimerCardForm (A B : Set (ConfigSpace α)) : Prop :=
  #(Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B)) ≤
    #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B))


theorem poc_slabCard_top_iff_reimerCardForm (A B : Set (ConfigSpace α)) :
    #(poc_slabBox A B poc_topKey) ≤ #(poc_slabImg A B poc_topKey) ↔ poc_ReimerCardForm A B := by
  rw [poc_slabBox_top, poc_slabImg_top]; rfl


theorem poc_reimerCardForm_of_slabCard (A B : Set (ConfigSpace α))
    (h : poc_SlabCard A B) : poc_ReimerCardForm A B :=
  (poc_slabCard_top_iff_reimerCardForm A B).mp (h poc_topKey)









omit [Fintype α] [DecidableEq α] in


theorem poc_membership (A B : Set (ConfigSpace α)) (ω τ : ConfigSpace α)
    (wK : α → Bool) (hA : OccursOn A {a | wK a = true} ω)
    (wL : α → Bool) (hB : OccursOn B {a | wL a = true} ω)
    (hdis : ∀ a, wK a = true → wL a = false) :
    swapGlue (fun a => !wK a) ω τ ∈ A ∧ swapGlue (fun a => !wK a) τ ω ∈ B := by
  refine ⟨hA _ ?_, hB _ ?_⟩
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha
    simp only [swapGlue_apply, ha, Bool.not_true, Bool.false_eq_true, if_false]
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha
    have haK : wK a = false := by
      cases hkk : wK a with
      | false => rfl
      | true => rw [hdis a hkk] at ha; exact absurd ha (by simp)
    simp only [swapGlue_apply, haK, Bool.not_false, if_true]













structure poc_WitnessData (A B : Set (ConfigSpace α)) where
  
  wK : ConfigSpace α → (α → Bool)
  
  wL : ConfigSpace α → (α → Bool)
  
  occA : ∀ ω, ω ∈ disjointOccurrence A B → OccursOn A {a | wK ω a = true} ω
  
  occB : ∀ ω, ω ∈ disjointOccurrence A B → OccursOn B {a | wL ω a = true} ω
  
  disj : ∀ ω, ω ∈ disjointOccurrence A B → ∀ a, wK ω a = true → wL ω a = false


def poc_swapSel (A B : Set (ConfigSpace α)) (W : poc_WitnessData A B) :
    ConfigSpace α × ConfigSpace α → (α → Bool) :=
  fun p => fun a => !(W.wK p.1 a)




def poc_WitnessInjection (A B : Set (ConfigSpace α)) : Prop :=
  ∃ W : poc_WitnessData A B,
    Set.InjOn (swapPair (poc_swapSel A B W))
      {p : ConfigSpace α × ConfigSpace α | p.1 ∈ disjointOccurrence A B}



theorem poc_swapInjection_of_witnessInjection (A B : Set (ConfigSpace α))
    (h : poc_WitnessInjection A B) : r2k_SwapInjection A B := by
  obtain ⟨W, hinj⟩ := h
  refine ⟨poc_swapSel A B W, ?_, hinj⟩
  intro p hp
  have := poc_membership A B p.1 p.2 (W.wK p.1) (W.occA p.1 hp) (W.wL p.1) (W.occB p.1 hp)
    (W.disj p.1 hp)
  simpa only [swapPair_fst, swapPair_snd, poc_swapSel] using this





theorem poc_rbi_Bwit_FF (wL : Fin 2 → Bool)
    (hB : OccursOn rbi_B {a | wL a = true} (rbi_cfg false false)) : wL 0 = true := by
  by_contra h
  have h0 : wL 0 = false := by cases hw : wL 0 with | false => rfl | true => exact absurd hw h
  have hmem := hB (rbi_cfg true false) (by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    fin_cases a
    · rw [show ((0 : Fin 2) = (⟨0, by omega⟩ : Fin 2)) from rfl] at h0
      exact absurd ha (by rw [h0]; simp)
    · rfl)
  simp only [rbi_B, Set.mem_setOf_eq, rbi_cfg_zero, rbi_cfg_one] at hmem
  exact hmem (by simp)


theorem poc_rbi_Bwit_FT (wL : Fin 2 → Bool)
    (hB : OccursOn rbi_B {a | wL a = true} (rbi_cfg false true)) (h0 : wL 0 = false) :
    wL 1 = true := by
  by_contra h
  have h1 : wL 1 = false := by cases hw : wL 1 with | false => rfl | true => exact absurd hw h
  have hmem := hB (rbi_cfg true false) (by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    fin_cases a
    · rw [show ((0 : Fin 2) = (⟨0, by omega⟩ : Fin 2)) from rfl] at h0
      exact absurd ha (by rw [h0]; simp)
    · rw [show ((1 : Fin 2) = (⟨1, by omega⟩ : Fin 2)) from rfl] at h1
      exact absurd ha (by rw [h1]; simp))
  simp only [rbi_B, Set.mem_setOf_eq, rbi_cfg_zero, rbi_cfg_one] at hmem
  exact hmem (by simp)


theorem poc_rbi_Awit_FF_one (wK : Fin 2 → Bool)
    (hA : OccursOn rbi_A {a | wK a = true} (rbi_cfg false false)) (h0 : wK 0 = false) :
    wK 1 = true := by
  by_contra h
  have h1 : wK 1 = false := by cases hw : wK 1 with | false => rfl | true => exact absurd hw h
  have hmem := hA (rbi_cfg true true) (by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    fin_cases a
    · rw [show ((0 : Fin 2) = (⟨0, by omega⟩ : Fin 2)) from rfl] at h0
      exact absurd ha (by rw [h0]; simp)
    · rw [show ((1 : Fin 2) = (⟨1, by omega⟩ : Fin 2)) from rfl] at h1
      exact absurd ha (by rw [h1]; simp))
  simp only [rbi_A, Set.mem_setOf_eq, rbi_cfg_zero, rbi_cfg_one] at hmem
  exact hmem (by simp)



theorem poc_rbi_Awit_FT_zero (wK : Fin 2 → Bool)
    (hA : OccursOn rbi_A {a | wK a = true} (rbi_cfg false true)) : wK 0 = true := by
  by_contra h
  have h0 : wK 0 = false := by cases hw : wK 0 with | false => rfl | true => exact absurd hw h
  have hmem := hA (rbi_cfg true true) (by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    fin_cases a
    · rw [show ((0 : Fin 2) = (⟨0, by omega⟩ : Fin 2)) from rfl] at h0
      exact absurd ha (by rw [h0]; simp)
    · rfl)
  simp only [rbi_A, Set.mem_setOf_eq, rbi_cfg_zero, rbi_cfg_one] at hmem
  exact hmem (by simp)


def poc_rbi_p1 : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) :=
  (rbi_cfg false false, rbi_cfg false true)

def poc_rbi_p2 : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) :=
  (rbi_cfg false true, rbi_cfg false false)







theorem poc_witnessInjection_rbi_false : ¬ poc_WitnessInjection rbi_A rbi_B := by
  rintro ⟨W, hinj⟩
  have hp1 : poc_rbi_p1.1 ∈ disjointOccurrence rbi_A rbi_B := rbi_FF_in_box
  have hp2 : poc_rbi_p2.1 ∈ disjointOccurrence rbi_A rbi_B := rbi_FT_in_box
  have hwLFF0 : W.wL (rbi_cfg false false) 0 = true :=
    poc_rbi_Bwit_FF _ (W.occB _ rbi_FF_in_box)
  have hwKFF0 : W.wK (rbi_cfg false false) 0 = false := by
    cases hw : W.wK (rbi_cfg false false) 0 with
    | false => rfl
    | true => rw [W.disj _ rbi_FF_in_box 0 hw] at hwLFF0; exact absurd hwLFF0 (by simp)
  have hwKFF1 : W.wK (rbi_cfg false false) 1 = true :=
    poc_rbi_Awit_FF_one _ (W.occA _ rbi_FF_in_box) hwKFF0
  have hwKFT0 : W.wK (rbi_cfg false true) 0 = true :=
    poc_rbi_Awit_FT_zero _ (W.occA _ rbi_FT_in_box)
  have hwLFT0 : W.wL (rbi_cfg false true) 0 = false := W.disj _ rbi_FT_in_box 0 hwKFT0
  have hwLFT1 : W.wL (rbi_cfg false true) 1 = true :=
    poc_rbi_Bwit_FT _ (W.occB _ rbi_FT_in_box) hwLFT0
  have hwKFT1 : W.wK (rbi_cfg false true) 1 = false := by
    cases hw : W.wK (rbi_cfg false true) 1 with
    | false => rfl
    | true => rw [W.disj _ rbi_FT_in_box 1 hw] at hwLFT1; exact absurd hwLFT1 (by simp)
  have hcol : swapPair (poc_swapSel rbi_A rbi_B W) poc_rbi_p1
      = swapPair (poc_swapSel rbi_A rbi_B W) poc_rbi_p2 := by
    apply Prod.ext <;> funext a <;> fin_cases a <;>
      simp only [swapPair_fst, swapPair_snd, poc_swapSel, swapGlue_apply, poc_rbi_p1, poc_rbi_p2,
        Fin.mk_zero, Fin.mk_one, rbi_cfg_zero, rbi_cfg_one, Fin.isValue,
        hwKFF0, hwKFF1, hwKFT0, hwKFT1, Bool.not_true, Bool.not_false] <;> rfl
  have heq : poc_rbi_p1 = poc_rbi_p2 := hinj hp1 hp2 hcol
  have hne : poc_rbi_p1 ≠ poc_rbi_p2 := by
    intro h
    have h2 := congrArg (fun q => q.1 1) h
    simp only [poc_rbi_p1, poc_rbi_p2, rbi_cfg_one] at h2
    exact absurd h2 (by decide)
  exact hne heq







theorem poc_slabCard_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    poc_SlabCard A B :=
  (poc_perOrbitCard_iff_slabCard A B).mp (perOrbitCard_of_disjoint_support hA hB hST)


theorem poc_slabCard_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : poc_SlabCard A B :=
  (poc_perOrbitCard_iff_slabCard A B).mp (perOrbitCard_of_box_empty hbox)



theorem poc_slabCard_rbi : poc_SlabCard rbi_A rbi_B :=
  (poc_perOrbitCard_iff_slabCard rbi_A rbi_B).mp perOrbitCard_rbi


theorem poc_reimerCardForm_rbi : poc_ReimerCardForm rbi_A rbi_B :=
  poc_reimerCardForm_of_slabCard rbi_A rbi_B poc_slabCard_rbi





theorem reimer_wprob_of_slabCard (φ : α → Bool → ℝ) (hφ0 : ∀ x b, 0 ≤ φ x b)
    (hφ1 : ∀ x, φ x false + φ x true = 1) {A B : Set (ConfigSpace α)}
    (h : poc_SlabCard A B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  reimer_wprob_of_perOrbitCard φ hφ0 hφ1 ((poc_perOrbitCard_iff_slabCard A B).mpr h)


def poc_SlabCardAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), poc_SlabCard A B


theorem reimer_wprob_core_of_slabCard (h : poc_SlabCardAll) : ReimerWprobCore :=
  reimer_wprob_core_of_perOrbitCard
    (fun n A B => (poc_perOrbitCard_iff_slabCard A B).mpr (h n A B))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in

theorem reimer_inequality_of_slabCard (h : poc_SlabCardAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_core (reimer_wprob_core_of_slabCard h) hp A B

end StatMech
