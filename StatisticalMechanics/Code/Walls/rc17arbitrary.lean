/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































































import Code.Walls.rc16sliceunion
import Code.Walls.rc9core
import Code.Walls.rc8core
import Code.Inequalities.Reimer
import Code.Inequalities.ReimerButterflyInjClose

open Finset MeasureTheory
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]






open Classical in


theorem rc17_deficit_incInc {n : ℕ} {A B : Set (ConfigSpace (Fin n))}
    (hA : IsIncreasing A) (hB : IsIncreasing B) : rc5_deficit A B ≤ 0 :=
  rc16_deficitBridgeIncInc n A B hA hB

open Classical in



theorem rc17_deficit_decDec {n : ℕ} {A B : Set (ConfigSpace (Fin n))}
    (hA : IsDecreasing A) (hB : IsDecreasing B) : rc5_deficit A B ≤ 0 :=
  rc9_decDec_of_incInc (fun {C D} hC hD => rc16_deficitBridgeIncInc n C D hC hD) hA hB

open Classical in





theorem rc17_deficit_le_zero_of_bothMonotone {n : ℕ} {A B : Set (ConfigSpace (Fin n))}
    (hA : IsIncreasing A ∨ IsDecreasing A) (hB : IsIncreasing B ∨ IsDecreasing B) :
    rc5_deficit A B ≤ 0 := by
  rcases hA with hAi | hAd
  · rcases hB with hBi | hBd
    · exact rc17_deficit_incInc hAi hBi
    · exact rc8_deficit_le_zero_inc_dec hAi hBd
  · rcases hB with hBi | hBd
    · exact rc8_deficit_le_zero_dec_inc hAd hBi
    · exact rc17_deficit_decDec hAd hBd











def rc17_NonMonotoneDeficit : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))),
    (¬ IsIncreasing A ∧ ¬ IsDecreasing A) ∨ (¬ IsIncreasing B ∧ ¬ IsDecreasing B) →
      rc5_deficit A B ≤ 0







open Classical in




theorem rc17_deficitBridge_of_nonMonotone (h : rc17_NonMonotoneDeficit) : rc7_DeficitBridge := by
  intro n A B
  by_cases hAi : IsIncreasing A
  · by_cases hBi : IsIncreasing B
    · exact rc17_deficit_le_zero_of_bothMonotone (Or.inl hAi) (Or.inl hBi)
    · by_cases hBd : IsDecreasing B
      · exact rc17_deficit_le_zero_of_bothMonotone (Or.inl hAi) (Or.inr hBd)
      · exact h n A B (Or.inr ⟨hBi, hBd⟩)
  · by_cases hAd : IsDecreasing A
    · by_cases hBi : IsIncreasing B
      · exact rc17_deficit_le_zero_of_bothMonotone (Or.inr hAd) (Or.inl hBi)
      · by_cases hBd : IsDecreasing B
        · exact rc17_deficit_le_zero_of_bothMonotone (Or.inr hAd) (Or.inr hBd)
        · exact h n A B (Or.inr ⟨hBi, hBd⟩)
    · exact h n A B (Or.inl ⟨hAi, hAd⟩)




theorem rc17_nonMonotone_of_deficitBridge (h : rc7_DeficitBridge) : rc17_NonMonotoneDeficit :=
  fun n A B _ => h n A B





theorem rc17_deficitBridge_iff_nonMonotone : rc7_DeficitBridge ↔ rc17_NonMonotoneDeficit :=
  ⟨rc17_nonMonotone_of_deficitBridge, rc17_deficitBridge_of_nonMonotone⟩










theorem rc17_reimerCardFormAll_of_nonMonotone (h : rc17_NonMonotoneDeficit) : ReimerCardFormAll :=
  rc7_reimerCardFormAll_of_deficitBridge (rc17_deficitBridge_of_nonMonotone h)



theorem rc17_reimerResidue_of_nonMonotone (h : rc17_NonMonotoneDeficit) : ReimerResidue :=
  rc7_reimerCardFormAll_iff_residue.mp (rc17_reimerCardFormAll_of_nonMonotone h)





theorem rc17_reimerWprobCore_of_nonMonotone (h : rc17_NonMonotoneDeficit) : ReimerWprobCore :=
  rc3_core_reimerWprobCore_of_residue (rc17_reimerResidue_of_nonMonotone h)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in



theorem rc17_reimer_inequality_of_nonMonotone (h : rc17_NonMonotoneDeficit) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_core (rc17_reimerWprobCore_of_nonMonotone h) hp A B


















noncomputable def rc17_spreadEvent {n : ℕ} (A : Set (ConfigSpace (Fin n))) :
    Set (ConfigSpace (Fin n ⊕ Fin n)) :=
  {η | (fun i => η (Sum.inl i)) ∈ A}




theorem rc17_spread_increasing_of_increasing {n : ℕ} {A : Set (ConfigSpace (Fin n))}
    (hA : IsIncreasing A) : IsIncreasing (rc17_spreadEvent A) := by
  intro η η' hηη' hη
  change (fun i => η' (Sum.inl i)) ∈ A
  refine hA (fun i => ?_) hη
  exact hηη' (Sum.inl i)

open Classical in







theorem rc17_spread_not_increasing :
    ¬ IsIncreasing (rc17_spreadEvent rbi_A) := by
  intro hcon
  set botC : ConfigSpace (Fin 2 ⊕ Fin 2) := fun _ => false with hbot
  set topC : ConfigSpace (Fin 2 ⊕ Fin 2) := fun _ => true with htop
  have hle : botC ≤ topC := by intro x; simp [hbot, htop]
  have hbotmem : botC ∈ rc17_spreadEvent rbi_A := by
    change (fun i => botC (Sum.inl i)) ∈ rbi_A
    simp [rbi_A, hbot]
  have htopmem : topC ∈ rc17_spreadEvent rbi_A := hcon hle hbotmem
  have : (fun i => topC (Sum.inl i)) ∈ rbi_A := htopmem
  simp [rbi_A, htop] at this









private def rc17_fcfg (a b : Bool) : ConfigSpace (Fin 2) := fun i => if i = 0 then a else b

open Classical in


theorem rc17_rbiB_not_increasing : ¬ IsIncreasing rbi_B := by
  rw [IsIncreasing, IsUpperSet]; intro h
  have hle : rc17_fcfg false false ≤ rc17_fcfg true false := by
    intro i; fin_cases i <;> simp [rc17_fcfg]
  have hmem : rc17_fcfg false false ∈ rbi_B := by simp [rbi_B, rc17_fcfg]
  have := h hle hmem
  simp [rbi_B, rc17_fcfg] at this

open Classical in


theorem rc17_rbiB_not_decreasing : ¬ IsDecreasing rbi_B := by
  rw [IsDecreasing, IsLowerSet]; intro h
  have hle : rc17_fcfg true false ≤ rc17_fcfg true true := by
    intro i; fin_cases i <;> simp [rc17_fcfg]
  have hmem : rc17_fcfg true true ∈ rbi_B := by simp [rbi_B, rc17_fcfg]
  have := h hle hmem
  simp [rbi_B, rc17_fcfg] at this






theorem rc17_nonMonotone_rbi :
    ((¬ IsIncreasing rbi_A ∧ ¬ IsDecreasing rbi_A) ∨ (¬ IsIncreasing rbi_B ∧ ¬ IsDecreasing rbi_B))
      ∧ rc5_deficit rbi_A rbi_B ≤ 0 :=
  ⟨Or.inr ⟨rc17_rbiB_not_increasing, rc17_rbiB_not_decreasing⟩, rc7_deficit_rbi⟩















noncomputable def rc17_upClosure {n : ℕ} (A : Set (ConfigSpace (Fin n))) :
    Set (ConfigSpace (Fin n)) :=
  {ω | ∃ ω₀ ∈ A, ω₀ ≤ ω}


theorem rc17_subset_upClosure {n : ℕ} (A : Set (ConfigSpace (Fin n))) : A ⊆ rc17_upClosure A :=
  fun ω hω => ⟨ω, hω, le_refl ω⟩


theorem rc17_upClosure_increasing {n : ℕ} (A : Set (ConfigSpace (Fin n))) :
    IsIncreasing (rc17_upClosure A) := by
  intro ω ω' hωω' hω
  obtain ⟨ω₀, hω₀, hle⟩ := hω
  exact ⟨ω₀, hω₀, hle.trans hωω'⟩



theorem rc17_box_subset_up {n : ℕ} (A B : Set (ConfigSpace (Fin n))) :
    disjointOccurrence A B ⊆ disjointOccurrence (rc17_upClosure A) (rc17_upClosure B) :=
  disjointOccurrence_mono (rc17_subset_upClosure A) (rc17_subset_upClosure B)

open Classical in











theorem rc17_box_le_reflInter_up {n : ℕ} (A B : Set (ConfigSpace (Fin n))) :
    (#(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ disjointOccurrence A B)) : ℤ)
      ≤ #(univ.filter (fun ω : ConfigSpace (Fin n) =>
            ω ∈ rc17_upClosure A ∩ rmr_reflect (rc17_upClosure B))) := by
  have hbox : #(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ disjointOccurrence A B))
      ≤ #(univ.filter (fun ω : ConfigSpace (Fin n) =>
            ω ∈ disjointOccurrence (rc17_upClosure A) (rc17_upClosure B))) := by
    apply Finset.card_le_card
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact rc17_box_subset_up A B hω
  have hdef : rc5_deficit (rc17_upClosure A) (rc17_upClosure B) ≤ 0 :=
    rc16_deficitBridgeIncInc n (rc17_upClosure A) (rc17_upClosure B)
      (rc17_upClosure_increasing A) (rc17_upClosure_increasing B)
  rw [rc5_deficit] at hdef
  have hbox' : (#(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ disjointOccurrence A B)) : ℤ)
      ≤ #(univ.filter (fun ω : ConfigSpace (Fin n) =>
            ω ∈ disjointOccurrence (rc17_upClosure A) (rc17_upClosure B))) := by exact_mod_cast hbox
  omega





theorem rc17_reflInter_subset_up {n : ℕ} (A B : Set (ConfigSpace (Fin n))) :
    A ∩ rmr_reflect B ⊆ rc17_upClosure A ∩ rmr_reflect (rc17_upClosure B) := by
  rintro ω ⟨hA, hB⟩
  refine ⟨rc17_subset_upClosure A hA, ?_⟩
  rw [rmr_mem_reflect] at hB ⊢
  exact rc17_subset_upClosure B hB

open Classical in







theorem rc17_reflInter_card_le_up {n : ℕ} (A B : Set (ConfigSpace (Fin n))) :
    #(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ A ∩ rmr_reflect B))
      ≤ #(univ.filter (fun ω : ConfigSpace (Fin n) =>
            ω ∈ rc17_upClosure A ∩ rmr_reflect (rc17_upClosure B))) := by
  apply Finset.card_le_card
  intro ω hω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
  exact rc17_reflInter_subset_up A B hω










open Classical in












theorem rc17_functional_bkr_of_reimer (h : ReimerWprobCore) {n : ℕ} {ι κ : Type*}
    (A : ι → Set (ConfigSpace (Fin n))) (B : κ → Set (ConfigSpace (Fin n)))
    (K : ι → Set (Fin n)) (L : κ → Set (Fin n))
    (hA : ∀ i, DependsOn (A i) (K i)) (hB : ∀ j, DependsOn (B j) (L j))
    (φ : Fin n → Bool → ℝ) (hφ0 : ∀ i b, 0 ≤ φ i b) (hφ1 : ∀ i, φ i false + φ i true = 1) :
    wprob φ {ω | ∃ i j, Disjoint (K i) (L j) ∧ ω ∈ A i ∧ ω ∈ B j}
      ≤ wprob φ (⋃ i, A i) * wprob φ (⋃ j, B j) := by
  have hsub : {ω | ∃ i j, Disjoint (K i) (L j) ∧ ω ∈ A i ∧ ω ∈ B j}
      ⊆ disjointOccurrence (⋃ i, A i) (⋃ j, B j) := by
    rintro ω ⟨i, j, hKL, hAi, hBj⟩
    refine ⟨K i, L j, hKL, ?_, ?_⟩
    · exact ((hA i).occursOn_iff ω |>.mpr hAi).mono_event (Set.subset_iUnion A i)
    · exact ((hB j).occursOn_iff ω |>.mpr hBj).mono_event (Set.subset_iUnion B j)
  calc wprob φ {ω | ∃ i j, Disjoint (K i) (L j) ∧ ω ∈ A i ∧ ω ∈ B j}
      ≤ wprob φ (disjointOccurrence (⋃ i, A i) (⋃ j, B j)) := wprob_mono hφ0 hsub
    _ ≤ wprob φ (⋃ i, A i) * wprob φ (⋃ j, B j) := h n φ hφ0 hφ1 _ _



set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open Classical in


























theorem rc17_arbitrary_reimer :
    (∀ {n : ℕ} {A B : Set (ConfigSpace (Fin n))},
        (IsIncreasing A ∨ IsDecreasing A) → (IsIncreasing B ∨ IsDecreasing B) →
          rc5_deficit A B ≤ 0)
      ∧ (rc7_DeficitBridge ↔ rc17_NonMonotoneDeficit)
      ∧ (rc17_NonMonotoneDeficit → ReimerWprobCore)
      ∧ ¬ IsIncreasing (rc17_spreadEvent rbi_A)
      ∧ (∀ {n : ℕ} (A B : Set (ConfigSpace (Fin n))),
          (#(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ disjointOccurrence A B)) : ℤ)
            ≤ #(univ.filter (fun ω : ConfigSpace (Fin n) =>
                  ω ∈ rc17_upClosure A ∩ rmr_reflect (rc17_upClosure B)))) :=
  ⟨fun {_ _ _} hA hB => rc17_deficit_le_zero_of_bothMonotone hA hB,
    rc17_deficitBridge_iff_nonMonotone,
    rc17_reimerWprobCore_of_nonMonotone,
    rc17_spread_not_increasing,
    fun {_} A B => rc17_box_le_reflInter_up A B⟩

end StatMech.Walls
