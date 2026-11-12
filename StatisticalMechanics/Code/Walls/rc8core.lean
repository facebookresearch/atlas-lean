/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Code.Walls.rc7core
import Code.Inequalities.Harris
import Code.Inequalities.Reimer

open Finset MeasureTheory
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]







noncomputable def rc8_half : ℝ≥0 := 1 / 2


lemma rc8_half_le_one : (rc8_half : ℝ≥0) ≤ 1 := by unfold rc8_half; norm_num


lemma rc8_half_singleton_bool (b : Bool) :
    (bernoulliMeasure rc8_half rc8_half_le_one).real {b} = (1 / 2 : ℝ) := by
  cases b
  · rw [Measure.real, bernoulliMeasure_apply_false, ENNReal.coe_toReal,
      NNReal.coe_sub rc8_half_le_one]
    norm_num [rc8_half]
  · rw [Measure.real, bernoulliMeasure_apply_true, ENNReal.coe_toReal]
    norm_num [rc8_half]

omit [DecidableEq α] in

lemma rc8_half_singleton (ω : ConfigSpace α) :
    (bernoulliProductMeasure (E := α) rc8_half rc8_half_le_one).real {ω}
      = (1 / 2) ^ (Fintype.card α) := by
  rw [bernoulliProductMeasure.real_singleton,
    Finset.prod_congr rfl (fun e _ => rc8_half_singleton_bool (ω e)), Finset.prod_const]
  rfl

open Classical in


lemma rc8_card_bridge (S : Set (ConfigSpace α)) :
    (bernoulliProductMeasure (E := α) rc8_half rc8_half_le_one).real S
      = (#(univ.filter (fun ω => ω ∈ S)) : ℝ) * (1 / 2) ^ (Fintype.card α) := by
  rw [bernoulliProductMeasure.real_eq_sum]
  have hpt : ∀ ω : ConfigSpace α,
      S.indicator (fun _ => (1 : ℝ)) ω
          * (bernoulliProductMeasure (E := α) rc8_half rc8_half_le_one).real {ω}
        = S.indicator (fun _ => (1 : ℝ)) ω * (1 / 2) ^ (Fintype.card α) :=
    fun ω => by rw [rc8_half_singleton ω]
  rw [Finset.sum_congr rfl (fun ω _ => hpt ω), ← Finset.sum_mul]
  congr 1
  rw [Finset.sum_indicator_eq_sum_filter]
  simp [Finset.sum_const]










lemma rc8_antiHarris {p : ℝ≥0} (hp : p ≤ 1) {A B : Set (ConfigSpace α)}
    (hA : IsIncreasing A) (hB : IsDecreasing B) :
    (bernoulliProductMeasure (E := α) p hp).real (A ∩ B)
      ≤ (bernoulliProductMeasure (E := α) p hp).real A
        * (bernoulliProductMeasure (E := α) p hp).real B := by
  set μ := bernoulliProductMeasure (E := α) p hp with hμ
  have hprob : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hBc : IsIncreasing Bᶜ := IsLowerSet.compl hB
  have hh := harris_inequality (E := α) hp hA hBc
  have hcompl : μ.real Bᶜ = 1 - μ.real B := by
    rw [measureReal_compl (DiscreteMeasurableSpace.forall_measurableSet B), probReal_univ]
  have hsplit : μ.real (A ∩ Bᶜ) = μ.real A - μ.real (A ∩ B) := by
    have hd : Disjoint (A ∩ B) (A ∩ Bᶜ) := by
      apply Set.disjoint_left.mpr; rintro x ⟨_, hxB⟩ ⟨_, hxBc⟩; exact hxBc hxB
    have hu : (A ∩ B) ∪ (A ∩ Bᶜ) = A := by
      rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
    have := measureReal_union (μ := μ) hd (DiscreteMeasurableSpace.forall_measurableSet _)
    rw [hu] at this; linarith
  rw [hcompl, hsplit] at hh; nlinarith [hh]


lemma rc8_antiHarris' {p : ℝ≥0} (hp : p ≤ 1) {A B : Set (ConfigSpace α)}
    (hA : IsDecreasing A) (hB : IsIncreasing B) :
    (bernoulliProductMeasure (E := α) p hp).real (A ∩ B)
      ≤ (bernoulliProductMeasure (E := α) p hp).real A
        * (bernoulliProductMeasure (E := α) p hp).real B := by
  have h := rc8_antiHarris hp hB hA
  rw [Set.inter_comm, mul_comm] at h
  exact h



lemma rc8_harrisDec {p : ℝ≥0} (hp : p ≤ 1) {A B : Set (ConfigSpace α)}
    (hA : IsDecreasing A) (hB : IsDecreasing B) :
    (bernoulliProductMeasure (E := α) p hp).real A
        * (bernoulliProductMeasure (E := α) p hp).real B
      ≤ (bernoulliProductMeasure (E := α) p hp).real (A ∩ B) := by
  set μ := bernoulliProductMeasure (E := α) p hp with hμ
  have hprob : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hAc : IsIncreasing Aᶜ := IsLowerSet.compl hA
  have hBc : IsIncreasing Bᶜ := IsLowerSet.compl hB
  have hh := harris_inequality (E := α) hp hAc hBc
  have cA : μ.real Aᶜ = 1 - μ.real A := by
    rw [measureReal_compl (DiscreteMeasurableSpace.forall_measurableSet A), probReal_univ]
  have cB : μ.real Bᶜ = 1 - μ.real B := by
    rw [measureReal_compl (DiscreteMeasurableSpace.forall_measurableSet B), probReal_univ]
  have hcap : Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ := by rw [Set.compl_union]
  have cAB : μ.real (Aᶜ ∩ Bᶜ) = 1 - μ.real (A ∪ B) := by
    rw [hcap, measureReal_compl (DiscreteMeasurableSpace.forall_measurableSet (A ∪ B)),
      probReal_univ]
  have hunion : μ.real (A ∪ B) = μ.real A + μ.real B - μ.real (A ∩ B) := by
    have := measureReal_union_add_inter (μ := μ) (s := A)
      (DiscreteMeasurableSpace.forall_measurableSet B)
    linarith
  rw [cA, cB, cAB, hunion] at hh; nlinarith [hh]







omit [Fintype α] [DecidableEq α] in

lemma rc8_isDecreasing_reflect {A : Set (ConfigSpace α)} (hA : IsIncreasing A) :
    IsDecreasing (rmr_reflect A) := by
  intro ω ω' hωω' hω
  simp only [rmr_reflect, Set.mem_preimage] at hω ⊢
  exact hA (flipCfg_antitone (E := α) (ω := ω') (ω' := ω) hωω') hω


lemma rc8_reflect_prob (B : Set (ConfigSpace α)) :
    (bernoulliProductMeasure (E := α) rc8_half rc8_half_le_one).real (rmr_reflect B)
      = (bernoulliProductMeasure (E := α) rc8_half rc8_half_le_one).real B := by
  rw [rc8_card_bridge, rc8_card_bridge, rmr_card_reflect B]



open Classical in



theorem rc8_cardForm_inc_dec {A B : Set (ConfigSpace α)}
    (hA : IsIncreasing A) (hB : IsDecreasing B) :
    #(univ.filter (fun ω => ω ∈ disjointOccurrence A B))
      ≤ #(univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
  set μ := bernoulliProductMeasure (E := α) rc8_half rc8_half_le_one with hμ
  have hrB : IsIncreasing (rmr_reflect B) := isIncreasing_flip_preimage hB
  have h1 : μ.real (disjointOccurrence A B) ≤ μ.real (A ∩ B) :=
    measureReal_mono (StatMech.disjointOccurrence_subset_inter A B)
  have h2 : μ.real (A ∩ B) ≤ μ.real A * μ.real B := rc8_antiHarris rc8_half_le_one hA hB
  have h3 : μ.real A * μ.real (rmr_reflect B) ≤ μ.real (A ∩ rmr_reflect B) :=
    harris_inequality rc8_half_le_one hA hrB
  have hrefl : μ.real (rmr_reflect B) = μ.real B := rc8_reflect_prob B
  have hchain : μ.real (disjointOccurrence A B) ≤ μ.real (A ∩ rmr_reflect B) :=
    calc μ.real (disjointOccurrence A B)
        ≤ μ.real (A ∩ B) := h1
      _ ≤ μ.real A * μ.real B := h2
      _ = μ.real A * μ.real (rmr_reflect B) := by rw [hrefl]
      _ ≤ μ.real (A ∩ rmr_reflect B) := h3
  rw [hμ, rc8_card_bridge, rc8_card_bridge] at hchain
  have hpos : (0 : ℝ) < (1 / 2) ^ (Fintype.card α) := by positivity
  have hcast := Nat.cast_le.mp (le_of_mul_le_mul_right hchain hpos)
  convert hcast using 3

open Classical in



theorem rc8_cardForm_dec_inc {A B : Set (ConfigSpace α)}
    (hA : IsDecreasing A) (hB : IsIncreasing B) :
    #(univ.filter (fun ω => ω ∈ disjointOccurrence A B))
      ≤ #(univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
  set μ := bernoulliProductMeasure (E := α) rc8_half rc8_half_le_one with hμ
  have hrB : IsDecreasing (rmr_reflect B) := rc8_isDecreasing_reflect hB
  have h1 : μ.real (disjointOccurrence A B) ≤ μ.real (A ∩ B) :=
    measureReal_mono (StatMech.disjointOccurrence_subset_inter A B)
  have h2 : μ.real (A ∩ B) ≤ μ.real A * μ.real B := rc8_antiHarris' rc8_half_le_one hA hB
  have h3 : μ.real A * μ.real (rmr_reflect B) ≤ μ.real (A ∩ rmr_reflect B) :=
    rc8_harrisDec rc8_half_le_one hA hrB
  have hrefl : μ.real (rmr_reflect B) = μ.real B := rc8_reflect_prob B
  have hchain : μ.real (disjointOccurrence A B) ≤ μ.real (A ∩ rmr_reflect B) :=
    calc μ.real (disjointOccurrence A B)
        ≤ μ.real (A ∩ B) := h1
      _ ≤ μ.real A * μ.real B := h2
      _ = μ.real A * μ.real (rmr_reflect B) := by rw [hrefl]
      _ ≤ μ.real (A ∩ rmr_reflect B) := h3
  rw [hμ, rc8_card_bridge, rc8_card_bridge] at hchain
  have hpos : (0 : ℝ) < (1 / 2) ^ (Fintype.card α) := by positivity
  have hcast := Nat.cast_le.mp (le_of_mul_le_mul_right hchain hpos)
  convert hcast using 3



open Classical in


theorem rc8_deficit_le_zero_inc_dec {A B : Set (ConfigSpace α)}
    (hA : IsIncreasing A) (hB : IsDecreasing B) : rc5_deficit A B ≤ 0 := by
  rw [rc5_deficit]
  have h := rc8_cardForm_inc_dec hA hB
  have : (#(univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) : ℤ)
      ≤ #(univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by exact_mod_cast h
  omega

open Classical in


theorem rc8_deficit_le_zero_dec_inc {A B : Set (ConfigSpace α)}
    (hA : IsDecreasing A) (hB : IsIncreasing B) : rc5_deficit A B ≤ 0 := by
  rw [rc5_deficit]
  have h := rc8_cardForm_dec_inc hA hB
  have : (#(univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) : ℤ)
      ≤ #(univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by exact_mod_cast h
  omega



theorem rc8_reimerCardForm_inc_dec {A B : Set (ConfigSpace α)}
    (hA : IsIncreasing A) (hB : IsDecreasing B) : StatMech.poc_ReimerCardForm A B :=
  (rc5_reimerCardForm_iff_deficit A B).mpr (rc8_deficit_le_zero_inc_dec hA hB)



theorem rc8_reimerCardForm_dec_inc {A B : Set (ConfigSpace α)}
    (hA : IsDecreasing A) (hB : IsIncreasing B) : StatMech.poc_ReimerCardForm A B :=
  (rc5_reimerCardForm_iff_deficit A B).mpr (rc8_deficit_le_zero_dec_inc hA hB)















def rc8_DeficitBridgeNonOpp : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))),
    ¬ ((IsIncreasing A ∧ IsDecreasing B) ∨ (IsDecreasing A ∧ IsIncreasing B)) →
      rc5_deficit A B ≤ 0





theorem rc8_deficitBridge_iff_nonOpp :
    rc7_DeficitBridge ↔ rc8_DeficitBridgeNonOpp := by
  constructor
  · intro h n A B _; exact h n A B
  · intro h n A B
    by_cases hopp : (IsIncreasing A ∧ IsDecreasing B) ∨ (IsDecreasing A ∧ IsIncreasing B)
    · rcases hopp with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · exact rc8_deficit_le_zero_inc_dec hA hB
      · exact rc8_deficit_le_zero_dec_inc hA hB
    · exact h n A B hopp



theorem rc8_reimerCardFormAll_of_nonOpp (h : rc8_DeficitBridgeNonOpp) : ReimerCardFormAll :=
  rc7_reimerCardFormAll_of_deficitBridge (rc8_deficitBridge_iff_nonOpp.mpr h)






open Classical in



theorem rc8_deficit_univ_univ :
    rc5_deficit (Set.univ : Set (ConfigSpace α)) Set.univ ≤ 0 :=
  rc8_deficit_le_zero_inc_dec (by simpa using isUpperSet_univ) (by simpa using isLowerSet_univ)

















theorem rc8_cardform_oppositeMonotone :
    (∀ {A B : Set (ConfigSpace α)}, IsIncreasing A → IsDecreasing B → rc5_deficit A B ≤ 0)
      ∧ (∀ {A B : Set (ConfigSpace α)}, IsDecreasing A → IsIncreasing B → rc5_deficit A B ≤ 0)
      ∧ (rc7_DeficitBridge ↔ rc8_DeficitBridgeNonOpp)
      ∧ (rc8_DeficitBridgeNonOpp → ReimerCardFormAll) :=
  ⟨fun hA hB => rc8_deficit_le_zero_inc_dec hA hB,
    fun hA hB => rc8_deficit_le_zero_dec_inc hA hB,
    rc8_deficitBridge_iff_nonOpp,
    rc8_reimerCardFormAll_of_nonOpp⟩

end StatMech.Walls
