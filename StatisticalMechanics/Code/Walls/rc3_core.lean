/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Code.Walls.rc3_slabcardiffperkey
import Code.Walls.rc3_slabimgeqinter
import Code.Walls.rc3_doubledboxcount
import Code.Walls.rc3_hallforswapinjection
import Code.Walls.rc3_minimalwitnessencoded
import Code.Walls.rc2_core
import Code.Walls.rc2_dpairsdowndownmono
import Code.Walls.rc2_blendpoint

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]














def ReimerCardFormAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), poc_ReimerCardForm A B











theorem rc3_core_reimerCardFormAll_of_slabCardAll (h : StatMech.poc_SlabCardAll) :
    ReimerCardFormAll :=
  fun n A B => poc_reimerCardForm_of_slabCard A B (h n A B)

open Classical in




theorem rc3_core_perKey_top_iff_reimerCardForm (A B : Set (ConfigSpace α)) :
    rc3_PerKey A B poc_topKey ↔
      #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤
        #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) :=
  rc3_perKey_top A B






















theorem rc3_core_provedDAG {β : Type*} [DecidableEq β] (𝒜 ℬ : Finset (Finset β)) :
    ((boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ)
      ∧ (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ))
      ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ)
            - dpairsCount 𝒜 ℬ
          = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
            - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
                (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i))
      ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β))
            ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ))
      ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β,
            dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
              ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
  refine ⟨rc3_doubled_box_count 𝒜 ℬ, ?_, ?_, ?_, ?_⟩
  · intro i; exact rc2_dpairsCount_downDown_mono 𝒜 ℬ i
  · intro i; exact rc2_deficit_identity 𝒜 ℬ i
  · obtain ⟨cs, hcs, hmono, _⟩ := rc2_blendpoint_converges 𝒜
    exact ⟨cs, hcs, hmono ℬ⟩
  · intro h𝒜 hℬ i; exact rc2_blendpoint_favourable h𝒜 hℬ i













def ReimerResidue : Prop := StatMech.poc_SlabCardAll



theorem rc3_core_residue_iff_bridge : ReimerResidue ↔ rc_core_CountBoxBridge :=
  rc2_countBoxBridge_iff_slabCardAll.symm




theorem rc3_core_residue_iff_perKeyAll : ReimerResidue ↔ rc3_PerKeyAll :=
  rc3_perKeyAll_iff_slabCardAll.symm





theorem rc3_core_residue_iff_slabInjectionAll : ReimerResidue ↔ SlabInjectionAll := by
  constructor
  · intro h n A B; exact rc2_slabInjection_of_slabCard (h n A B)
  · intro h; exact rc2_slabCardAll_of_slabInjectionAll h




theorem rc3_core_reimerWprobCore_of_residue (h : ReimerResidue) : ReimerWprobCore :=
  reimer_wprob_core_of_slabCard h

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in



theorem rc3_core_reimer_inequality_of_residue (h : ReimerResidue) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_slabCard h hp A B












omit [Fintype α] [DecidableEq α] in




theorem rc3_core_slab_frozen {k : ConfigSpace α × ConfigSpace α} {ω : ConfigSpace α}
    (hk : ω ∈ rc2_slab k) (a : α) (hne : k.1 a = k.2 a) : ω a = k.1 a := by
  rw [rc2_mem_slab] at hk
  have hor := congrFun (congrArg Prod.fst hk) a
  simp only [orbitKey, poc_keyFlip, poc_flip,
    show (decide (k.1 a ≠ k.2 a)) = false by simp [hne],
    Bool.false_eq_true, if_false, Bool.or_self] at hor
  exact hor

omit [Fintype α] [DecidableEq α] in



theorem rc3_core_slab_differ_key {k : ConfigSpace α × ConfigSpace α} {ω : ConfigSpace α}
    (hk : ω ∈ rc2_slab k) (a : α) (hne : k.1 a ≠ k.2 a) :
    k.1 a = true ∧ k.2 a = false := by
  rw [rc2_mem_slab] at hk
  have hor := congrFun (congrArg Prod.fst hk) a
  have hand := congrFun (congrArg Prod.snd hk) a
  simp only [orbitKey, poc_keyFlip, poc_flip,
    show (decide (k.1 a ≠ k.2 a)) = true by simp [hne], if_true] at hor hand
  cases hw : ω a <;> simp_all

omit [Fintype α] [DecidableEq α] in





theorem rc3_core_slab_of_frozen {k : ConfigSpace α × ConfigSpace α} {ω : ConfigSpace α}
    (hvalid : ∀ a, k.1 a ≠ k.2 a → (k.1 a = true ∧ k.2 a = false))
    (hfroz : ∀ a, k.1 a = k.2 a → ω a = k.1 a) : ω ∈ rc2_slab k := by
  rw [rc2_mem_slab]
  apply Prod.ext <;> funext a <;> simp only [orbitKey, poc_keyFlip, poc_flip]
  · by_cases hne : k.1 a = k.2 a
    · simp only [show (decide (k.1 a ≠ k.2 a)) = false by simp [hne], Bool.false_eq_true,
        if_false, Bool.or_self]; exact hfroz a hne
    · obtain ⟨h1, h2⟩ := hvalid a hne
      simp only [show (decide (k.1 a ≠ k.2 a)) = true by simp [hne], if_true]
      cases hw : ω a <;> simp_all
  · by_cases hne : k.1 a = k.2 a
    · simp only [show (decide (k.1 a ≠ k.2 a)) = false by simp [hne], Bool.false_eq_true,
        if_false, Bool.and_self]; rw [hfroz a hne, hne]
    · obtain ⟨h1, h2⟩ := hvalid a hne
      simp only [show (decide (k.1 a ≠ k.2 a)) = true by simp [hne], if_true]
      cases hw : ω a <;> simp_all

omit [Fintype α] [DecidableEq α] in




theorem rc3_core_orbitKey_valid (p : ConfigSpace α × ConfigSpace α) (a : α)
    (hne : (orbitKey p).1 a ≠ (orbitKey p).2 a) :
    (orbitKey p).1 a = true ∧ (orbitKey p).2 a = false := by
  simp only [orbitKey] at hne ⊢
  revert hne; cases p.1 a <;> cases p.2 a <;> simp





















def ReimerSubcubeReduction : Prop := ReimerCardFormAll → rc3_PerKeyAll




theorem rc3_core_residue_of_subcubeReduction
    (hred : ReimerSubcubeReduction) (hcard : ReimerCardFormAll) : ReimerResidue :=
  rc3_core_residue_iff_perKeyAll.mpr (hred hcard)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in



theorem rc3_core_reimer_inequality_of_subcubeReduction
    (hred : ReimerSubcubeReduction) (hcard : ReimerCardFormAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  rc3_core_reimer_inequality_of_residue
    (rc3_core_residue_of_subcubeReduction hred hcard) hp A B






theorem rc3_core_reimerCardFormAll_of_residue (h : ReimerResidue) : ReimerCardFormAll :=
  rc3_core_reimerCardFormAll_of_slabCardAll h












theorem rc3_core_reimerCardForm_rbi : poc_ReimerCardForm rbi_A rbi_B :=
  poc_reimerCardForm_of_slabCard rbi_A rbi_B poc_slabCard_rbi


theorem rc3_core_reimerCardForm_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    poc_ReimerCardForm A B :=
  poc_reimerCardForm_of_slabCard A B (poc_slabCard_of_disjoint_support hA hB hST)


theorem rc3_core_reimerCardForm_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : poc_ReimerCardForm A B :=
  poc_reimerCardForm_of_slabCard A B (poc_slabCard_of_box_empty hbox)



theorem rc3_core_reimerCardForm_one (A B : Set (ConfigSpace (Fin 1))) : poc_ReimerCardForm A B :=
  poc_reimerCardForm_of_slabCard A B (rc_core_bridge_one A B)













set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in













theorem rc3_core_count_box_bridge :
    (ReimerResidue ↔ rc_core_CountBoxBridge)
      ∧ (ReimerResidue ↔ rc3_PerKeyAll)
      ∧ (ReimerResidue ↔ SlabInjectionAll)
      ∧ (ReimerResidue → ReimerWprobCore)
      ∧ (ReimerResidue → ReimerCardFormAll)
      ∧ (ReimerSubcubeReduction → ReimerCardFormAll → ReimerResidue) :=
  ⟨rc3_core_residue_iff_bridge, rc3_core_residue_iff_perKeyAll,
    rc3_core_residue_iff_slabInjectionAll, rc3_core_reimerWprobCore_of_residue,
    rc3_core_reimerCardFormAll_of_residue, rc3_core_residue_of_subcubeReduction⟩

end StatMech.Walls
