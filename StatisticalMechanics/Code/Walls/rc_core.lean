/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Code.Inequalities.ReimerButterflyProve3
import Code.Inequalities.ReimerButterflyClose
import Code.Walls.rc_dpairsfiberrecursion
import Code.Walls.rc_dpairsmodular
import Code.Walls.rmr_reflectinvolution
import Code.Walls.rmr_baseanddisjoint

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]













theorem rc_core_diagonal_empty (𝒜 ℬ : Finset (Finset α)) (i : α) :
    ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∈ p.1 ∧ i ∈ p.2) = ∅ :=
  rc_fourthFiber_empty 𝒜 ℬ i










theorem rc_core_fiber_repairing (𝒜 ℬ : Finset (Finset α)) (i : α) :
    dpairsCount 𝒜 ℬ
      = dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)
      + dpairsCount (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)
      + dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i) :=
  rc_dpairsCount_fiber_recursion 𝒜 ℬ i



















theorem rc_core_deficit_identity (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ
      = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
        - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
            (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) := by
  rw [dpairsCount_fiber_recursion 𝒜 ℬ i,
    dpairsCount_fiber_recursion (Down.compression i 𝒜) (Down.compression i ℬ) i,
    downComp_nonMemberSubfamily i 𝒜, downComp_memberSubfamily i 𝒜,
    downComp_nonMemberSubfamily i ℬ, downComp_memberSubfamily i ℬ]
  set am := 𝒜.memberSubfamily i
  set an := 𝒜.nonMemberSubfamily i
  set bm := ℬ.memberSubfamily i
  set bn := ℬ.nonMemberSubfamily i
  have e1 := dpairsCount_modular_left am an (bm ∪ bn)
  have e2 := dpairsCount_modular_left am an (bm ∩ bn)
  have e3 := dpairsCount_modular_right bm bn am
  have e4 := dpairsCount_modular_right bm bn an
  have e5 := dpairsCount_modular_right bm bn (am ∩ an)
  push_cast
  omega


















theorem rc_core_box_compress_preserve (𝒜 ℬ : Finset (Finset α)) (i : α) :
    dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) :=
  dpairsCount_downDown_mono 𝒜 ℬ i



theorem rc_core_deficit_nonneg (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (0 : ℤ) ≤ (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
        - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
            (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) := by
  rw [← rc_core_deficit_identity 𝒜 ℬ i, sub_nonneg]
  exact_mod_cast rc_core_box_compress_preserve 𝒜 ℬ i










theorem rc_core_iter_box_compress_preserve (cs : List α) (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ) :=
  dpairsCount_iterDownComp_mono cs 𝒜 ℬ



theorem rc_core_iter_card (cs : List α) (𝒜 : Finset (Finset α)) :
    (iterDownComp cs 𝒜).card = 𝒜.card :=
  iterDownComp_card cs 𝒜












theorem rc_core_endpoint_favourable {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (hℬ : IsLowerSet (ℬ : Set (Finset α))) (i : α) :
    dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
      ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) :=
  dpairsCount_member_le_nonMember_of_isLowerSet h𝒜 hℬ i




theorem rc_core_exists_endpoint (𝒜 : Finset (Finset α)) :
    ∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)) :=
  exists_iterDownComp_isLowerSet 𝒜





















theorem rc_core_downUp_box_refuted :
    ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2),
      (boxDoubled (Down.compression i 𝒜)
        (UV.compression ({i} : Finset (Fin 2)) ∅ ℬ)).card
      < (boxDoubled 𝒜 ℬ).card :=
  rby_separate_compression_strictly_decreases







theorem rc_core_fixed_deficit_le_rbi : poc_ReimerCardForm rbi_A rbi_B :=
  poc_reimerCardForm_rbi









open Classical in



theorem rc_core_reimerCardForm_iff_deficit_le [Fintype α] (A B : Set (ConfigSpace α)) :
    StatMech.poc_ReimerCardForm A B ↔
      #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤
        #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) :=
  rmr_reimerCardForm_iff_inter A B




















def rc_core_CountBoxBridge : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), poc_SlabCard A B



theorem rc_core_countBoxBridge_iff : rc_core_CountBoxBridge ↔ StatMech.poc_SlabCardAll := Iff.rfl




theorem rc_core_reimer_of_bridge (h : rc_core_CountBoxBridge) : ReimerWprobCore :=
  reimer_wprob_core_of_slabCard h

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in



theorem rc_core_reimer_inequality_of_bridge (h : rc_core_CountBoxBridge) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_slabCard h hp A B









variable {β : Type*} [Fintype β] [DecidableEq β]





theorem rc_core_bridge_of_disjoint_support {A B : Set (ConfigSpace β)} {S T : Finset β}
    (hA : StatMech.DependsOn A (↑S)) (hB : StatMech.DependsOn B (↑T)) (hST : Disjoint S T) :
    poc_SlabCard A B :=
  rmr_slabCard_of_disjoint_support hA hB hST




theorem rc_core_bridge_one (A B : Set (ConfigSpace (Fin 1))) : poc_SlabCard A B :=
  rmr_slabCard_one A B



theorem rc_core_bridge_of_box_empty {A B : Set (ConfigSpace β)}
    (hbox : disjointOccurrence A B = ∅) : poc_SlabCard A B :=
  poc_slabCard_of_box_empty hbox

end StatMech.Walls
