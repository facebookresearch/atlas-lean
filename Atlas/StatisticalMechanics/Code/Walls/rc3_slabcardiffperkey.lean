/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Code.Walls.rc2_slabimgeqinter
import Code.Walls.rc2_slabcardallisbridge

open Finset
open scoped FinsetFamily NNReal

namespace StatMech.Walls

open StatMech

variable {α : Type*} [Fintype α] [DecidableEq α]








open Classical in






theorem rc3_slabBox_eq_inter (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    poc_slabBox A B k =
      Finset.univ.filter
        (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k) := by
  unfold poc_slabBox
  refine Finset.filter_congr (fun ω _ => ?_)
  simp only [rc2_mem_slab]








open Classical in





def rc3_PerKey (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) : Prop :=
  #(Finset.univ.filter
      (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k)) ≤
    #(Finset.univ.filter
      (fun ω : ConfigSpace α => ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k))

open Classical in





theorem rc3_slabCardKey_iff_perKey (A B : Set (ConfigSpace α))
    (k : ConfigSpace α × ConfigSpace α) :
    (#(poc_slabBox A B k) ≤ #(poc_slabImg A B k)) ↔ rc3_PerKey A B k := by
  rw [rc3_slabBox_eq_inter, rc2_slabImg_eq_inter]; rfl

open Classical in







theorem rc3_slabCard_iff_perKey (A B : Set (ConfigSpace α)) :
    poc_SlabCard A B ↔ ∀ k : ConfigSpace α × ConfigSpace α, rc3_PerKey A B k := by
  unfold poc_SlabCard
  exact forall_congr' (fun k => rc3_slabCardKey_iff_perKey A B k)







open Classical in




theorem rc3_perKey_top (A B : Set (ConfigSpace α)) :
    rc3_PerKey A B poc_topKey ↔
      #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤
        #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
  rw [← rc3_slabCardKey_iff_perKey, rc2_slabCard_top_iff_inter]








def rc3_PerKeyAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))) (k : ConfigSpace (Fin n) × ConfigSpace (Fin n)),
    rc3_PerKey A B k




theorem rc3_perKeyAll_iff_slabCardAll : rc3_PerKeyAll ↔ StatMech.poc_SlabCardAll := by
  unfold rc3_PerKeyAll StatMech.poc_SlabCardAll
  refine forall_congr' (fun n => forall_congr' (fun A => forall_congr' (fun B => ?_)))
  exact (rc3_slabCard_iff_perKey A B).symm





theorem rc3_reimerWprobCore_of_perKeyAll (h : rc3_PerKeyAll) : ReimerWprobCore :=
  rc2_reimerWprobCore_of_slabCardAll (rc3_perKeyAll_iff_slabCardAll.mp h)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in




theorem rc3_reimer_inequality_of_perKeyAll (h : rc3_PerKeyAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_slabCard (rc3_perKeyAll_iff_slabCardAll.mp h) hp A B








theorem rc3_perKey_rbi (k : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    rc3_PerKey rbi_A rbi_B k :=
  (rc3_slabCard_iff_perKey rbi_A rbi_B).mp poc_slabCard_rbi k


theorem rc3_perKey_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T)
    (k : ConfigSpace α × ConfigSpace α) :
    rc3_PerKey A B k :=
  (rc3_slabCard_iff_perKey A B).mp (poc_slabCard_of_disjoint_support hA hB hST) k


theorem rc3_perKey_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) (k : ConfigSpace α × ConfigSpace α) :
    rc3_PerKey A B k :=
  (rc3_slabCard_iff_perKey A B).mp (poc_slabCard_of_box_empty hbox) k

end StatMech.Walls
