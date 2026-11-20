/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusCycleTopology









open scoped BigOperators

namespace StatMech.FrontierA

noncomputable def triangularIntReduce (L : Nat) : Int × Int -> ZMod L × ZMod L :=
  fun p => ((p.1 : ZMod L), (p.2 : ZMod L))

@[simp] theorem triangularIntReduce_zero (L : Nat) :
    triangularIntReduce L 0 = 0 := by
  apply Prod.ext <;> simp [triangularIntReduce]

@[simp] theorem triangularIntReduce_add (L : Nat) (p q : Int × Int) :
    triangularIntReduce L (p + q) =
      triangularIntReduce L p + triangularIntReduce L q := by
  apply Prod.ext <;> simp [triangularIntReduce]

theorem triangularIntReduce_sum
    {alpha : Type*} (L : Nat) (s : Finset alpha) (f : alpha -> Int × Int) :
    triangularIntReduce L (∑ i ∈ s, f i) =
      ∑ i ∈ s, triangularIntReduce L (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        triangularIntReduce_add, ih]

theorem triangularIntReduce_step
    (L : Nat) (a : Fin 6) :
    triangularIntReduce L (triangularIntStep a) =
      -triangularTorusDirectionStep L a := by
  fin_cases a <;>
    simp [triangularIntReduce, triangularIntStep,
      triangularTorusDirectionStep]

noncomputable def triangularTorusCycleNativeDart
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root)
    (k : Fin p.darts.length) : triangularTorusDart L :=
  (triangularTorusDartEquiv L).symm (kwGraphCycleDartLoop p k)

@[simp] theorem triangularTorusCycleNativeDart_equiv
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root)
    (k : Fin p.darts.length) :
    triangularTorusDartEquiv L (triangularTorusCycleNativeDart L p k) =
      kwGraphCycleDartLoop p k := by
  simp [triangularTorusCycleNativeDart]

theorem triangularTorusCycleNativeDart_fst
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root)
    (k : Fin p.darts.length) :
    (triangularTorusCycleNativeDart L p k).1 =
      (kwGraphCycleDartLoop p k).fst := by
  have h := congrArg (fun d : (triangularTorusGraph L).Dart => d.fst)
    (triangularTorusCycleNativeDart_equiv L p k)
  simpa [triangularTorusDartEquiv_apply,
    triangularTorusDartToGraphDart] using h

theorem triangularTorusCycleNativeDart_snd
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root)
    (k : Fin p.darts.length) :
    (triangularTorusCycleNativeDart L p k).2 =
      triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k) := by
  rfl

theorem triangularTorusCycleNativeSite_succ
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall k,
      (triangularTorusCycleNativeDart L p (k + 1)).1 =
        (triangularTorusCycleNativeDart L p k).1 +
          triangularIntReduce L (triangularIntStep
            (triangularTorusCycleNativeDart L p k).2) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k
  let d := triangularTorusCycleNativeDart L p k
  let e := triangularTorusCycleNativeDart L p (k + 1)
  have hadj := kwGraphCycleDartLoop_valid p hp k
  change (kwGraphCycleDartLoop p k).snd =
    (kwGraphCycleDartLoop p (k + 1)).fst at hadj
  rw [<- triangularTorusCycleNativeDart_equiv L p k,
    <- triangularTorusCycleNativeDart_equiv L p (k + 1)] at hadj
  have hnative : d.1 - triangularTorusDirectionStep L d.2 = e.1 := by
    simpa only [d, e, triangularTorusDartEquiv_apply,
      triangularTorusDartToGraphDart] using hadj
  rw [triangularIntReduce_step]
  exact hnative.symm.trans (sub_eq_add_neg _ _)

theorem triangularIntPos_succ_cast
    {m : Nat} (direction : Fin (m + 1) -> Fin 6) (i : Fin m) :
    triangularIntPos direction i.succ =
      triangularIntPos direction i.castSucc +
        triangularIntStep (direction i.castSucc) := by
  have hfilter :
      (Finset.univ.filter (fun j : Fin (m + 1) => j < i.succ)) =
        insert i.castSucc
          (Finset.univ.filter (fun j : Fin (m + 1) => j < i.castSucc)) := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hj
      rw [Fin.lt_def] at hj
      simp only [Fin.val_succ] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact Or.inr (Fin.lt_def.mpr hlt)
      · exact Or.inl (Fin.ext heq)
    · rintro (rfl | hj)
      · exact Fin.castSucc_lt_succ
      · exact hj.trans Fin.castSucc_lt_succ
  have hnotmem : i.castSucc ∉
      (Finset.univ.filter (fun j : Fin (m + 1) => j < i.castSucc)) := by
    simp
  rw [triangularIntPos, triangularIntPos, hfilter,
    Finset.sum_insert hnotmem, add_comm]

theorem triangularCyclicSite_eq_reduce_pos
    {n : Nat} [NeZero n]
    (site : Fin n -> ZMod L × ZMod L) (direction : Fin n -> Fin 6)
    (hsucc : forall k, site (k + 1) = site k +
      triangularIntReduce L (triangularIntStep (direction k))) (k : Fin n) :
    site k = triangularIntReduce L (triangularIntPos direction k) + site 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  refine Fin.induction ?_ (fun i ih => ?_) k
  · simp [triangularIntPos_zero]
  · have hs := hsucc i.castSucc
    have hisucc : (i.castSucc + 1 : Fin (m + 1)) = i.succ := by
      apply Fin.ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : i.val + 1 < m + 1)]
    rw [hisucc] at hs
    rw [hs, ih, triangularIntPos_succ_cast direction i,
      triangularIntReduce_add]
    abel

theorem triangularTorusCycleNativeSite_eq_reduce_pos
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall k,
      (triangularTorusCycleNativeDart L p k).1 =
        triangularIntReduce L (triangularIntPos
          (fun j => (triangularTorusCycleNativeDart L p j).2) k) +
          (triangularTorusCycleNativeDart L p 0).1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k
  exact triangularCyclicSite_eq_reduce_pos
    (fun j => (triangularTorusCycleNativeDart L p j).1)
    (fun j => (triangularTorusCycleNativeDart L p j).2)
    (triangularTorusCycleNativeSite_succ L p hp) k

theorem triangularTorusCycle_totalStep_reduce_eq_zero
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    triangularIntReduce L (∑ k, triangularIntStep
      (triangularTorusCycleNativeDart L p k).2) = 0 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let site : Fin p.darts.length -> ZMod L × ZMod L :=
    fun k => (triangularTorusCycleNativeDart L p k).1
  let direction : Fin p.darts.length -> Fin 6 :=
    fun k => (triangularTorusCycleNativeDart L p k).2
  have hshift : (∑ k, site (k + 1)) = ∑ k, site k :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin p.darts.length)) site
  have hrec : (∑ k, site (k + 1)) =
      ∑ k, (site k + triangularIntReduce L
        (triangularIntStep (direction k))) := by
    apply Finset.sum_congr rfl
    intro k _
    exact triangularTorusCycleNativeSite_succ L p hp k
  rw [hshift, Finset.sum_add_distrib] at hrec
  have hzero : (∑ k, triangularIntReduce L
      (triangularIntStep (direction k))) = 0 := by
    apply add_left_cancel (a := ∑ k, site k)
    simpa using hrec.symm
  rw [triangularIntReduce_sum]
  exact hzero



theorem exists_triangularTorusCycle_winding
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    exists mx my : Int,
      (∑ k, triangularIntStep
        (triangularTorusCycleNativeDart L p k).2) =
          ((L : Int) * mx, (L : Int) * my) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let displacement : Int × Int := ∑ k, triangularIntStep
    (triangularTorusCycleNativeDart L p k).2
  have hreduce : triangularIntReduce L displacement = 0 :=
    triangularTorusCycle_totalStep_reduce_eq_zero L p hp
  have hx : ((displacement.1 : Int) : ZMod L) = 0 := by
    simpa [triangularIntReduce] using congrArg Prod.fst hreduce
  have hy : ((displacement.2 : Int) : ZMod L) = 0 := by
    simpa [triangularIntReduce] using congrArg Prod.snd hreduce
  obtain ⟨mx, hmx⟩ :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd displacement.1 L).mp hx
  obtain ⟨my, hmy⟩ :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd displacement.2 L).mp hy
  refine ⟨mx, my, ?_⟩
  apply Prod.ext
  · exact hmx
  · exact hmy

theorem triangularIntStep_fst_eq_movementExponent (a : Fin 6) :
    (triangularIntStep a).1 =
      StatMech.Onsager.ons_dirExponentX
        (triangularTorusXMovementDirection a) := by
  fin_cases a <;>
    simp [triangularIntStep, triangularTorusXMovementDirection,
      StatMech.Onsager.ons_dirExponentX]

theorem triangularIntStep_snd_eq_movementExponent (a : Fin 6) :
    (triangularIntStep a).2 =
      StatMech.Onsager.ons_dirExponentY
        (triangularTorusYMovementDirection a) := by
  fin_cases a <;>
    simp [triangularIntStep, triangularTorusYMovementDirection,
      StatMech.Onsager.ons_dirExponentY]

theorem sum_triangularCycleStep_fst_eq_wrap
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, (triangularIntStep
      (triangularTorusCycleNativeDart L p k).2).1) =
      (L : Int) * ∑ k, StatMech.Onsager.ons_xWrapSign
        (triangularTorusXMovementDart L
          (triangularTorusCycleNativeDart L p k)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let d : Fin p.darts.length -> triangularTorusDart L :=
    fun k => triangularTorusCycleNativeDart L p k
  have htarget (k : Fin p.darts.length) :
      (StatMech.Onsager.ons_dirStep L
        (triangularTorusXMovementDirection (d k).2) (d k).1).1 =
          (d (k + 1)).1.1 := by
    rw [triangularTorusXMovement_target]
    have hs := triangularTorusCycleNativeSite_succ L p hp k
    rw [triangularIntReduce_step] at hs
    simpa [d, sub_eq_add_neg] using congrArg Prod.fst hs.symm
  have htargetSum :
      (∑ k, (((StatMech.Onsager.ons_dirStep L
        (triangularTorusXMovementDirection (d k).2) (d k).1).1.val : Nat) : Int)) =
        ∑ k, ((((d k).1.1.val : Nat) : Int)) := by
    calc
      _ = ∑ k, ((((d (k + 1)).1.1.val : Nat) : Int)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [htarget k]
      _ = _ := by
        simpa [add_comm] using
          (Equiv.sum_comp (Equiv.addRight (1 : Fin p.darts.length))
            (fun k => ((((d k).1.1.val : Nat) : Int))))
  calc
    (∑ k, (triangularIntStep (d k).2).1) =
        ∑ k, StatMech.Onsager.ons_dirExponentX
          (triangularTorusXMovementDirection (d k).2) := by
      apply Finset.sum_congr rfl
      intro k _
      exact triangularIntStep_fst_eq_movementExponent (d k).2
    _ = ∑ k, (((((StatMech.Onsager.ons_dirStep L
          (triangularTorusXMovementDirection (d k).2) (d k).1).1.val : Nat) : Int) -
        (((d k).1.1.val : Nat) : Int)) +
          (L : Int) * StatMech.Onsager.ons_xWrapSign
            (triangularTorusXMovementDart L (d k))) := by
      apply Finset.sum_congr rfl
      intro k _
      exact StatMech.Onsager.ons_dirExponentX_eq_val_diff_add_wrap
        (triangularTorusXMovementDart L (d k))
    _ = (L : Int) * ∑ k, StatMech.Onsager.ons_xWrapSign
        (triangularTorusXMovementDart L (d k)) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, htargetSum,
        sub_self, zero_add, Finset.mul_sum]

theorem sum_triangularCycleStep_snd_eq_wrap
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, (triangularIntStep
      (triangularTorusCycleNativeDart L p k).2).2) =
      (L : Int) * ∑ k, StatMech.Onsager.ons_yWrapSign
        (triangularTorusYMovementDart L
          (triangularTorusCycleNativeDart L p k)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let d : Fin p.darts.length -> triangularTorusDart L :=
    fun k => triangularTorusCycleNativeDart L p k
  have htarget (k : Fin p.darts.length) :
      (StatMech.Onsager.ons_dirStep L
        (triangularTorusYMovementDirection (d k).2) (d k).1).2 =
          (d (k + 1)).1.2 := by
    rw [triangularTorusYMovement_target]
    have hs := triangularTorusCycleNativeSite_succ L p hp k
    rw [triangularIntReduce_step] at hs
    simpa [d, sub_eq_add_neg] using congrArg Prod.snd hs.symm
  have htargetSum :
      (∑ k, (((StatMech.Onsager.ons_dirStep L
        (triangularTorusYMovementDirection (d k).2) (d k).1).2.val : Nat) : Int)) =
        ∑ k, ((((d k).1.2.val : Nat) : Int)) := by
    calc
      _ = ∑ k, ((((d (k + 1)).1.2.val : Nat) : Int)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [htarget k]
      _ = _ := by
        simpa [add_comm] using
          (Equiv.sum_comp (Equiv.addRight (1 : Fin p.darts.length))
            (fun k => ((((d k).1.2.val : Nat) : Int))))
  calc
    (∑ k, (triangularIntStep (d k).2).2) =
        ∑ k, StatMech.Onsager.ons_dirExponentY
          (triangularTorusYMovementDirection (d k).2) := by
      apply Finset.sum_congr rfl
      intro k _
      exact triangularIntStep_snd_eq_movementExponent (d k).2
    _ = ∑ k, (((((StatMech.Onsager.ons_dirStep L
          (triangularTorusYMovementDirection (d k).2) (d k).1).2.val : Nat) : Int) -
        (((d k).1.2.val : Nat) : Int)) +
          (L : Int) * StatMech.Onsager.ons_yWrapSign
            (triangularTorusYMovementDart L (d k))) := by
      apply Finset.sum_congr rfl
      intro k _
      exact StatMech.Onsager.ons_dirExponentY_eq_val_diff_add_wrap
        (triangularTorusYMovementDart L (d k))
    _ = (L : Int) * ∑ k, StatMech.Onsager.ons_yWrapSign
        (triangularTorusYMovementDart L (d k)) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, htargetSum,
        sub_self, zero_add, Finset.mul_sum]

theorem triangularTorusCycle_edges_toFinset_eq_image
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) :
    p.edges.toFinset = Finset.univ.image
      (fun k : Fin p.darts.length => (kwGraphCycleDartLoop p k).edge) := by
  ext edge
  simp only [List.mem_toFinset, SimpleGraph.Walk.edges, List.mem_map,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨dart, hdart, rfl⟩
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hdart
    exact ⟨k, congrArg SimpleGraph.Dart.edge hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨kwGraphCycleDartLoop p k, ?_, hk⟩
    exact List.mem_iff_get.mpr ⟨k, rfl⟩

theorem triangularTorusCycle_edge_injective
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    Function.Injective
      (fun k : Fin p.darts.length => (kwGraphCycleDartLoop p k).edge) := by
  apply List.nodup_ofFn.mp
  rw [List.ofFn_comp', kwGraphCycleDartLoop_ofFn]
  simpa [SimpleGraph.Walk.edges] using hp.edges_nodup

theorem triangularTorusCycle_xSeam_card
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    (p.edges.toFinset.filter (triangularTorusXSeamEdge L)).card =
      (Finset.univ.filter (fun k : Fin p.darts.length =>
        StatMech.Onsager.ons_xWrap (triangularTorusXMovementDart L
          (triangularTorusCycleNativeDart L p k)))).card := by
  let edgeAt := fun k : Fin p.darts.length =>
    (kwGraphCycleDartLoop p k).edge
  have himage :
      (Finset.univ.image edgeAt).filter (triangularTorusXSeamEdge L) =
        (Finset.univ.filter (fun k =>
          triangularTorusXSeamEdge L (edgeAt k))).image edgeAt := by
    ext edge
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
      true_and]
    aesop
  rw [triangularTorusCycle_edges_toFinset_eq_image L p, himage,
    Finset.card_image_iff.mpr (fun _ _ _ _ h =>
      triangularTorusCycle_edge_injective L p hp h)]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro k _
  rw [show edgeAt k =
      (triangularTorusDartEquiv L
        (triangularTorusCycleNativeDart L p k)).edge by
    rw [triangularTorusCycleNativeDart_equiv]]
  exact triangularTorusXSeamEdge_dart_iff L _

theorem triangularTorusCycle_ySeam_card
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    (p.edges.toFinset.filter (triangularTorusYSeamEdge L)).card =
      (Finset.univ.filter (fun k : Fin p.darts.length =>
        StatMech.Onsager.ons_yWrap (triangularTorusYMovementDart L
          (triangularTorusCycleNativeDart L p k)))).card := by
  let edgeAt := fun k : Fin p.darts.length =>
    (kwGraphCycleDartLoop p k).edge
  have himage :
      (Finset.univ.image edgeAt).filter (triangularTorusYSeamEdge L) =
        (Finset.univ.filter (fun k =>
          triangularTorusYSeamEdge L (edgeAt k))).image edgeAt := by
    ext edge
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
      true_and]
    aesop
  rw [triangularTorusCycle_edges_toFinset_eq_image L p, himage,
    Finset.card_image_iff.mpr (fun _ _ _ _ h =>
      triangularTorusCycle_edge_injective L p hp h)]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro k _
  rw [show edgeAt k =
      (triangularTorusDartEquiv L
        (triangularTorusCycleNativeDart L p k)).edge by
    rw [triangularTorusCycleNativeDart_equiv]]
  exact triangularTorusYSeamEdge_dart_iff L _

theorem triangularTorusCycle_evenHomology_eq_windingParity
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (mx my : Int)
    (hdisplacement : ∑ k, triangularIntStep
      (triangularTorusCycleNativeDart L p k).2 =
        ((L : Int) * mx, (L : Int) * my)) :
    triangularTorusEvenHomology L p.edges.toFinset =
      (StatMech.Onsager.ons_intParity mx,
        StatMech.Onsager.ons_intParity my) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  have hL : (L : Int) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans (by decide : 0 < 2)
      (Fact.out : 2 < L)))
  have hmx : mx = ∑ k, StatMech.Onsager.ons_xWrapSign
      (triangularTorusXMovementDart L
        (triangularTorusCycleNativeDart L p k)) := by
    apply mul_left_cancel₀ hL
    have hcoord := congrArg Prod.fst hdisplacement
    simp only [Prod.fst_sum] at hcoord
    exact hcoord.symm.trans (sum_triangularCycleStep_fst_eq_wrap L p hp)
  have hmy : my = ∑ k, StatMech.Onsager.ons_yWrapSign
      (triangularTorusYMovementDart L
        (triangularTorusCycleNativeDart L p k)) := by
    apply mul_left_cancel₀ hL
    have hcoord := congrArg Prod.snd hdisplacement
    simp only [Prod.snd_sum] at hcoord
    exact hcoord.symm.trans (sum_triangularCycleStep_snd_eq_wrap L p hp)
  apply Prod.ext
  · change
      ⟨(p.edges.toFinset.filter (triangularTorusXSeamEdge L)).card % 2,
        Nat.mod_lt _ (by decide)⟩ = StatMech.Onsager.ons_intParity mx
    rw [triangularTorusCycle_xSeam_card L p hp, hmx]
    exact (StatMech.Onsager.ons_intParity_sum_xWrapSign
      (fun k => triangularTorusXMovementDart L
        (triangularTorusCycleNativeDart L p k))).symm
  · change
      ⟨(p.edges.toFinset.filter (triangularTorusYSeamEdge L)).card % 2,
        Nat.mod_lt _ (by decide)⟩ = StatMech.Onsager.ons_intParity my
    rw [triangularTorusCycle_ySeam_card L p hp, hmy]
    exact (StatMech.Onsager.ons_intParity_sum_yWrapSign
      (fun k => triangularTorusYMovementDart L
        (triangularTorusCycleNativeDart L p k))).symm

theorem triangularTorusCycle_surfaceHomology_eq_windingParity
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (mx my : Int)
    (hdisplacement : ∑ k, triangularIntStep
      (triangularTorusCycleNativeDart L p k).2 =
        ((L : Int) * mx, (L : Int) * my)) :
    surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L)
        p.edges.toFinset =
      (fun _ => StatMech.Onsager.ons_intParity mx,
        fun _ => StatMech.Onsager.ons_intParity my) := by
  rw [triangularTorus_surfaceSubgraphHomology_eq,
    triangularTorusCycle_evenHomology_eq_windingParity L p hp mx my
      hdisplacement]

theorem triangularTorusCycleNativeSite_injective
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    Function.Injective (fun k => (triangularTorusCycleNativeDart L p k).1) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro i j hij
  apply Fin.ext
  apply hp.getVert_injOn'
  · simp only [Set.mem_setOf_eq]
    rw [<- SimpleGraph.Walk.length_darts]
    exact Nat.le_sub_one_of_lt i.isLt
  · simp only [Set.mem_setOf_eq]
    rw [<- SimpleGraph.Walk.length_darts]
    exact Nat.le_sub_one_of_lt j.isLt
  · have hi : (kwGraphCycleDartLoop p i).fst = p.getVert i.val :=
      congrArg (fun dart : (triangularTorusGraph L).Dart => dart.fst)
        (SimpleGraph.Walk.darts_getElem_eq_getVert i.val i.isLt)
    have hj : (kwGraphCycleDartLoop p j).fst = p.getVert j.val :=
      congrArg (fun dart : (triangularTorusGraph L).Dart => dart.fst)
        (SimpleGraph.Walk.darts_getElem_eq_getVert j.val j.isLt)
    exact hi.symm.trans ((triangularTorusCycleNativeDart_fst L p i).symm.trans
      (hij.trans ((triangularTorusCycleNativeDart_fst L p j).trans hj)))

theorem triangularTorusCycleLiftPos_injective
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    Function.Injective (triangularIntPos
      (fun k => (triangularTorusCycleNativeDart L p k).2)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro i j hij
  have hi := triangularTorusCycleNativeSite_eq_reduce_pos L p hp i
  have hj := triangularTorusCycleNativeSite_eq_reduce_pos L p hp j
  apply (triangularTorusCycleNativeSite_injective L p hp)
  change (triangularTorusCycleNativeDart L p i).1 =
    (triangularTorusCycleNativeDart L p j).1
  rw [hi, hj, hij]

def triangularIntPeriodicPos
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (z : Int × Fin n) : Int × Int :=
  let displacement := ∑ k, triangularIntStep (direction k)
  (z.1 * displacement.1 + (triangularIntPos direction z.2).1,
    z.1 * displacement.2 + (triangularIntPos direction z.2).2)

theorem triangularIntPeriodicPos_reduce
    {n : Nat} [NeZero n] (L : Nat) (direction : Fin n -> Fin 6)
    (mx my : Int)
    (hdisplacement : ∑ k, triangularIntStep (direction k) =
      ((L : Int) * mx, (L : Int) * my)) (z : Int × Fin n) :
    triangularIntReduce L (triangularIntPeriodicPos direction z) =
      triangularIntReduce L (triangularIntPos direction z.2) := by
  rcases z with ⟨r, i⟩
  apply Prod.ext <;>
    simp [triangularIntPeriodicPos, triangularIntReduce,
      hdisplacement]

theorem triangularTorusCyclePeriodicPos_injective
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (mx my : Int)
    (hdisplacement : ∑ k, triangularIntStep
      (triangularTorusCycleNativeDart L p k).2 =
        ((L : Int) * mx, (L : Int) * my))
    (hne : mx ≠ 0 ∨ my ≠ 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    Function.Injective (triangularIntPeriodicPos
      (fun k => (triangularTorusCycleNativeDart L p k).2)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro z w hzw
  let direction : Fin p.darts.length -> Fin 6 :=
    fun k => (triangularTorusCycleNativeDart L p k).2
  have hred := congrArg (triangularIntReduce L) hzw
  rw [triangularIntPeriodicPos_reduce L direction mx my
      hdisplacement z,
    triangularIntPeriodicPos_reduce L direction mx my
      hdisplacement w] at hred
  have hsite : (triangularTorusCycleNativeDart L p z.2).1 =
      (triangularTorusCycleNativeDart L p w.2).1 := by
    rw [triangularTorusCycleNativeSite_eq_reduce_pos L p hp z.2,
      triangularTorusCycleNativeSite_eq_reduce_pos L p hp w.2,
      hred]
  have hindex : z.2 = w.2 :=
    triangularTorusCycleNativeSite_injective L p hp hsite
  rcases z with ⟨r, i⟩
  rcases w with ⟨s, j⟩
  dsimp only at hindex
  subst j
  apply Prod.ext
  · dsimp only
    have hL : (L : Int) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_trans (by decide : 0 < 2)
        (Fact.out : 2 < L)))
    rcases hne with hx | hy
    · have heq : r * ((L : Int) * mx) = s * ((L : Int) * mx) := by
        have h := congrArg Prod.fst hzw
        dsimp [triangularIntPeriodicPos, direction] at h
        rw [hdisplacement] at h
        simpa using add_right_cancel h
      exact mul_right_cancel₀ (mul_ne_zero hL hx) heq
    · have heq : r * ((L : Int) * my) = s * ((L : Int) * my) := by
        have h := congrArg Prod.snd hzw
        dsimp [triangularIntPeriodicPos, direction] at h
        rw [hdisplacement] at h
        simpa using add_right_cancel h
      exact mul_right_cancel₀ (mul_ne_zero hL hy) heq
  · rfl

theorem triangularTorusCycleLiftPos_injective_of_closed
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall (hclosed : ∑ k, triangularIntStep
        (triangularTorusCycleNativeDart L p k).2 = 0),
      Function.Injective (triangularIntPos
        (fun k => (triangularTorusCycleNativeDart L p k).2)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro _
  exact triangularTorusCycleLiftPos_injective L p hp



theorem exists_triangularTorus_cycleTurnSum_eq_eight_mul_odd_of_closed
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall (hclosed : ∑ k, triangularIntStep
        (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k)) = 0),
      exists m : Int,
        (∑ k, triangularTorusTurnExponent
          (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k))
          (triangularTorusGraphDartDirection L
            (kwGraphCycleDartLoop p (k + 1)))) = 8 * (2 * m + 1) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro hclosed
  apply exists_triangularTorusTurnExponent_sum_eq_eight_mul_odd_of_closed
  · exact triangularTorus_cycleDirection_nonbacktracking L p hp
  · exact hclosed
  · simpa [SimpleGraph.Walk.length_darts] using hp.three_le_length
  · have hnclosed : ∑ k, triangularIntStep
        (triangularTorusCycleNativeDart L p k).2 = 0 := by
      simpa only [triangularTorusCycleNativeDart_snd] using hclosed
    simpa only [triangularTorusCycleNativeDart_snd] using
      (triangularTorusCycleLiftPos_injective_of_closed L p hp hnclosed)



theorem triangularTorus_cyclePhaseProduct_eq_neg_one_of_closed
    (L : Nat) [Fact (2 < L)]
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall (hclosed : ∑ k, triangularIntStep
        (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k)) = 0),
      kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1)
        (kwGraphCycleDartLoop p) = -1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro hclosed
  obtain ⟨m, hm⟩ :=
    exists_triangularTorus_cycleTurnSum_eq_eight_mul_odd_of_closed L p hp hclosed
  exact triangularTorus_cyclePhaseProduct_eq_neg_one_of_odd_revolutions
    L rho hrho p hp m hm

end StatMech.FrontierA
