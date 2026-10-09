/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Internal.Execution
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Internal.Paths
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Internal.Simplify

/-!
# Floyd-Warshall stage invariant

Internal realization and optimality facts for the mathematical stage recurrence.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloydWarshall.Internal

lemma stageValue_realized {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (k : Nat) (hk : k ≤ n) (source target : Fin n) (distance : Int)
    (hdistance : stageValue weight k hk source target = (distance : WithTop Int)) :
    ∃ path, IsWeightedPath weight source target path ∧
      InternalVerticesBelow k path ∧ pathWeight weight path = (distance : WithTop Int) := by
  induction k generalizing source target distance with
  | zero =>
      simp only [stageValue, initialValue] at hdistance
      rcases min_choice (weight source target)
          (if source = target then 0 else ⊤) with hdirect | hdiagonal
      · have hweight : weight source target = (distance : WithTop Int) := by
          rw [← hdistance, hdirect]
        have hedge : weight source target ≠ ⊤ := by simp [hweight]
        refine ⟨[source, target], weightedPath_pair weight hedge, ?_, ?_⟩
        · simp [InternalVerticesBelow]
        · simp [pathWeight, hweight]
      · by_cases heq : source = target
        · subst target
          have hzeroCoe : ((0 : Int) : WithTop Int) = (distance : WithTop Int) := by
            rw [← hdistance]
            simpa using hdiagonal.symm
          have hzero : distance = 0 := by simpa using hzeroCoe.symm
          subst distance
          exact ⟨[source], weightedPath_singleton weight source,
            by simp [InternalVerticesBelow], by simp [pathWeight]⟩
        · simp [heq] at hdiagonal
          rw [hdiagonal] at hdistance
          simp [heq] at hdistance
  | succ k induction =>
      simp only [stageValue] at hdistance
      let pivot : Fin n := ⟨k, by omega⟩
      rcases min_choice (stageValue weight k (by omega) source target)
          (stageValue weight k (by omega) source pivot +
            stageValue weight k (by omega) pivot target) with hold | hthrough
      · have holdDistance : stageValue weight k (by omega) source target =
            (distance : WithTop Int) := by
          rw [← hdistance, hold]
        obtain ⟨path, hpath, hbound, hweight⟩ :=
          induction (by omega) source target distance holdDistance
        exact ⟨path, hpath, internalVerticesBelow_mono (Nat.le_succ k) hbound, hweight⟩
      · have hsum : stageValue weight k (by omega) source pivot +
            stageValue weight k (by omega) pivot target = (distance : WithTop Int) := by
          rw [← hdistance, hthrough]
        obtain ⟨leftDistance, rightDistance, hleftDistance, hrightDistance, hadd⟩ :=
          WithTop.add_eq_coe.mp hsum
        obtain ⟨left, hleft, hleftBound, hleftWeight⟩ :=
          induction (by omega) source pivot leftDistance hleftDistance.symm
        obtain ⟨right, hright, hrightBound, hrightWeight⟩ :=
          induction (by omega) pivot target rightDistance hrightDistance.symm
        refine ⟨left ++ right.tail, weightedPath_append_tail weight hleft hright,
          internalVerticesBelow_append_tail hleft hright
            (internalVerticesBelow_mono (Nat.le_succ k) hleftBound)
            (internalVerticesBelow_mono (Nat.le_succ k) hrightBound) (by simp [pivot]), ?_⟩
        rw [pathWeight_append_tail weight hleft hright, hleftWeight, hrightWeight,
          ← WithTop.coe_add, hadd]

lemma stageValue_le_nodup {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (k : Nat) (hk : k ≤ n) {source target : Fin n} {path : List (Fin n)}
    (hpath : IsWeightedPath weight source target path)
    (hnodup : path.Nodup) (hbound : InternalVerticesBelow k path) :
    stageValue weight k hk source target ≤ pathWeight weight path := by
  induction k generalizing source target path with
  | zero =>
      cases path with
      | nil => exact False.elim (hpath.ne_nil rfl)
      | cons first rest =>
          cases rest with
          | nil =>
              have hsource : first = source := by simpa using hpath.head_eq
              have htarget : first = target := by simpa using hpath.getLast_eq
              subst source
              subst target
              simp [stageValue, initialValue, pathWeight]
          | cons second rest =>
              cases rest with
              | nil =>
                  have hsource : first = source := by simpa using hpath.head_eq
                  have htarget : second = target := by simpa using hpath.getLast_eq
                  subst source
                  subst target
                  simp [stageValue, initialValue, pathWeight]
              | cons third rest =>
                  have himpossible := hbound second (by simp)
                  omega
  | succ k induction =>
      let pivot : Fin n := ⟨k, by omega⟩
      by_cases hpivot : pivot ∈ path.tail.dropLast
      · have hpivotPath : pivot ∈ path :=
          List.mem_of_mem_tail (List.mem_of_mem_dropLast hpivot)
        have hpivotNeSource := internalVertex_ne_source hpath hnodup hpivot
        have hpivotNeTarget := internalVertex_ne_target hpath hnodup hpivot
        have hpivotDropLast : pivot ∈ path.dropLast :=
          List.mem_dropLast_of_mem_of_ne_getLast hpivotPath (by
            simpa [hpath.getLast_eq] using hpivotNeTarget)
        let index := path.idxOf pivot
        have hindex : index < path.length := List.idxOf_lt_length_iff.mpr hpivotPath
        have hindexBeforeLast : index < path.length - 1 :=
          (List.mem_dropLast_iff_idxOf_lt hpivotPath).mp hpivotDropLast
        have hget : path[index] = pivot := List.getElem_idxOf (x := pivot) hindex
        have hindexPos : 0 < index := by
          by_contra hzero
          have hindexZero : index = 0 := Nat.eq_zero_of_not_pos hzero
          have hpivotAtZero : path[0] = pivot := by
            simpa [hindexZero] using hget
          have hpivotSource : pivot = source := by
            calc
              pivot = path[0] := hpivotAtZero.symm
              _ = source := hpath.getElem_zero
          exact hpivotNeSource hpivotSource
        let left := path.take (index + 1)
        let right := path.drop index
        have hleft : IsWeightedPath weight source pivot left := by
          change List.IsChainFromTo (fun a b => weight a b ≠ ⊤) left source pivot
          simpa [left, hget] using hpath.take hindex
        have hright : IsWeightedPath weight pivot target right := by
          change List.IsChainFromTo (fun a b => weight a b ≠ ⊤) right pivot target
          simpa [right, hget] using hpath.drop hindex
        have hleftNodup : left.Nodup := hnodup.sublist (List.take_sublist ..)
        have hrightNodup : right.Nodup := hnodup.sublist (List.drop_sublist ..)
        have hleftBound : InternalVerticesBelow k left := by
          intro vertex hvertex
          have hvertexLeft : vertex ∈ left :=
            List.mem_of_mem_tail (List.mem_of_mem_dropLast hvertex)
          have hvertexPath : vertex ∈ path :=
            List.Sublist.mem hvertexLeft (List.take_sublist ..)
          have hneSource := internalVertex_ne_source hleft hleftNodup hvertex
          have hnePivot := internalVertex_ne_target hleft hleftNodup hvertex
          have hneTarget : vertex ≠ target := by
            intro heq
            subst vertex
            have htargetMem : path.getLast hpath.ne_nil ∈ left := by
              simpa [hpath.getLast_eq] using hvertexLeft
            have heqLists := List.Nodup.eq_of_getLast_mem_of_prefix
              (List.take_prefix (index + 1) path) htargetMem hnodup
            have hlen := congrArg List.length heqLists
            simp [List.length_take] at hlen
            omega
          have horiginal := internal_mem_of_mem_of_ne_endpoints hpath hvertexPath
            hneSource hneTarget
          have hlt := hbound vertex horiginal
          have hneValue : vertex.val ≠ k := by
            intro heq
            exact hnePivot (Fin.ext heq)
          omega
        have hrightBound : InternalVerticesBelow k right := by
          intro vertex hvertex
          have hvertexRight : vertex ∈ right :=
            List.mem_of_mem_tail (List.mem_of_mem_dropLast hvertex)
          have hvertexPath : vertex ∈ path :=
            List.Sublist.mem hvertexRight (List.drop_sublist ..)
          have hnePivot := internalVertex_ne_source hright hrightNodup hvertex
          have hneTarget := internalVertex_ne_target hright hrightNodup hvertex
          have hneSource : vertex ≠ source := by
            intro heq
            subst vertex
            have hsourceMem : path.head hpath.ne_nil ∈ right := by
              simpa [hpath.head_eq] using hvertexRight
            have heqLists := List.Nodup.eq_of_head_mem_of_suffix
              (List.drop_suffix index path) hsourceMem hnodup
            have hlen := congrArg List.length heqLists
            simp [List.length_drop] at hlen
            omega
          have horiginal := internal_mem_of_mem_of_ne_endpoints hpath hvertexPath
            hneSource hneTarget
          have hlt := hbound vertex horiginal
          have hneValue : vertex.val ≠ k := by
            intro heq
            exact hnePivot (Fin.ext heq)
          omega
        have hleftLe := induction (by omega) hleft hleftNodup hleftBound
        have hrightLe := induction (by omega) hright hrightNodup hrightBound
        have hdecomp : left ++ right.tail = path := by
          dsimp only [left, right]
          simp [List.tail_drop, List.take_append_drop]
        calc
          stageValue weight (k + 1) hk source target ≤
              stageValue weight k (by omega) source pivot +
                stageValue weight k (by omega) pivot target := min_le_right _ _
          _ ≤ pathWeight weight left + pathWeight weight right :=
            add_le_add hleftLe hrightLe
          _ = pathWeight weight path := by
            rw [← pathWeight_append_tail weight hleft hright, hdecomp]
      · have hboundPrevious : InternalVerticesBelow k path := by
          intro vertex hvertex
          have hlt := hbound vertex hvertex
          have hne : vertex.val ≠ k := by
            intro heq
            have : vertex = pivot := Fin.ext heq
            subst vertex
            exact hpivot hvertex
          omega
        exact (min_le_left _ _).trans
          (induction (by omega) hpath hnodup hboundPrevious)

lemma stageValue_le_of_noNegativeCycle {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (hNoCycle : NoNegativeCycle weight)
    (k : Nat) (hk : k ≤ n) {source target : Fin n} {path : List (Fin n)}
    (hpath : IsWeightedPath weight source target path)
    (hbound : InternalVerticesBelow k path) :
    stageValue weight k hk source target ≤ pathWeight weight path := by
  obtain ⟨simple, hsimple, hnodup, hweight, hsubset⟩ :=
    exists_nodup_weight_le_of_noNegativeCycle weight hNoCycle hpath
  have hsimpleBound : InternalVerticesBelow k simple := by
    intro vertex hvertex
    have hvertexSimple : vertex ∈ simple :=
      List.mem_of_mem_tail (List.mem_of_mem_dropLast hvertex)
    have hneSource := internalVertex_ne_source hsimple hnodup hvertex
    have hneTarget := internalVertex_ne_target hsimple hnodup hvertex
    have hvertexPath := hsubset vertex hvertexSimple
    exact hbound vertex
      (internal_mem_of_mem_of_ne_endpoints hpath hvertexPath hneSource hneTarget)
  exact (stageValue_le_nodup weight k hk hsimple hnodup hsimpleBound).trans hweight

lemma stageValue_spec {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (hNoCycle : NoNegativeCycle weight) (k : Nat) (hk : k ≤ n)
    (source target : Fin n) :
    IsStageShortestPathWeight weight k source target
      (stageValue weight k hk source target) := by
  constructor
  · intro path hpath hbound
    exact stageValue_le_of_noNegativeCycle weight hNoCycle k hk hpath hbound
  · by_cases htop : stageValue weight k hk source target = ⊤
    · exact Or.inl htop
    · right
      obtain ⟨distance, hdistance⟩ := WithTop.ne_top_iff_exists.mp htop
      obtain ⟨path, hpath, hbound, hweight⟩ :=
        stageValue_realized weight k hk source target distance hdistance.symm
      exact ⟨path, hpath, hbound, hweight.trans hdistance⟩

end Cslib.Algorithms.Lean.FloydWarshall.Internal
