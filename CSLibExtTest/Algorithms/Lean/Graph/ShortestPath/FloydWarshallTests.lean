/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Basic

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloydWarshallTests

open FloydWarshall

#check pathWeight
#check IsWeightedPath
#check InternalVerticesBelow
#check IsStageShortestPathWeight
#check IsNegativeCycle
#check HasNegativeCycle
#check NoNegativeCycle
#check Cost
#check Cost.total
#check floydWarshall
#check hasNegativeDiagonal
#check floydWarshall_distance_spec
#check floydWarshall_distance_realized
#check floydWarshall_distance_minimal
#check floydWarshall_distance_eq_top_iff
#check hasNegativeDiagonal_eq_true_iff
#check floydWarshall_hasNegativeDiagonal_sound
#check floydWarshall_hasNegativeDiagonal_eq_false
#check floydWarshall_initializations
#check floydWarshall_transitions
#check floydWarshall_time

private def emptyWeight (i : Fin 0) (_j : Fin 0) : WithTop Int := nomatch i

example : (floydWarshall emptyWeight).time.initializations = 0 := by decide
example : (floydWarshall emptyWeight).time.transitions = 0 := by decide
example : (floydWarshall emptyWeight).time.total = 0 := by decide
example : hasNegativeDiagonal (floydWarshall emptyWeight).ret = false := by decide

private def singletonWeight (weight : WithTop Int) : Fin 1 → Fin 1 → WithTop Int :=
  fun _ _ ↦ weight

example : (floydWarshall (singletonWeight ⊤)).ret 0 0 = 0 := by decide
example : (floydWarshall (singletonWeight 7)).ret 0 0 = 0 := by decide
example : (floydWarshall (singletonWeight 0)).ret 0 0 = 0 := by decide
example : (floydWarshall (singletonWeight (-3))).ret 0 0 = -6 := by decide
example : (floydWarshall (singletonWeight ⊤)).time.initializations = 1 := by decide
example : (floydWarshall (singletonWeight ⊤)).time.transitions = 1 := by decide
example : (floydWarshall (singletonWeight ⊤)).time.total = 2 := by decide
example : hasNegativeDiagonal (floydWarshall (singletonWeight 7)).ret = false := by decide
example : hasNegativeDiagonal (floydWarshall (singletonWeight 0)).ret = false := by decide
example : hasNegativeDiagonal (floydWarshall (singletonWeight (-3))).ret = true := by decide
example : IsNegativeCycle (singletonWeight (-3)) [0, 0] := by
  refine ⟨0, ?_, by decide, by decide, ?_⟩
  · refine ⟨?_, by simp, rfl, rfl⟩
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    change (((-3 : Int) : WithTop Int) ≠ ⊤)
    exact WithTop.coe_ne_top
  · decide

private def acyclicWeight (i j : Fin 3) : WithTop Int :=
  match i.val, j.val with
  | 0, 1 => 4
  | 0, 2 => 11
  | 1, 2 => -2
  | _, _ => ⊤

example : (floydWarshall acyclicWeight).ret 0 0 = 0 := by decide
example : (floydWarshall acyclicWeight).ret 0 2 = 2 := by decide
example : (floydWarshall acyclicWeight).ret 1 2 = -2 := by decide
example : (floydWarshall acyclicWeight).ret 2 0 = ⊤ := by decide
example : hasNegativeDiagonal (floydWarshall acyclicWeight).ret = false := by decide
example : IsWeightedPath acyclicWeight 0 2 [0, 1, 2] := by
  refine ⟨?_, by simp, rfl, rfl⟩
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
  change (((4 : Int) : WithTop Int) ≠ ⊤) ∧ (((-2 : Int) : WithTop Int) ≠ ⊤)
  exact ⟨WithTop.coe_ne_top, WithTop.coe_ne_top⟩
example : pathWeight acyclicWeight [0, 1, 2] = 2 := by decide
example : ¬InternalVerticesBelow 1 ([0, 1, 2] : List (Fin 3)) := by
  simp [InternalVerticesBelow]
example : InternalVerticesBelow 2 ([0, 1, 2] : List (Fin 3)) := by
  simp [InternalVerticesBelow]

private def zeroCycleWeight (i j : Fin 2) : WithTop Int :=
  match i.val, j.val with
  | 0, 1 => 2
  | 1, 0 => -2
  | _, _ => ⊤

private def negativeCycleWeight (i j : Fin 2) : WithTop Int :=
  match i.val, j.val with
  | 0, 1 => 1
  | 1, 0 => -3
  | _, _ => ⊤

example : (floydWarshall zeroCycleWeight).ret 0 0 = 0 := by decide
example : (floydWarshall zeroCycleWeight).ret 1 1 = 0 := by decide
example : hasNegativeDiagonal (floydWarshall zeroCycleWeight).ret = false := by decide
example : hasNegativeDiagonal (floydWarshall negativeCycleWeight).ret = true := by decide
example : IsNegativeCycle negativeCycleWeight [0, 1, 0] := by
  refine ⟨0, ?_, by decide, by decide, ?_⟩
  · refine ⟨?_, by simp, rfl, rfl⟩
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    change (((1 : Int) : WithTop Int) ≠ ⊤) ∧ (((-3 : Int) : WithTop Int) ≠ ⊤)
    exact ⟨WithTop.coe_ne_top, WithTop.coe_ne_top⟩
  · decide
example : HasNegativeCycle negativeCycleWeight :=
  floydWarshall_hasNegativeDiagonal_sound negativeCycleWeight (by decide)
example : (floydWarshall negativeCycleWeight).time.initializations = 4 := by decide
example : (floydWarshall negativeCycleWeight).time.transitions = 8 := by decide
example : (floydWarshall negativeCycleWeight).time.total = 12 := by decide

private def disconnectedNegativeCycleWeight (i j : Fin 3) : WithTop Int :=
  match i.val, j.val with
  | 1, 2 => 1
  | 2, 1 => -4
  | _, _ => ⊤

example : hasNegativeDiagonal (floydWarshall disconnectedNegativeCycleWeight).ret = true := by
  decide
example : (floydWarshall disconnectedNegativeCycleWeight).ret 0 1 = ⊤ := by decide
example : (floydWarshall disconnectedNegativeCycleWeight).ret 1 0 = ⊤ := by decide

private def mixedNegativeSelfLoopWeight (i j : Fin 2) : WithTop Int :=
  match i.val, j.val with
  | 0, 0 => -1
  | 0, 1 => 4
  | 1, 0 => 2
  | _, _ => ⊤

example : (floydWarshall mixedNegativeSelfLoopWeight).ret 0 0 < 0 := by decide
example : hasNegativeDiagonal (floydWarshall mixedNegativeSelfLoopWeight).ret = true := by decide

private def positiveSelfLoopCheaperReturnWeight (i j : Fin 2) : WithTop Int :=
  match i.val, j.val with
  | 0, 0 => 9
  | 0, 1 => 2
  | 1, 0 => 3
  | _, _ => ⊤

example : pathWeight positiveSelfLoopCheaperReturnWeight [0, 1, 0] = 5 := by decide
example : (floydWarshall positiveSelfLoopCheaperReturnWeight).ret 0 0 = 0 := by decide
example : hasNegativeDiagonal (floydWarshall positiveSelfLoopCheaperReturnWeight).ret = false := by
  decide

private def positiveSelfLoopNegativeReturnWeight (i j : Fin 2) : WithTop Int :=
  match i.val, j.val with
  | 0, 0 => 9
  | 0, 1 => 2
  | 1, 0 => -5
  | _, _ => ⊤

example : pathWeight positiveSelfLoopNegativeReturnWeight [0, 1, 0] = -3 := by decide
example : (floydWarshall positiveSelfLoopNegativeReturnWeight).ret 0 0 < 0 := by decide
example : hasNegativeDiagonal (floydWarshall positiveSelfLoopNegativeReturnWeight).ret = true := by
  decide

private def equalRouteWeight (i j : Fin 3) : WithTop Int :=
  match i.val, j.val with
  | 0, 1 => 2
  | 1, 2 => 3
  | 0, 2 => 5
  | _, _ => ⊤

example : (floydWarshall equalRouteWeight).ret 0 2 = 5 := by decide

private def collapsedParallelWeight (i j : Fin 2) : WithTop Int :=
  if i = 0 ∧ j = 1 then -2 else ⊤

example : (floydWarshall collapsedParallelWeight).ret 0 1 = -2 := by decide

private def largeWeight (i j : Fin 3) : WithTop Int :=
  match i.val, j.val with
  | 0, 1 => ((1000000000000000000 : Int) : WithTop Int)
  | 1, 2 => ((-999999999999999999 : Int) : WithTop Int)
  | _, _ => ⊤

example : (floydWarshall largeWeight).ret 0 2 = 1 := by decide

private def clrsWeight (i j : Fin 5) : WithTop Int :=
  match i.val, j.val with
  | 0, 0 => 0
  | 0, 1 => 3
  | 0, 2 => 8
  | 0, 4 => -4
  | 1, 1 => 0
  | 1, 3 => 1
  | 1, 4 => 7
  | 2, 1 => 4
  | 2, 2 => 0
  | 3, 0 => 2
  | 3, 2 => -5
  | 3, 3 => 0
  | 4, 3 => 6
  | 4, 4 => 0
  | _, _ => ⊤

private def clrsExpected (i j : Fin 5) : WithTop Int :=
  match i.val, j.val with
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => -3
  | 0, 3 => 2
  | 0, 4 => -4
  | 1, 0 => 3
  | 1, 1 => 0
  | 1, 2 => -4
  | 1, 3 => 1
  | 1, 4 => -1
  | 2, 0 => 7
  | 2, 1 => 4
  | 2, 2 => 0
  | 2, 3 => 5
  | 2, 4 => 3
  | 3, 0 => 2
  | 3, 1 => -1
  | 3, 2 => -5
  | 3, 3 => 0
  | 3, 4 => -2
  | 4, 0 => 8
  | 4, 1 => 5
  | 4, 2 => 1
  | 4, 3 => 6
  | 4, 4 => 0
  | _, _ => ⊤

example :
    (List.finRange 5).all fun i ↦
      (List.finRange 5).all fun j ↦
        (floydWarshall clrsWeight).ret i j == clrsExpected i j := by
  decide

example : (floydWarshall clrsWeight).time.initializations = 25 := by decide
example : (floydWarshall clrsWeight).time.transitions = 125 := by decide
example : (floydWarshall clrsWeight).time.total = 150 := by decide
example : hasNegativeDiagonal (floydWarshall clrsWeight).ret = false := by decide

example : (floydWarshall equalRouteWeight).time.initializations = 9 := by decide
example : (floydWarshall equalRouteWeight).time.transitions = 27 := by decide
example : (floydWarshall equalRouteWeight).time.total = 36 := by decide

example {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (source target : Fin n) (hNoCycle : NoNegativeCycle weight) :
    IsStageShortestPathWeight weight n source target
      ((floydWarshall weight).ret source target) :=
  floydWarshall_distance_spec weight source target hNoCycle

example {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (source target : Fin n) (distance : Int)
    (hDistance : (floydWarshall weight).ret source target = distance) :
    ∃ path, IsWeightedPath weight source target path ∧
      pathWeight weight path = (distance : WithTop Int) :=
  floydWarshall_distance_realized weight source target distance hDistance

example {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (source target : Fin n) (path : List (Fin n))
    (hNoCycle : NoNegativeCycle weight) (hPath : IsWeightedPath weight source target path) :
    (floydWarshall weight).ret source target ≤ pathWeight weight path :=
  floydWarshall_distance_minimal weight source target path hNoCycle hPath

example {n : Nat} (weight : Fin n → Fin n → WithTop Int) (source target : Fin n) :
    (floydWarshall weight).ret source target = ⊤ ↔
      ¬∃ path, IsWeightedPath weight source target path :=
  floydWarshall_distance_eq_top_iff weight source target

example {n : Nat} (distance : Fin n → Fin n → WithTop Int) :
    hasNegativeDiagonal distance = true ↔ ∃ vertex, distance vertex vertex < 0 :=
  hasNegativeDiagonal_eq_true_iff distance

example {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (hNegative : hasNegativeDiagonal (floydWarshall weight).ret = true) :
    HasNegativeCycle weight :=
  floydWarshall_hasNegativeDiagonal_sound weight hNegative

example {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (hNoCycle : NoNegativeCycle weight) :
    hasNegativeDiagonal (floydWarshall weight).ret = false :=
  floydWarshall_hasNegativeDiagonal_eq_false weight hNoCycle

example {n : Nat} (weight : Fin n → Fin n → WithTop Int) :
    (floydWarshall weight).time.initializations = n ^ 2 :=
  floydWarshall_initializations weight

example {n : Nat} (weight : Fin n → Fin n → WithTop Int) :
    (floydWarshall weight).time.transitions = n ^ 3 :=
  floydWarshall_transitions weight

example {n : Nat} (weight : Fin n → Fin n → WithTop Int) :
    (floydWarshall weight).time.total = n ^ 2 + n ^ 3 :=
  floydWarshall_time weight

end Cslib.Algorithms.Lean.FloydWarshallTests
