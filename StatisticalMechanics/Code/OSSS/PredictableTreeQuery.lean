/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.OSSS.LindebergTree

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedFintypeInType false

namespace StatMech
namespace OSSS
namespace PredictableTreeQuery

open DecisionTree LindebergTree

variable {E : Type*} [Fintype E] [DecidableEq E]



def pathQuery : DecisionTree E → ConfigSpace E → ℕ → Option E
  | .leaf _, _, _ => none
  | .node e _ _, _, 0 => some e
  | .node e l r, ω, t + 1 => pathQuery (if ω e then l else r) ω t



theorem pathPrefix_eq_of_agree (T : DecisionTree E) (ω ω' : ConfigSpace E) (t : ℕ)
    (hagree : ∀ e ∈ pathPrefix T ω t, ω' e = ω e) :
    pathPrefix T ω' t = pathPrefix T ω t := by
  induction T generalizing t with
  | leaf b => simp
  | node e l r ihl ihr =>
      cases t with
      | zero => simp
      | succ t =>
          have heMem : e ∈ pathPrefix (.node e l r) ω (t + 1) := by
            rw [pathPrefix_node_succ]
            exact Finset.mem_insert_self _ _
          have he : ω' e = ω e := hagree e heMem
          rw [pathPrefix_node_succ, pathPrefix_node_succ, he]
          congr 1
          by_cases hωe : ω e
          · simp only [hωe, if_true]
            apply ihl
            intro i hi
            apply hagree i
            rw [pathPrefix_node_succ]
            simp only [hωe, if_true]
            exact Finset.mem_insert_of_mem hi
          · simp only [hωe, Bool.false_eq_true, if_false]
            apply ihr
            intro i hi
            apply hagree i
            rw [pathPrefix_node_succ]
            simp only [hωe, Bool.false_eq_true, if_false]
            exact Finset.mem_insert_of_mem hi



theorem pathQuery_eq_of_agree (T : DecisionTree E) (ω ω' : ConfigSpace E) (t : ℕ)
    (hagree : ∀ e ∈ pathPrefix T ω t, ω' e = ω e) :
    pathQuery T ω' t = pathQuery T ω t := by
  induction T generalizing t with
  | leaf b => simp [pathQuery]
  | node e l r ihl ihr =>
      cases t with
      | zero => rfl
      | succ t =>
          have heMem : e ∈ pathPrefix (.node e l r) ω (t + 1) := by
            rw [pathPrefix_node_succ]
            exact Finset.mem_insert_self _ _
          have he : ω' e = ω e := hagree e heMem
          simp only [pathQuery, he]
          by_cases hωe : ω e
          · simp only [hωe, if_true]
            apply ihl
            intro i hi
            apply hagree i
            rw [pathPrefix_node_succ]
            simp only [hωe, if_true]
            exact Finset.mem_insert_of_mem hi
          · simp only [hωe, Bool.false_eq_true, if_false]
            apply ihr
            intro i hi
            apply hagree i
            rw [pathPrefix_node_succ]
            simp only [hωe, Bool.false_eq_true, if_false]
            exact Finset.mem_insert_of_mem hi



theorem pathPrefix_succ_eq_insert_query (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) :
    pathPrefix T ω (t + 1) =
      match pathQuery T ω t with
      | none => pathPrefix T ω t
      | some e => insert e (pathPrefix T ω t) := by
  induction T generalizing t with
  | leaf b => simp [pathQuery]
  | node e l r ihl ihr =>
      cases t with
      | zero => simp [pathQuery, pathPrefix_node_succ]
      | succ t =>
          rw [pathPrefix_node_succ, pathPrefix_node_succ]
          by_cases hωe : ω e
          · simp only [hωe, if_true, pathQuery]
            rw [ihl]
            cases hq : pathQuery l ω t with
            | none => simp [hq]
            | some i => simp [hq, Finset.insert_comm]
          · simp only [hωe, Bool.false_eq_true, if_false, pathQuery]
            rw [ihr]
            cases hq : pathQuery r ω t with
            | none => simp [hq]
            | some i => simp [hq, Finset.insert_comm]



theorem freshAt_eq_one_iff (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) (e : E) :
    freshAt T ω t e = 1 ↔ pathQuery T ω t = some e ∧ e ∉ pathPrefix T ω t := by
  unfold freshAt
  rw [pathPrefix_succ_eq_insert_query]
  cases hq : pathQuery T ω t with
  | none => simp [hq]
  | some i =>
      change (if e ∈ insert i (pathPrefix T ω t) ∧ e ∉ pathPrefix T ω t then 1 else 0) = 1 ↔
        some i = some e ∧ e ∉ pathPrefix T ω t
      constructor
      · intro hone
        have hcond : e ∈ insert i (pathPrefix T ω t) ∧ e ∉ pathPrefix T ω t := by
          by_contra hnot
          rw [if_neg hnot] at hone
          norm_num at hone
        have hei : e = i := (Finset.mem_insert.mp hcond.1).resolve_right hcond.2
        exact ⟨by rw [hei], hcond.2⟩
      · rintro ⟨hie, he⟩
        have hie' : i = e := Option.some.inj hie
        subst i
        rw [if_pos ⟨Finset.mem_insert_self _ _, he⟩]

end PredictableTreeQuery
end OSSS
end StatMech
