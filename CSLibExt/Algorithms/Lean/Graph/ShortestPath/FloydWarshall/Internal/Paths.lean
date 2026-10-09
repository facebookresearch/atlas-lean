/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Basic
import Mathlib.Data.List.Infix

/-!
# Floyd-Warshall path lemmas

Internal list-path operations used by the stage invariant.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloydWarshall.Internal

lemma weightedPath_singleton {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (vertex : Fin n) : IsWeightedPath weight vertex vertex [vertex] :=
  List.isChainFromTo_singleton

lemma weightedPath_pair {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    {source target : Fin n} (hedge : weight source target ≠ ⊤) :
    IsWeightedPath weight source target [source, target] := by
  simpa [IsWeightedPath] using
    (List.isChainFromTo_pair_iff (r := fun left right => weight left right ≠ ⊤)
      (a := source) (b := target) (a' := source) (b' := target)).mpr
      ⟨hedge, rfl, rfl⟩

lemma pathWeight_cons_of_ne_nil {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (source : Fin n) {path : List (Fin n)} (hne : path ≠ []) :
    pathWeight weight (source :: path) =
      weight source (path.head hne) + pathWeight weight path := by
  cases path with
  | nil => contradiction
  | cons target rest => rfl

private lemma pathWeight_append_tail_of_join {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (left right : List (Fin n))
    (hleft : left ≠ []) (hright : right ≠ [])
    (hjoin : left.getLast hleft = right.head hright) :
    pathWeight weight (left ++ right.tail) =
      pathWeight weight left + pathWeight weight right := by
  induction left with
  | nil => contradiction
  | cons first rest induction =>
      cases rest with
      | nil =>
          have hhead : first = right.head hright := by simpa using hjoin
          have hrightEq : first :: right.tail = right := by
            rw [hhead, List.cons_head_tail hright]
          simp [pathWeight, hrightEq]
      | cons second rest =>
          have htailJoin : (second :: rest).getLast (by simp) = right.head hright := by
            simpa [List.getLast_cons] using hjoin
          have hinduction := induction (by simp) htailJoin
          simpa [pathWeight, add_assoc] using
            congrArg (fun value => weight first second + value) hinduction

lemma pathWeight_append_tail {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    {source pivot target : Fin n} {left right : List (Fin n)}
    (hleft : IsWeightedPath weight source pivot left)
    (hright : IsWeightedPath weight pivot target right) :
    pathWeight weight (left ++ right.tail) =
      pathWeight weight left + pathWeight weight right := by
  apply pathWeight_append_tail_of_join weight left right hleft.ne_nil hright.ne_nil
  rw [hleft.getLast_eq, hright.head_eq]

lemma weightedPath_append_tail {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    {source pivot target : Fin n} {left right : List (Fin n)}
    (hleft : IsWeightedPath weight source pivot left)
    (hright : IsWeightedPath weight pivot target right) :
    IsWeightedPath weight source target (left ++ right.tail) :=
  hleft.append_tail hright

private lemma pathWeight_ne_top_of_isChain {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (path : List (Fin n))
    (hchain : path.IsChain fun left right => weight left right ≠ ⊤) :
    pathWeight weight path ≠ ⊤ := by
  induction path with
  | nil => simp [pathWeight]
  | cons first rest induction =>
      cases rest with
      | nil => simp [pathWeight]
      | cons second rest =>
          obtain ⟨hedge, htail⟩ := List.isChain_cons_cons.mp hchain
          exact WithTop.add_ne_top.mpr
            ⟨hedge, induction htail⟩

lemma pathWeight_ne_top {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    {source target : Fin n} {path : List (Fin n)}
    (hpath : IsWeightedPath weight source target path) :
    pathWeight weight path ≠ ⊤ :=
  pathWeight_ne_top_of_isChain weight path hpath.isChain

lemma internalVerticesBelow_mono {n : Nat} {path : List (Fin n)} {k l : Nat}
    (hkl : k ≤ l) (hpath : InternalVerticesBelow k path) :
    InternalVerticesBelow l path := by
  intro vertex hvertex
  exact (hpath vertex hvertex).trans_le hkl

lemma internalVerticesBelow_append_tail {n : Nat} {k : Nat}
    {weight : Fin n → Fin n → WithTop Int} {source pivot target : Fin n}
    {left right : List (Fin n)}
    (hleft : IsWeightedPath weight source pivot left)
    (hright : IsWeightedPath weight pivot target right)
    (hleftBound : InternalVerticesBelow k left)
    (hrightBound : InternalVerticesBelow k right)
    (hpivot : pivot.val < k) :
    InternalVerticesBelow k (left ++ right.tail) := by
  cases left with
  | nil => exact False.elim (hleft.ne_nil rfl)
  | cons first leftTail =>
      cases right with
      | nil => exact False.elim (hright.ne_nil rfl)
      | cons rightFirst rightTail =>
          have hfirst : first = source := by simpa using hleft.head_eq
          have hrightFirst : rightFirst = pivot := by simpa using hright.head_eq
          subst first
          subst rightFirst
          cases leftTail with
          | nil => simpa [InternalVerticesBelow] using hrightBound
          | cons second leftRest =>
              cases rightTail with
              | nil => simpa [InternalVerticesBelow] using hleftBound
              | cons rightSecond rightRest =>
                  have hlast : (second :: leftRest).getLast (by simp) = pivot := by
                    simpa [List.getLast_cons] using hleft.getLast_eq
                  intro vertex hvertex
                  change vertex ∈
                    ((second :: leftRest) ++ (rightSecond :: rightRest)).dropLast at hvertex
                  rw [List.dropLast_append_of_ne_nil (by simp), List.mem_append] at hvertex
                  rcases hvertex with hleftMem | hrightMem
                  · have hdecomp : second :: leftRest =
                        (second :: leftRest).dropLast ++ [pivot] := by
                      simpa [hlast] using
                        (List.dropLast_append_getLast (l := second :: leftRest) (by simp)).symm
                    rw [hdecomp, List.mem_append] at hleftMem
                    simp only [List.mem_singleton] at hleftMem
                    rcases hleftMem with hleftInternal | rfl
                    · exact hleftBound vertex (by simpa [InternalVerticesBelow] using hleftInternal)
                    · exact hpivot
                  · exact hrightBound vertex (by
                      simpa [InternalVerticesBelow] using hrightMem)

lemma internalVertex_ne_source {n : Nat} {weight : Fin n → Fin n → WithTop Int}
    {source target vertex : Fin n} {path : List (Fin n)}
    (hpath : IsWeightedPath weight source target path) (hnodup : path.Nodup)
    (hvertex : vertex ∈ path.tail.dropLast) : vertex ≠ source := by
  cases path with
  | nil => exact False.elim (hpath.ne_nil rfl)
  | cons first rest =>
      have hfirst : first = source := by simpa using hpath.head_eq
      have hvertexRest : vertex ∈ rest :=
        List.mem_of_mem_dropLast hvertex
      intro heq
      subst vertex
      rw [← hfirst] at hvertexRest
      exact (List.nodup_cons.mp hnodup).1 hvertexRest

lemma internalVertex_ne_target {n : Nat} {weight : Fin n → Fin n → WithTop Int}
    {source target vertex : Fin n} {path : List (Fin n)}
    (hpath : IsWeightedPath weight source target path) (hnodup : path.Nodup)
    (hvertex : vertex ∈ path.tail.dropLast) : vertex ≠ target := by
  cases path with
  | nil => exact False.elim (hpath.ne_nil rfl)
  | cons first rest =>
      have hrest : rest ≠ [] := by
        intro hnil
        subst rest
        simp at hvertex
      have hlast : rest.getLast hrest = target := by
        simpa [List.getLast_cons hrest] using hpath.getLast_eq
      have htailNodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hsplit : (rest.dropLast ++ [rest.getLast hrest]).Nodup := by
        simpa [List.dropLast_append_getLast hrest] using htailNodup
      intro heq
      subst vertex
      rw [← hlast] at hvertex
      exact (List.nodup_append.mp hsplit).2.2 _ hvertex _ (by simp) rfl

lemma internal_mem_of_mem_of_ne_endpoints {n : Nat}
    {weight : Fin n → Fin n → WithTop Int} {source target vertex : Fin n}
    {path : List (Fin n)} (hpath : IsWeightedPath weight source target path)
    (hmem : vertex ∈ path) (hsource : vertex ≠ source) (htarget : vertex ≠ target) :
    vertex ∈ path.tail.dropLast := by
  cases path with
  | nil => contradiction
  | cons first rest =>
      have hfirst : first = source := by simpa using hpath.head_eq
      have hmemRest : vertex ∈ rest := by
        simp only [List.mem_cons] at hmem
        rcases hmem with hfirstMem | hrestMem
        · exact False.elim (hsource (hfirstMem ▸ hfirst))
        · exact hrestMem
      have hrest : rest ≠ [] := by
        intro hnil
        subst rest
        contradiction
      have hlast : rest.getLast hrest = target := by
        simpa [List.getLast_cons hrest] using hpath.getLast_eq
      apply List.mem_dropLast_of_mem_of_ne_getLast hmemRest
      simpa [hlast] using htarget

end Cslib.Algorithms.Lean.FloydWarshall.Internal
