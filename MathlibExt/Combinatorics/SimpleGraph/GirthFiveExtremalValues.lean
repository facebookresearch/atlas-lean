/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/ExGirthFive/README.md` (leansolving/SqueezeBench,
commit e2e19eef093a77882da57f348def029533ec2d5e): the table in the theorem statement.
Copyright the SqueezeBench contributors.
Authors: P. Manrique, H. Xia, S. Szeider.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
the definition `girthFiveExtremalNumber` is taken from leansolving/SqueezeBench
at commit e2e19eef093a77882da57f348def029533ec2d5e,
`SqueezeBench/Problems/ExGirthFive/Def.lean` (`f`; authors P. Manrique,
H. Xia, S. Szeider), and the values from the "Known values" section of
`SqueezeBench/Problems/ExGirthFive/README.md`, distributed under the Apache
License, Version 2.0. SqueezeBench ships no `NOTICE` file. Changes made:
renamed `f` to `girthFiveExtremalNumber`, dropped the `nMin = 1` pin (at
`n = 0` the supremum is already `0`) and the helper lemmas, and turned the
README values, which SqueezeBench marks as reporting only, into theorems.
The definition and the fifty-vertex result now live in
`MathlibExt/Combinatorics/SimpleGraph/GirthFiveExtremalNumber.lean`.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.GirthFiveExtremalNumber
import all MathlibExt.Combinatorics.SimpleGraph.GirthFiveExtremalNumber
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Eval
import Mathlib.Tactic.IntervalCases

/-!
# Extremal numbers for girth at least five

`girthFiveExtremalNumber_one_to_twenty` gives the maximum numbers of edges in graphs
without three- or four-cycles on one through twenty vertices.

Deleting a vertex of minimum degree from a sufficiently dense graph leaves a smaller graph
above the preceding edge threshold. To restore the vertex, its neighbors must be pairwise
at distance greater than two in that smaller graph. We enumerate all such neighbor sets
and check an explicit relabeling into the table at the next order. For the reverse bounds,
we check the edge count and common neighbors of a graph attaining each value.
-/

namespace MathlibExt.Combinatorics.SimpleGraph.GirthFiveExtremalValuesWanted

open Finset _root_.SimpleGraph

-- A row is the bit mask of the neighbors of a vertex.
private abbrev Rows := Array Nat

private def rowAdj (r : Rows) (i j : Nat) := r[i]!.testBit j

-- Vertices joined to a new vertex cannot be at distance one or two from each other.
private def compatible (r : Rows) (i j : Nat) : Bool :=
  !rowAdj r i j && r[i]! &&& r[j]! == 0

private def choices (r : Rows) : List Nat → List (List Nat)
  | [] => [[]]
  | i :: l =>
    let ss := choices r l
    ss ++ (ss.filter fun s => s.all (compatible r i)).map (i :: ·)

private theorem filter_mem_choices (r : Rows) (p : Nat → Bool) (l : List Nat)
    (hl : l.Nodup) (h : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → p i → p j → compatible r i j) :
    l.filter p ∈ choices r l := by
  induction l with
  | nil => simp [choices]
  | cons i l ih =>
    have ht := ih hl.of_cons (fun a ha b hb => h a (by simp [ha]) b (by simp [hb]))
    by_cases hp : p i
    · simp only [choices, List.mem_append, List.mem_map, List.mem_filter]
      right
      refine ⟨_, ⟨ht, List.all_eq_true.mpr ?_⟩, by simp [hp]⟩
      intro j hj
      obtain ⟨hj, hpj⟩ := List.mem_filter.mp hj
      exact h i (by simp) j (by simp [hj]) (fun e => hl.notMem (e ▸ hj)) hp hpj
    · simp [choices, hp, ht]

-- The incremental code keeps the edge count alongside the adjacency rows.
private abbrev Entry := Nat × Rows

private def bitMask (s : List Nat) := (s.map fun j => 1 <<< j).foldr (· ||| ·) 0

private theorem bitMask_spec (s : List Nat) (i : Nat) :
    (bitMask s).testBit i = true ↔ i ∈ s := by
  induction s with
  | nil => simp [bitMask]
  | cons j s ih =>
    change ((1 <<< j) ||| bitMask s).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq,
      ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

private def extendRows (n : Nat) (r : Rows) (s : List Nat) : Rows :=
  ((List.range n).map fun i => if i ∈ s then r[i]! ||| (1 <<< n) else r[i]!).toArray
    |>.push (bitMask s)

private def extensions (n threshold : Nat) (a : Entry) : List Entry := do
  let s ← choices a.2 (List.range n)
  guard (threshold ≤ a.1 + s.length)
  return (a.1 + s.length, extendRows n a.2 s)

-- A labeling lists every vertex exactly once and agrees with all the recorded rows.
private def Represents {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : Nat) (a : Entry) : Prop :=
  a.1 = #G.edgeFinset ∧
    ∃ e : Fin n ≃ V, ∀ i j : Fin n, rowAdj a.2 i j = true ↔ G.Adj (e i) (e j)

private lemma extendRows_old (n : Nat) (r : Rows) (s : List Nat) {i : Nat} (hi : i < n) :
    (extendRows n r s)[i]! = if i ∈ s then r[i]! ||| (1 <<< n) else r[i]! := by
  simp [extendRows, getElem!_pos, hi, Nat.lt_succ_of_lt hi]

private lemma extendRows_last (n : Nat) (r : Rows) (s : List Nat) :
    (extendRows n r s)[n]! = bitMask s := by
  simp [extendRows, getElem!_pos]

private theorem extend_represents {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hg : 5 ≤ G.egirth) (x : V) {n t : Nat}
    {a : Entry} (hr : Represents (G.induce {x}ᶜ) n a)
    (hb : ∀ i < n, a.2[i]! < 2 ^ n) (ht : t ≤ #G.edgeFinset) :
    ∃ b ∈ extensions n t a, Represents G (n + 1) b := by
  classical
  obtain ⟨hm, e, he⟩ := hr
  let p (i : Nat) : Bool := if hi : i < n then decide (G.Adj x (e ⟨i, hi⟩)) else false
  let s := (List.range n).filter p
  have hs (i : Nat) : i ∈ s ↔ ∃ hi : i < n, G.Adj x (e ⟨i, hi⟩) := by
    by_cases hi : i < n <;> simp [s, p, hi]
  have hslen : s.length = G.degree x := by
    rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _),
      ← G.card_neighborFinset_eq_degree]
    apply card_bij (fun i hi => (e ⟨i, ((hs i).mp (List.mem_toFinset.mp hi)).choose⟩ : V))
    · intro i hi
      exact (G.mem_neighborFinset _ _).mpr ((hs i).mp (List.mem_toFinset.mp hi)).choose_spec
    · intro i hi j hj hij
      exact congrArg Fin.val (e.injective (Subtype.ext hij))
    · intro v hv
      have hxv := (G.mem_neighborFinset _ _).mp hv
      obtain ⟨i, hi⟩ := e.surjective ⟨v, hxv.ne.symm⟩
      exact ⟨i.val, List.mem_toFinset.mpr ((hs _).mpr ⟨i.isLt, by simpa [hi]⟩),
        congrArg Subtype.val hi⟩
  have hc : s ∈ choices a.2 (List.range n) := by
    apply filter_mem_choices _ _ _ List.nodup_range
    intro i hi j hj hij hpi hpj
    have hi' := List.mem_range.mp hi
    have hj' := List.mem_range.mp hj
    let u : Fin n := ⟨i, hi'⟩
    let v : Fin n := ⟨j, hj'⟩
    have hu : G.Adj x (e u) := by simpa [p, hi', u] using hpi
    have hv : G.Adj x (e v) := by simpa [p, hj', v] using hpj
    have hne : (e u : V) ≠ (e v : V) :=
      fun h => hij (congrArg Fin.val (e.injective (Subtype.ext h)))
    have hadj : ¬ rowAdj a.2 i j := fun h => no_triangle hg hu ((he u v).mp h) hv.symm
    have hzero : a.2[i]! &&& a.2[j]! = 0 := by
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, Nat.zero_testBit]
      by_cases hk : k < n
      · apply Bool.eq_false_iff.mpr
        intro hh
        obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp hh
        exact no_quadrangle hg hu ((he u ⟨k, hk⟩).mp h₁) ((he v ⟨k, hk⟩).mp h₂).symm
          hv.symm (Ne.symm (show (e ⟨k, hk⟩ : V) ≠ x from (e ⟨k, hk⟩).property)) hne
      · simp [Nat.testBit_lt_two_pow ((hb i hi').trans_le (Nat.pow_le_pow_right (by decide)
            (Nat.le_of_not_gt hk)))]
    simp [compatible, hadj, hzero]
  have hm' : a.1 + s.length = #G.edgeFinset := by
    rw [hm, G.card_edgeFinset_induce_compl_singleton, G.card_edgeFinset_deleteIncidenceSet, hslen]
    exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset x)
  refine ⟨(a.1 + s.length, extendRows n a.2 s), ?_, hm', ?_⟩
  · change _ ∈ List.flatMap _ _
    apply List.mem_flatMap.mpr
    exact ⟨s, hc, by simp [guard, hm', ht, pure, Bind.bind]⟩
  let E := finSuccEquivLast.trans (e.optionCongr.trans (Equiv.optionSubtypeNe x))
  have hE (i : Fin n) : E i.castSucc = e i := by
    simp only [E, Equiv.trans_apply, finSuccEquivLast_castSucc]
    rfl
  have hL : E (Fin.last n) = x := by
    simp only [E, Equiv.trans_apply, finSuccEquivLast_last]
    rfl
  refine ⟨E, ?_⟩
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [rowAdj, extendRows_last, hL, bitMask_spec, hs]
  · simp [rowAdj, extendRows_last, hL, hE, bitMask_spec, hs, j.isLt]
  · by_cases h : (i : Nat) ∈ s
    · have hi := ((hs _).mp h).choose_spec
      simp [rowAdj, extendRows_old _ _ _ i.isLt, hL, hE, h, Nat.testBit_or, Nat.one_shiftLeft,
        hi.symm]
    · have hi : ¬ G.Adj (e i) x := fun ha => h ((hs _).mpr ⟨i.isLt, ha.symm⟩)
      simp [rowAdj, extendRows_old _ _ _ i.isLt, hL, hE, h, Nat.testBit_lt_two_pow (hb i i.isLt),
        hi]
  · by_cases hi : (i : Nat) ∈ s <;>
      simpa [rowAdj, extendRows_old _ _ _ i.isLt, hi, hE, Nat.testBit_or, Nat.one_shiftLeft,
        Nat.testBit_two_pow, Nat.ne_of_gt j.isLt] using he i j

-- Only graphs dense enough to be predecessors of a possible extremizer need be kept.
private def threshold (n : Nat) : Nat :=
  #[0, 0, 1, 2, 3, 4, 5, 7, 9, 11, 13, 15, 17, 19, 22, 25, 28, 31, 34, 37, 41][n]!

private def expected (n : Nat) : Nat :=
  #[0, 0, 1, 2, 3, 5, 6, 8, 10, 12, 15, 16, 18, 21, 23, 26, 28, 31, 34, 38, 41][n]!

-- Refine vertex classes by their neighbor counts in each class. If refinement stalls,
-- distinguish one vertex of a nonsingleton class. This just proposes a relabeling.
private def orderVertices (r : Rows) (n : Nat) : Array Nat := Id.run do
  let mut cells := [List.range n]
  for _ in [:n] do
    if cells.length == n then break
    let signature := fun i => cells.foldl (init := 0) fun key c =>
      key * (n + 1) + c.countP (rowAdj r i)
    let refined := cells.flatMap fun c =>
      let tags := c.map signature
      (tags.eraseDups.mergeSort).map fun tag => c.filter (fun i => signature i == tag)
    if refined.length == cells.length then
      match cells.span (fun c => c.length ≤ 1) with
      | (l, (i :: is) :: rest) => cells := l ++ [[i], is] ++ rest
      | _ => break
    else cells := refined
  return cells.flatten.toArray

-- Each extension carries an index into the next table and its proposed vertex order.
-- Five bits per vertex and ten for the table index suffice at these orders.
private def packOrder (p : Array Nat) := p.foldr (fun i tail => i ||| (tail <<< 5)) 0

private def label (code i : Nat) := (code >>> (5 * i)) % 32

private abbrev Level := Array Entry × Array (Array Nat)

private def nextLevel (n : Nat) (prev : Array Entry) : Level := Id.run do
  let mut nodes : Array Entry := #[]
  let mut hints := #[]
  for a in prev do
    let mut row := #[]
    for b in extensions n (threshold (n + 1)) a do
      let order := orderVertices b.2 (n + 1)
      let graph := order.map fun i =>
        bitMask ((List.range (n + 1)).filter fun j => rowAdj b.2 i order[j]!)
      let normalized := (b.1, graph)
      let k := nodes.idxOf normalized
      if k == nodes.size then nodes := nodes.push normalized
      row := row.push (k ||| (packOrder order <<< 10))
    hints := hints.push row
  return (nodes, hints)

-- Materialize one order at a time so each table can be used directly by the kernel.
set_option maxRecDepth 32768

private def level0 : Level := (#[(0, #[])], #[])

private def level1 : Level := eval% nextLevel 0 level0.1

private def level2 : Level := eval% nextLevel 1 level1.1

private def level3 : Level := eval% nextLevel 2 level2.1

private def level4 : Level := eval% nextLevel 3 level3.1

private def level5 : Level := eval% nextLevel 4 level4.1

private def level6 : Level := eval% nextLevel 5 level5.1

private def level7 : Level := eval% nextLevel 6 level6.1

private def level8 : Level := eval% nextLevel 7 level7.1

private def level9 : Level := eval% nextLevel 8 level8.1

private def level10 : Level := eval% nextLevel 9 level9.1

private def level11 : Level := eval% nextLevel 10 level10.1

private def level12 : Level := eval% nextLevel 11 level11.1

private def level13 : Level := eval% nextLevel 12 level12.1

private def level14 : Level := eval% nextLevel 13 level13.1

private def level15 : Level := eval% nextLevel 14 level14.1

private def level16 : Level := eval% nextLevel 15 level15.1

private def level17 : Level := eval% nextLevel 16 level16.1

private def level18 : Level := eval% nextLevel 17 level17.1

private def level19 : Level := eval% nextLevel 18 level18.1

private def level20 : Level := eval% nextLevel 19 level19.1

private def levels : Array Level := #[
  level0, level1, level2, level3, level4, level5, level6, level7, level8, level9,
  level10, level11, level12, level13, level14, level15, level16, level17, level18, level19,
  level20]

private def nodes (n : Nat) := (levels[n]!).1

-- These checks use only the proposed permutation and the two actual adjacency matrices.
private def validHint (n : Nat) (a b : Entry) (p : Nat) : Bool :=
  let vs := List.range n
  a.1 == b.1 && vs.all fun i =>
    (label p i) < n && (vs.any fun j => (label p j) == i) &&
    vs.all fun j => rowAdj b.2 i j == rowAdj a.2 (label p i) (label p j)

private def validRow (n i : Nat) : Bool :=
  let a := (nodes n)[i]!
  let bs := extensions n (threshold (n + 1)) a
  let hints := (levels[n + 1]!.2)[i]!
  (List.range n).all (fun j => a.2[j]! < 2 ^ n) &&
    (List.range bs.length).all fun j =>
      let k := hints[j]! % 1024
      let p := hints[j]! >>> 10
      k < (nodes (n + 1)).size && validHint (n + 1) bs[j]! (nodes (n + 1))[k]! p

private def validStep (n : Nat) : Bool :=
  (List.range (nodes n).size).all (validRow n)

-- Check four predecessor graphs per kernel reduction to bound peak memory.
private lemma checkChunks (n : Nat) (k := ((nodes n).size + 3) / 4) (hk : (nodes n).size ≤ k * 4)
    (h : ∀ q : Fin k, (List.range 4).all fun r =>
      let i := 4 * q.val + r
      i ≥ (nodes n).size || validRow n i) : validStep n := by
  apply List.all_eq_true.mpr
  intro i hi
  have hi' := List.mem_range.mp hi
  have hq : i / 4 < k := by omega
  have hr := List.all_eq_true.mp (h ⟨_, hq⟩) (i % 4) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have he : 4 * (i / 4) + i % 4 = i := by omega
  simpa [he, Nat.not_le_of_gt hi'] using hr

set_option maxHeartbeats 8000000 in
-- The finite case split checks all batches of extensions at all twenty orders.
private lemma steps_checked : ∀ i < 20, validStep i := by
  intro i hi
  interval_cases i <;> apply checkChunks _ (hk := by decide) <;>
    intro q <;> fin_cases q <;> decide +kernel

private lemma relabel_represents {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n : Nat} {a b : Entry} {p : Nat}
    (ha : Represents G n a) (h : validHint n a b p) : Represents G n b := by
  simp only [validHint, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨hm, e, he⟩ := ha
  let f (i : Fin n) : Fin n := ⟨label p i, (h.2 i i.isLt).1.1⟩
  have hf : Function.Surjective f := by
    intro i
    obtain ⟨j, hj, hji⟩ := (h.2 i i.isLt).1.2
    exact ⟨⟨j, hj⟩, Fin.ext hji⟩
  let E := Equiv.ofBijective f ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf, rfl⟩)
  refine ⟨h.1 ▸ hm, E.trans e, fun i j => ?_⟩
  rw [(h.2 i i.isLt).2 j j.isLt]
  exact he (f i) (f j)

private lemma extend_table {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n : Nat} (hg : 5 ≤ G.egirth) (x : V)
    (ht : threshold (n + 1) ≤ #G.edgeFinset) (hc : validStep n)
    (ih : ∃ i < (nodes n).size, Represents (G.induce {x}ᶜ) n (nodes n)[i]!) :
    ∃ k < (nodes (n + 1)).size, Represents G (n + 1) (nodes (n + 1))[k]! := by
  simp only [validStep, validRow, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨i, hi, ha⟩ := ih
  obtain ⟨b, hb, hr⟩ := extend_represents G hg x ha (hc i hi).1 ht
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hb
  obtain ⟨hk, hh⟩ := (hc i hi).2 j hj
  rw [getElem!_pos (extensions n (threshold (n + 1)) (nodes n)[i]!) j hj, he] at hh
  exact ⟨_, hk, relabel_represents hr hh⟩

private lemma threshold_delete {n m d : Nat} (hn : n < 20) (ht : threshold (n + 1) ≤ m)
    (hd : (n + 1) * d ≤ 2 * m) (hzero : d ≤ n) : threshold n ≤ m - d := by
  interval_cases n <;> norm_num [threshold] at ht hd ⊢ <;> omega

private lemma table_complete {n : Nat} (hn : n ≤ 20)
    (steps : ∀ i < 20, validStep i) {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hv : Fintype.card V = n)
    (hg : 5 ≤ G.egirth) (ht : threshold n ≤ #G.edgeFinset) :
    ∃ i < (nodes n).size, Represents G n (nodes n)[i]! := by
  classical
  induction n generalizing V with
  | zero =>
    have := Fintype.card_eq_zero_iff.mp hv
    refine ⟨0, by decide, ?_, Fintype.equivOfCardEq (by simp), fun i => i.elim0⟩
    have h := G.card_edgeFinset_le_card_choose_two
    change 0 = #G.edgeFinset
    apply Nat.eq_zero_of_le_zero ?_ |>.symm
    exact h.trans (by simp)
  | succ n ih =>
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨x, hx⟩ := G.exists_minimal_degree_vertex
    have havg := sum_le_sum (s := univ) fun v _ => G.minDegree_le_degree v
    simp only [sum_const, card_univ, smul_eq_mul, hv, G.sum_degrees_eq_twice_card_edges, hx] at havg
    have hd := G.minDegree_lt_card
    rw [hv, hx] at hd
    have hsmall := threshold_delete (by omega : n < 20) ht havg (by omega)
    apply extend_table hg x ht (steps n (by omega))
    apply ih (by omega)
    · rw [Fintype.card_compl_set, hv, Fintype.card_unique]
      omega
    · exact hg.trans (Embedding.induce _).isContained.egirth_le
    · simpa only [G.card_edgeFinset_induce_compl_singleton, G.card_edgeFinset_deleteIncidenceSet]
        using hsmall

-- Use a table entry at the claimed edge count as a witness. Its edges and short-cycle
-- constraints are checked independently of the enumeration.
private def witnessRows (n : Nat) : Rows :=
  ((nodes n).find? fun a => a.1 == expected n).getD (0, #[]) |>.2

private def witnessGraph (n : Nat) : SimpleGraph (Fin n) :=
  fromRel fun i j => rowAdj (witnessRows n) i j = true

private instance decWitnessAdj (n : Nat) : DecidableRel (witnessGraph n).Adj :=
  inferInstanceAs (DecidableRel (fromRel _).Adj)

private lemma witness_edges (n : Fin 21) : #(witnessGraph n).edgeFinset = expected n := by
  have hs : ∀ n : Fin 21, ∑ v, (witnessGraph n).degree v = 2 * expected n := by
    simp only [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    decide +kernel
  have h := hs n
  rw [sum_degrees_eq_twice_card_edges] at h
  omega

private lemma witness_common : ∀ (n : Fin 21) (i j : Fin n), i ≠ j →
    #((witnessGraph n).neighborFinset i ∩ (witnessGraph n).neighborFinset j) ≤
      if (witnessGraph n).Adj i j then 0 else 1 := by
  simp only [neighborFinset_eq_filter]
  decide +kernel

private lemma witness_girth (n : Fin 21) : 5 ≤ (witnessGraph n).egirth := by
  rw [le_egirth]
  intro u p hp
  change (↑(5 : Nat) : ℕ∞) ≤ ↑p.length
  rw [ENat.natCast_le_natCast]
  by_contra! h
  have hlen := hp.three_le_length
  have mem_common {a b c} (hac : (witnessGraph n).Adj a c) (hbc : (witnessGraph n).Adj b c) :
      c ∈ (witnessGraph n).neighborFinset a ∩ (witnessGraph n).neighborFinset b := by
    simp [hac, hbc]
  rcases (show p.length = 3 ∨ p.length = 4 by omega) with h3 | h4
  · obtain ⟨f⟩ := (cycleGraph_isContained_iff (by decide : 2 < 3)).2 ⟨u, p, hp, h3⟩
    have edge (i j : Fin 3) (hij : (cycleGraph 3).Adj i j) := f.toHom.map_rel hij
    have h01 := edge 0 1 (by decide)
    have hpos := card_pos.mpr ⟨_, mem_common (edge 0 2 (by decide)) (edge 1 2 (by decide))⟩
    have hle := witness_common n _ _ h01.ne
    simp only [h01, ite_true] at hle
    omega
  · obtain ⟨f⟩ := (cycleGraph_isContained_iff (by decide : 2 < 4)).2 ⟨u, p, hp, h4⟩
    have edge (i j : Fin 4) (hij : (cycleGraph 4).Adj i j) := f.toHom.map_rel hij
    have hc := witness_common n _ _ (f.injective.ne (by decide : (0 : Fin 4) ≠ 2))
    have hle : #((witnessGraph n).neighborFinset (f 0) ∩
        (witnessGraph n).neighborFinset (f 2)) ≤ 1 := hc.trans (by split <;> decide)
    exact f.injective.ne (by decide : (1 : Fin 4) ≠ 3) (card_le_one_iff.mp hle
      (mem_common (edge 0 1 (by decide)) (edge 2 1 (by decide)))
      (mem_common (edge 0 3 (by decide)) (edge 2 3 (by decide))))

private theorem value_at (n : Fin 21) : girthFiveExtremalNumber n = expected n := by
  have bounds : ∀ n : Fin 21, threshold n ≤ expected n ∧
      ((List.range (nodes n).size).all fun i => (nodes n)[i]!.1 ≤ expected n) := by decide +kernel
  classical
  apply le_antisymm
  · unfold girthFiveExtremalNumber
    refine Finset.sup_le fun G hG => ?_
    have hg : 5 ≤ G.egirth := (mem_filter.mp hG).2
    by_cases ht : threshold n ≤ #G.edgeFinset
    · obtain ⟨i, hi, hr⟩ := table_complete (by omega : n.val ≤ 20)
        steps_checked G (Fintype.card_fin _) hg ht
      have hb := List.all_eq_true.mp (bounds n).2 i (List.mem_range.mpr hi)
      rw [← hr.1]
      exact of_decide_eq_true hb
    · exact (Nat.le_of_not_ge ht).trans (bounds n).1
  · unfold girthFiveExtremalNumber
    refine le_trans ?_ (Finset.le_sup (b := witnessGraph n) ?_)
    · convert (witness_edges n).ge
    · simpa only [mem_filter, mem_univ, true_and] using witness_girth n

/-- **Girth-five extremal numbers up to twenty vertices.** For $n = 1, 2, \dots, 20$ the
girth-five extremal numbers $\mathrm{ex}(n; \{C_3, C_4\})$, the largest numbers of edges of a
simple graph on $n$ vertices that contains no triangle and no four-cycle, are, in order,
$0, 1, 2, 3, 5, 6, 8, 10, 12, 15, 16, 18, 21, 23, 26, 28, 31, 34, 38, 41$.

Source: D. K. Garnick, Y. H. H. Kwong, and F. Lazebnik, *Extremal graphs without
three-cycles or four-cycles*, J. Graph Theory 17 (1993), 633–645 (`n ≤ 24`);
OEIS A006856; listed in leansolving/SqueezeBench
`SqueezeBench/Problems/ExGirthFive/README.md`. -/
public theorem girthFiveExtremalNumber_one_to_twenty :
    (List.range 20).map (fun i => girthFiveExtremalNumber (i + 1)) =
      [0, 1, 2, 3, 5, 6, 8, 10, 12, 15, 16, 18, 21, 23, 26, 28, 31, 34, 38, 41] := by
  calc
    _ = (List.range 20).map (fun i => expected (i + 1)) := by
      apply List.map_congr_left
      intro i hi
      have hi' := List.mem_range.mp hi
      exact value_at ⟨i + 1, by omega⟩
    _ = _ := by decide

end MathlibExt.Combinatorics.SimpleGraph.GirthFiveExtremalValuesWanted
