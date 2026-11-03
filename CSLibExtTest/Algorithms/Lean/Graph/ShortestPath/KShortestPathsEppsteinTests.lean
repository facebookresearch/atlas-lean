/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.KShortestPathsEppstein

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.KShortestPathsEppsteinTests

open Cslib.Algorithms.Lean.KShortestPathsEppstein

#check eppDelta
#check DiWalk
#check DiWalk.length
#check DiWalk.sidetracks
#check listSidetrackSum
#check lemma1_delta_nonneg
#check lemma1_delta_tree
#check lemma1_all_nonneg
#check lemma2_telescoping
#check lemma2_sidetrack
#check lemma2_path_length
#check sidetrackSum_eq_listSum
#check lemma3_core
#check lemma3_prefpath_le
#check PPath
#check PPath.weight
#check PPath.sidetrackList
#check IsBFSTrace
#check lemma5_decode
#check lemma5_encode
#check DiWalk_eq_of_sidetracks_eq
#check PPath_eq_of_sidetrackList_eq
#check lemma6_weight_mono
#check lemma7_parent_weight
#check thm1_bfs_enumeration
#check thm1_bfs_enumeration_unique
#check thm2_all_dests
#check thm2_bfs_enumeration_unique

/-! ## Concrete fixtures

A four-vertex graph with a path tree and two competing routes from `0`
to `3`, used below to exercise the path API on concrete walks,
sidetracks, weights, and traces rather than under abstract hypotheses;
and a cyclic tree where tree walks are not unique, documenting the
collapse the `htree` hypotheses exclude. -/

/-- The concrete graph: the tree path `0 → 1 → 2 → 3` plus the
sidetracks `(0, 2)`, `(0, 3)`, and `(1, 3)`. -/
def fourG : Digraph (Fin 4) where
  Adj a b := (a.val, b.val) ∈ [(0, 1), (1, 2), (2, 3), (0, 2), (0, 3), (1, 3)]

/-- The tree path `0 → 1 → 2 → 3`. -/
def fourT : Digraph (Fin 4) where
  Adj a b := (a.val, b.val) ∈ [(0, 1), (1, 2), (2, 3)]

/-- Distances to `3` along the tree. -/
def fourDist : Fin 4 → ℝ := fun a => 3 - (a.val : ℝ)

/-- Edge lengths: tree-consistent, except `(0, 2)`, which carries a
penalty of `3` (positive `δ`). -/
def fourLen : Fin 4 → Fin 4 → ℝ :=
  fun a b => ((b.val : ℝ) - (a.val : ℝ)) + (if a = 0 ∧ b = 2 then 3 else 0)

/-- Triangle inequality for the concrete lengths and distances. -/
theorem fourHtri : ∀ a b : Fin 4, fourG.Adj a b → fourDist a ≤ fourLen a b + fourDist b := by
  intro a b hadj
  fin_cases a
  all_goals fin_cases b
  all_goals simp [fourG, fourLen, fourDist] at hadj ⊢
  all_goals norm_num

/-- Tree edges are graph edges. -/
theorem fourTle : ∀ a b : Fin 4, fourT.Adj a b → fourG.Adj a b := by
  intro a b hadj
  fin_cases a
  all_goals fin_cases b
  all_goals simp [fourT, fourG] at hadj ⊢

/-- Tree edges are tight (`δ = 0`). -/
theorem fourTightDelta : ∀ a b : Fin 4, fourT.Adj a b →
    eppDelta fourLen fourDist a b = 0 := by
  intro a b hadj
  fin_cases a
  all_goals fin_cases b
  all_goals simp [fourT, eppDelta, fourLen, fourDist] at hadj ⊢

/-- Every vertex reaches `3` by a tree walk. -/
theorem fourTreeWalkExists (a : Fin 4) : Nonempty (DiWalk fourT a 3) := by
  fin_cases a
  · exact ⟨DiWalk.cons 0 1 3 (by simp [fourT]) (DiWalk.cons 1 2 3 (by simp [fourT])
      (DiWalk.cons 2 3 3 (by simp [fourT]) (DiWalk.nil 3)))⟩
  · exact ⟨DiWalk.cons 1 2 3 (by simp [fourT]) (DiWalk.cons 2 3 3 (by simp [fourT])
      (DiWalk.nil 3))⟩
  · exact ⟨DiWalk.cons 2 3 3 (by simp [fourT]) (DiWalk.nil 3)⟩
  · exact ⟨DiWalk.nil 3⟩

/-- Tree route `0 → 1 → 2 → 3`. -/
def fourTreeWalk : DiWalk fourG 0 3 :=
  DiWalk.cons 0 1 3 (by simp [fourG]) (DiWalk.cons 1 2 3 (by simp [fourG])
    (DiWalk.cons 2 3 3 (by simp [fourG]) (DiWalk.nil 3)))

/-- Direct sidetrack route `0 → 3`. -/
def fourDirectWalk : DiWalk fourG 0 3 :=
  DiWalk.single (by simp [fourG] : fourG.Adj 0 3)

/-- Sidestep to `(0, 3)`: zero `δ`, tied with the root. -/
def fourQ03 : PPath fourG fourT 0 3 :=
  PPath.sidestep (0, 3) PPath.root (DiWalk.nil 0) (by simp [fourG]) (by simp [fourT])

/-- Sidestep to `(1, 3)` via the tree walk `0 → 1`: zero `δ`, tied with
`fourQ03`. -/
def fourQ13 : PPath fourG fourT 0 3 :=
  PPath.sidestep (1, 3) PPath.root
    (DiWalk.cons 0 1 1 (by simp [fourT]) (DiWalk.nil 1)) (by simp [fourG])
    (by simp [fourT])

/-- Sidestep to `(0, 2)`: positive `δ`. -/
def fourQ02 : PPath fourG fourT 0 2 :=
  PPath.sidestep (0, 2) PPath.root (DiWalk.nil 0) (by simp [fourG]) (by simp [fourT])

/-- Number of steps in a walk (test-only discriminator). -/
def walkSteps {V : Type*} {G : Digraph V} {a b : V} : DiWalk G a b → ℕ
  | .nil _ => 0
  | .cons _ _ _ _ tl => walkSteps tl + 1

/-- Total number of tree-walk steps joining the sidetracks of a `PPath`
(test-only discriminator). -/
def ppathTwSteps {V : Type*} {G T : Digraph V} {s c : V} : PPath G T s c → ℕ
  | .root => 0
  | .sidestep _ prev tw _ _ => ppathTwSteps prev + walkSteps tw

/-- A cyclic tree: `0 → 1 → 0`, plus `1 → 2`. Tree walks are not unique
here, which is exactly the collapse the `htree` hypotheses exclude. -/
def cycleT : Digraph (Fin 3) where
  Adj a b := (a.val, b.val) ∈ [(0, 1), (1, 0), (1, 2)]

/-- The cyclic tree plus the sidetrack `(0, 2)`. -/
def cycleG : Digraph (Fin 3) where
  Adj a b := (a.val, b.val) ∈ [(0, 1), (1, 0), (1, 2), (0, 2)]

/-- Tree-only route `0 → 1 → 2` in the cyclic tree. -/
def cycleTreeWalk : DiWalk cycleG 0 2 :=
  DiWalk.cons 0 1 2 (by simp [cycleG]) (DiWalk.cons 1 2 2 (by simp [cycleG])
    (DiWalk.nil 2))

/-- Route `0 → 1 → 0 → 1 → 2` in the cyclic tree: same sidetracks as
`cycleTreeWalk`, a different walk. -/
def cycleWalk : DiWalk cycleG 0 2 :=
  DiWalk.cons 0 1 2 (by simp [cycleG]) (DiWalk.cons 1 0 2 (by simp [cycleG])
    (DiWalk.cons 0 1 2 (by simp [cycleG]) (DiWalk.cons 1 2 2 (by simp [cycleG])
      (DiWalk.nil 2))))

/-- Sidestep to `(0, 2)` with the empty joining tree walk. -/
def cycleQA : PPath cycleG cycleT 0 2 :=
  PPath.sidestep (0, 2) PPath.root (DiWalk.nil 0) (by simp [cycleG]) (by simp [cycleT])

/-- Sidestep to `(0, 2)` with the joining tree walk `0 → 1 → 0`: same
sidetrack list as `cycleQA`, a different `PPath`. -/
def cycleQB : PPath cycleG cycleT 0 2 :=
  PPath.sidestep (0, 2) PPath.root
    (DiWalk.cons 0 1 0 (by simp [cycleT]) (DiWalk.cons 1 0 0 (by simp [cycleT])
      (DiWalk.nil 0))) (by simp [cycleG]) (by simp [cycleT])

-- `δ` unfolds to its defining arithmetic expression.
example (len : Fin 2 → Fin 2 → ℝ) (dist : Fin 2 → ℝ) (u v : Fin 2) :
    eppDelta len dist u v = len u v + dist v - dist u := rfl

-- Lemma 1 applies on a concrete triangle inequality witness.
example (len : Fin 2 → Fin 2 → ℝ) (dist : Fin 2 → ℝ)
    (G : Digraph (Fin 2)) (u v : Fin 2) (hadj : G.Adj u v)
    (htri : dist u ≤ len u v + dist v) :
    0 ≤ eppDelta len dist u v :=
  lemma1_delta_nonneg len dist hadj htri

-- Lemma 2 telescopes on the empty walk.
example (len : Fin 2 → Fin 2 → ℝ) (dist : Fin 2 → ℝ)
    (G : Digraph (Fin 2)) (u : Fin 2) :
    (DiWalk.nil u : DiWalk G u u).length len
      = dist u - dist u + (DiWalk.nil u : DiWalk G u u).deltaSum len dist :=
  lemma2_telescoping len dist (DiWalk.nil u)

-- Lemma 6 applies to a single sidestep extension.
example (len : Fin 2 → Fin 2 → ℝ) (dist : Fin 2 → ℝ)
    {G T : Digraph (Fin 2)} {s a : Fin 2} (q : PPath G T s a) (e : Fin 2 × Fin 2)
    (tw : DiWalk T a e.1) (hadj : G.Adj e.1 e.2) (hside : ¬ T.Adj e.1 e.2)
    (hδ : 0 ≤ eppDelta len dist e.1 e.2) :
    q.weight len dist ≤ (PPath.sidestep e q tw hadj hside).weight len dist :=
  lemma6_weight_mono len dist q e tw hadj hside hδ

-- `lemma5_encode` is purely combinatorial: it needs no lengths,
-- potentials, or spanning-tree witness, only the walk and `T`.
example {G T : Digraph (Fin 2)} {s t : Fin 2} (p : DiWalk G s t) :
    ∃ (c : Fin 2) (q : PPath G T s c), q.sidetrackList = p.sidetracks T :=
  lemma5_encode T p

-- Under unique tree walks, equal sidetrack lists identify walks.
example {G T : Digraph (Fin 2)}
    (htree : ∀ a b (p q : DiWalk T a b), p = q)
    (Tle : ∀ a b : Fin 2, T.Adj a b → G.Adj a b) {s t : Fin 2}
    (p q : DiWalk G s t) (h : p.sidetracks T = q.sidetracks T) : p = q :=
  DiWalk_eq_of_sidetracks_eq htree Tle _ p q h rfl

-- Under unique tree walks, equal sidetrack lists identify `PPath`s.
example {G T : Digraph (Fin 2)}
    (htree : ∀ a b (p q : DiWalk T a b), p = q) {s : Fin 2}
    {c1 c2 : Fin 2} (q1 : PPath G T s c1) (q2 : PPath G T s c2)
    (h : q1.sidetrackList = q2.sidetrackList) :
    (⟨c1, q1⟩ : Σ c, PPath G T s c) = ⟨c2, q2⟩ :=
  PPath_eq_of_sidetrackList_eq htree q1 q2 h

-- The unique-decoding variant decodes each trace output to exactly one walk.
example (T : Digraph (Fin 2)) (len : Fin 2 → Fin 2 → ℝ) (dist : Fin 2 → ℝ)
    {G : Digraph (Fin 2)} {s t : Fin 2}
    (htree : ∀ a b (p q : DiWalk T a b), p = q)
    (Tle : ∀ a b : Fin 2, T.Adj a b → G.Adj a b)
    (treeWalk : ∀ a : Fin 2, DiWalk T a t)
    (hdist_t : dist t = 0)
    (htight : ∀ a b : Fin 2, T.Adj a b → len a b + dist b = dist a)
    (htri : ∀ a b : Fin 2, G.Adj a b → dist a ≤ len a b + dist b)
    (L : List (Σ c, PPath G T s c)) (hTrace : IsBFSTrace G T s len dist L)
    (x : Σ c, PPath G T s c) (hx : x ∈ L) :
    ∃! p : DiWalk G s t,
      p.sidetracks T = x.2.sidetrackList ∧
      p.length len = dist s + x.2.weight len dist := by
  obtain ⟨-, -, -, hDecU, -⟩ :=
    thm1_bfs_enumeration_unique T len dist htree Tle treeWalk hdist_t htight
      htri L hTrace
  exact hDecU x hx

-- The tree route has no sidetracks.
example : fourTreeWalk.sidetracks fourT = [] := by
  have h01 : fourT.Adj 0 1 := by simp [fourT]
  have h12 : fourT.Adj 1 2 := by simp [fourT]
  have h23 : fourT.Adj 2 3 := by simp [fourT]
  simp only [fourTreeWalk, DiWalk.sidetracks, h01, h12, h23, ite_true]

-- The direct route has the genuine sidetrack `(0, 3)`.
example : fourDirectWalk.sidetracks fourT = [(0, 3)] := by
  have hside : ¬ fourT.Adj 0 3 := by simp [fourT]
  simp only [fourDirectWalk, DiWalk.single, DiWalk.sidetracks, hside, ite_false]

-- The two competing routes have equal length: a zero-`δ` tie. The tree
-- route costs `1 + 1 + 1` and the direct route costs `3`.
example : fourTreeWalk.length fourLen = fourDirectWalk.length fourLen := by
  have hTree : fourTreeWalk.length fourLen = 3 := by
    simp only [fourTreeWalk, DiWalk.length, fourLen]
    norm_num
  have hDirect : fourDirectWalk.length fourLen = 3 := by
    simp only [fourDirectWalk, DiWalk.single, DiWalk.length, fourLen]
    norm_num
  rw [hTree, hDirect]

-- The sidetrack lists of the two zero-`δ` sidesteps.
example : fourQ03.sidetrackList = [(0, 3)] := rfl
example : fourQ13.sidetrackList = [(1, 3)] := rfl

-- Both zero-`δ` sidesteps weigh `0`, tied with the root.
example : fourQ03.weight fourLen fourDist = 0 := by
  norm_num [fourQ03, PPath.weight, eppDelta, fourLen, fourDist]
example : fourQ13.weight fourLen fourDist = 0 := by
  norm_num [fourQ13, PPath.weight, eppDelta, fourLen, fourDist]

-- The `(0, 2)` sidestep has positive weight `3`, above the ties.
example : fourQ02.weight fourLen fourDist = 3 := by
  norm_num [fourQ02, PPath.weight, eppDelta, fourLen, fourDist]

-- Equal weights do not identify the outputs: the two tied sidesteps are
-- distinct nodes of the path tree.
example : fourQ03.weight fourLen fourDist = fourQ13.weight fourLen fourDist ∧
    (⟨3, fourQ03⟩ : Σ c, PPath fourG fourT 0 c) ≠ ⟨3, fourQ13⟩ := by
  have hw03 : fourQ03.weight fourLen fourDist = 0 := by
    norm_num [fourQ03, PPath.weight, eppDelta, fourLen, fourDist]
  have hw13 : fourQ13.weight fourLen fourDist = 0 := by
    norm_num [fourQ13, PPath.weight, eppDelta, fourLen, fourDist]
  refine ⟨by rw [hw03, hw13], ?_⟩
  intro h
  have h2 := congrArg (fun x : Σ c, PPath fourG fourT 0 c => x.2.sidetrackList) h
  simp [fourQ03, fourQ13, PPath.sidetrackList] at h2

-- A hand-built two-step abstract trace: root, then the two tied
-- zero-`δ` outputs in either tie order. This is a specification
-- instance built with `IsBFSTrace.step`; no algorithm is run. Frontier
-- minimality at each step follows from `PPath_weight_nonneg`: every
-- frontier node weighs at least `0`, and each chosen node weighs `0`.
example : IsBFSTrace fourG fourT 0 fourLen fourDist
    [⟨0, PPath.root⟩, ⟨3, fourQ03⟩, ⟨3, fourQ13⟩] := by
  have hnonneg : ∀ x : Σ c, PPath fourG fourT 0 c,
      0 ≤ x.2.weight fourLen fourDist :=
    fun x => PPath_weight_nonneg fourLen fourDist fourHtri x.2
  have hw03 : fourQ03.weight fourLen fourDist = 0 := by
    norm_num [fourQ03, PPath.weight, eppDelta, fourLen, fourDist]
  have hw13 : fourQ13.weight fourLen fourDist = 0 := by
    norm_num [fourQ13, PPath.weight, eppDelta, fourLen, fourDist]
  have hstep1 : IsBFSTrace fourG fourT 0 fourLen fourDist
      [⟨0, PPath.root⟩, ⟨3, fourQ03⟩] := by
    refine IsBFSTrace.step _ _ IsBFSTrace.root ?_ ?_ ?_
    · exact ⟨⟨0, PPath.root⟩, by simp,
        (0, 3), DiWalk.nil 0, by simp [fourG], by simp [fourT], rfl⟩
    · intro hmem
      rw [List.mem_singleton] at hmem
      have h2 := congrArg (fun x : Σ c, PPath fourG fourT 0 c => x.2.sidetrackList) hmem
      simp [fourQ03, PPath.sidetrackList] at h2
    · intro y _ _
      rw [hw03]
      exact hnonneg y
  refine IsBFSTrace.step _ _ hstep1 ?_ ?_ ?_
  · exact ⟨⟨0, PPath.root⟩, by simp [List.mem_cons],
      (1, 3), DiWalk.cons 0 1 1 (by simp [fourT]) (DiWalk.nil 1),
      by simp [fourG], by simp [fourT], rfl⟩
  · intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h
    · have h2 := congrArg (fun x : Σ c, PPath fourG fourT 0 c => x.2.sidetrackList) h
      simp [fourQ13, PPath.sidetrackList] at h2
    · have h2 := congrArg (fun x : Σ c, PPath fourG fourT 0 c => x.2.sidetrackList) h
      simp [fourQ03, fourQ13, PPath.sidetrackList] at h2
  · intro y _ _
    rw [hw13]
    exact hnonneg y

-- Decode/encode round trip on the concrete direct walk: encoding gives a
-- `PPath` with the same sidetrack list, and decoding it gives a walk
-- with the same sidetracks and length `d(s,t) + weight`.
example : ∃ (x : Σ c, PPath fourG fourT 0 c) (p : DiWalk fourG 0 3),
    x.2.sidetrackList = fourDirectWalk.sidetracks fourT ∧
    p.sidetracks fourT = x.2.sidetrackList ∧
    p.length fourLen = fourDist 0 + x.2.weight fourLen fourDist := by
  obtain ⟨c, q, hq⟩ := lemma5_encode fourT fourDirectWalk
  obtain ⟨p, hp_side, hp_len⟩ := lemma5_decode fourT fourLen fourDist fourTle
    (fun a => (fourTreeWalkExists a).some) (by norm_num [fourDist]) fourTightDelta q
  exact ⟨⟨c, q⟩, p, hq, hp_side, hp_len⟩

-- Without unique tree walks, sidetrack lists do not identify walks: both
-- cyclic-tree routes have empty sidetrack lists.
example : cycleTreeWalk.sidetracks cycleT = [] ∧
    cycleWalk.sidetracks cycleT = [] := by
  have h01 : cycleT.Adj 0 1 := by simp [cycleT]
  have h10 : cycleT.Adj 1 0 := by simp [cycleT]
  have h12 : cycleT.Adj 1 2 := by simp [cycleT]
  refine ⟨?_, ?_⟩
  · simp only [cycleTreeWalk, DiWalk.sidetracks, h01, h12, ite_true]
  · simp only [cycleWalk, DiWalk.sidetracks, h01, h10, h12, ite_true]

-- ... yet the two routes are different walks (distinguished by step count).
example : cycleTreeWalk ≠ cycleWalk := by
  intro h
  have h2 := congrArg walkSteps h
  simp [cycleTreeWalk, cycleWalk, walkSteps] at h2

-- The two cyclic-tree `PPath`s share a sidetrack list ...
example : cycleQA.sidetrackList = cycleQB.sidetrackList := rfl

-- ... but are different `PPath`s (distinguished by their joining
-- tree-walk step counts). This is the collapse that `htree` excludes:
-- without it, the Lemma 5 correspondence is not one-to-one.
example : cycleQA ≠ cycleQB := by
  intro h
  have h2 := congrArg ppathTwSteps h
  simp [cycleQA, cycleQB, ppathTwSteps, walkSteps] at h2

end Cslib.Algorithms.Lean.KShortestPathsEppsteinTests
