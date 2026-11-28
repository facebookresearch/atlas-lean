/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.Blob
import Mathlib.Tactic.FinCases

/-!
# Tests for blobs and the tree of blobs

Two parallel edges between two vertices are not cut edges, and the whole graph is one nontrivial
blob with no incident edge. A single edge is a cut edge: deleting it raises the number of
connected components, each end is a trivial blob, the end chosen as root is a `2`-blob and the
other end a `1`-blob, and the two blobs are adjacent in the tree of blobs. The blob of a pendant
vertex has at most one neighbour in the tree of blobs. The centre of an infinite
star has infinitely many incident cut edges and is an `m`-blob for no `m`. Suppressing the middle
vertex of a path on three vertices joins the two ends, while the centre of a star with three leaves
is kept, so no two leaves of the star are joined.
-/

@[expose] public section

open Graph

namespace MathlibExtTest.Combinatorics.GraphBlob

/-! ### Two parallel edges -/

/-- Two vertices joined by two parallel edges. -/
abbrev parallelPair : Graph (Fin 2) (Fin 2) := banana 0 1 Set.univ

theorem parallelPair_isLink (e : Fin 2) : parallelPair.IsLink e 0 1 := by simp

/-- Neither of two parallel edges is a cut edge: the other one still joins their ends. -/
theorem parallelPair_not_isBridge (e : Fin 2) : ¬ parallelPair.IsBridge e := by
  rw [isBridge_iff_not_reachable (parallelPair_isLink e), not_not]
  fin_cases e
  · exact .single ⟨1, by simp⟩
  · exact .single ⟨0, by simp⟩

theorem parallelPair_connected : parallelPair.toSimpleGraph.Connected := by
  have : Nonempty V(parallelPair) := ⟨⟨0, by simp⟩⟩
  refine ⟨fun a b ↦ toSimpleGraph_reachable_iff.2 ?_⟩
  obtain ⟨a, -⟩ := a
  obtain ⟨b, -⟩ := b
  fin_cases a <;> fin_cases b
  · exact .refl
  · exact .single ⟨0, by simp⟩
  · exact .single ⟨0, by simp⟩
  · exact .refl

/-- The two parallel edges form a single blob, the whole graph. -/
theorem parallelPair_isBlob : parallelPair.IsBlob parallelPair :=
  ⟨⟨le_rfl, parallelPair_connected, fun e _ ↦ parallelPair_not_isBridge e⟩, fun _ hK _ ↦ hK.1⟩

/-- This blob has two vertices, so it is not trivial: in a simple graph the edge would be a cut
edge instead. -/
example : ¬ parallelPair.IsTrivialBlob parallelPair := by
  rintro ⟨-, v, hv⟩
  have h0 : (0 : Fin 2) ∈ V(parallelPair) := by simp
  have h1 : (1 : Fin 2) ∈ V(parallelPair) := by simp
  rw [hv] at h0 h1
  exact absurd (h0.trans h1.symm) (by decide)

/-- No edge leaves the whole graph, so it is a `0`-blob. -/
example : parallelPair.IsMBlob 0 parallelPair := by
  refine ⟨parallelPair_isBlob, ?_⟩
  rw [Nat.cast_zero, Set.encard_eq_zero]
  ext e
  simp only [Set.mem_inter_iff, mem_edgeCut_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨u, v, huv, -, hv⟩, -⟩
  exact hv huv.right_mem

/-! ### A single edge -/

/-- Two vertices joined by a single edge. -/
abbrev singleEdge : Graph (Fin 2) (Fin 1) := banana 0 1 Set.univ

/-- A single edge is a cut edge. -/
theorem singleEdge_isBridge : singleEdge.IsBridge 0 := by
  rw [isBridge_iff_not_reachable (u := 0) (v := 1) (by simp)]
  intro h
  rcases Relation.ReflTransGen.cases_head h with h | ⟨z, ⟨f, hf⟩, -⟩
  · exact absurd h (by decide)
  · exact hf.2 (Subsingleton.elim f 0)

/-- Deleting it raises the number of components. -/
example : Nat.card singleEdge.toSimpleGraph.ConnectedComponent <
    Nat.card (singleEdge.deleteEdges {0}).toSimpleGraph.ConnectedComponent :=
  (isBridge_iff_natCard_connectedComponent_lt (by simp)).1 singleEdge_isBridge

theorem singleEdge_isTrivialBlob (v : Fin 2) : singleEdge.IsTrivialBlob (singleEdge.induce {v}) :=
  isTrivialBlob_induce_singleton (by fin_cases v <;> simp) fun e _ _ ↦ by
    obtain rfl := Subsingleton.elim e 0
    exact singleEdge_isBridge

theorem singleEdge_edgeCut (v : Fin 2) :
    singleEdge.edgeCut V(singleEdge.induce {v}) ∩ {e | singleEdge.IsBridge e} = {0} := by
  ext e
  obtain rfl := Subsingleton.elim e 0
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, iff_true]
  refine ⟨?_, singleEdge_isBridge⟩
  fin_cases v
  · exact mem_edgeCut_iff.2 ⟨0, 1, by simp, rfl, by simp⟩
  · exact mem_edgeCut_iff.2 ⟨1, 0, by simp, rfl, by simp⟩

/-- With the vertex `0` as root, the blob of the root has one incident cut edge and counts the root
as a second one, so it is a `2`-blob. -/
example : singleEdge.IsRootedMBlob 0 2 (singleEdge.induce {0}) :=
  ⟨(singleEdge_isTrivialBlob 0).1,
    Or.inr ⟨rfl, by rw [singleEdge_edgeCut, Set.encard_singleton]; rfl⟩⟩

/-- The other end is a `1`-blob. -/
example : singleEdge.IsRootedMBlob 0 1 (singleEdge.induce {1}) :=
  ⟨(singleEdge_isTrivialBlob 1).1,
    Or.inl ⟨by simp, by rw [singleEdge_edgeCut, Set.encard_singleton]; rfl⟩⟩

/-- The two blobs of a single edge are adjacent in the tree of blobs. -/
example : singleEdge.treeOfBlobs.Adj ⟨_, (singleEdge_isTrivialBlob 0).1⟩
    ⟨_, (singleEdge_isTrivialBlob 1).1⟩ := by
  refine ⟨fun h ↦ ?_, 0, 0, 1, by simp, rfl, rfl⟩
  have h' : ({0} : Set (Fin 2)) = {1} :=
    congrArg (fun B : {H // singleEdge.IsBlob H} ↦ V(B.1)) h
  simp at h'

/-- An end of a single edge is pendant: its blob has at most one neighbour in the tree of
blobs. -/
example (B : {H // singleEdge.IsBlob H}) (h : (0 : Fin 2) ∈ V(B.1)) :
    (singleEdge.treeOfBlobs.neighborSet B).Subsingleton :=
  subsingleton_neighborSet_treeOfBlobs B h (fun e f _ _ _ _ ↦ Subsingleton.elim e f)
    (fun _ h ↦ by simp at h)

/-! ### An infinite star -/

/-- The star on `ℕ` with centre `0`: the edge `e` joins `0` and `e + 1`. -/
def infiniteStar : Graph ℕ ℕ where
  vertexSet := Set.univ
  IsLink e x y := x = 0 ∧ y = e + 1 ∨ x = e + 1 ∧ y = 0
  isLink_symm _ _ := ⟨fun _ _ h ↦ (Or.symm h).imp And.symm And.symm⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y v w (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
  left_mem_of_isLink _ _ _ _ := trivial

theorem infiniteStar_isBridge (e : ℕ) : infiniteStar.IsBridge e :=
  isBridge_of_forall_isLink_eq (x := e + 1) (y := 0) (Or.inr ⟨rfl, rfl⟩) (by omega)
    fun f z h ↦ by rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- The centre of the infinite star has infinitely many incident cut edges, so it is an `m`-blob
for no `m`, rooted at the centre or not. -/
example (m : ℕ) : ¬ infiniteStar.IsMBlob m (infiniteStar.induce {0}) ∧
    ¬ infiniteStar.IsRootedMBlob 0 m (infiniteStar.induce {0}) := by
  have huniv : infiniteStar.edgeCut V(infiniteStar.induce {0}) ∩
      {e | infiniteStar.IsBridge e} = Set.univ := by
    refine Set.eq_univ_of_forall fun e ↦ ⟨mem_edgeCut_iff.2 ⟨0, e + 1, Or.inl ⟨rfl, rfl⟩, rfl,
      fun h ↦ by simp at h⟩, infiniteStar_isBridge e⟩
  have htop : (infiniteStar.edgeCut V(infiniteStar.induce {0}) ∩
      {e | infiniteStar.IsBridge e}).encard = ⊤ := by
    rw [huniv, Set.encard_eq_top_iff]
    exact Set.infinite_univ
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h.2] at htop
    exact ENat.natCast_ne_top m htop
  · rcases h.2 with ⟨h0, -⟩ | ⟨-, h⟩
    · exact h0 rfl
    · rw [htop, top_add] at h
      exact ENat.natCast_ne_top m h.symm

/-! ### Suppressing vertices of degree two -/

/-- The path `0 - 1 - 2`. -/
def path3 : SimpleGraph (Fin 3) := SimpleGraph.fromRel fun i j ↦ i.val + 1 = j.val

theorem path3_neighborSet_one : path3.neighborSet 1 = {0, 2} := by
  ext v
  fin_cases v <;> simp [path3]

theorem path3_neighborSet_zero : path3.neighborSet 0 = {1} := by
  ext v
  fin_cases v <;> simp [path3]

theorem path3_neighborSet_two : path3.neighborSet 2 = {1} := by
  ext v
  fin_cases v <;> simp [path3]

/-- The ends of the path have degree one and are kept. -/
abbrev path3End (i : Fin 3) (hi : i ≠ 1) : {v // (path3.neighborSet v).ncard ≠ 2} :=
  ⟨i, by fin_cases i <;> simp_all [path3_neighborSet_zero, path3_neighborSet_two]⟩

/-- Suppressing the middle vertex, of degree two, joins the two ends. -/
example : path3.suppressDegreeTwo.Adj (path3End 0 (by decide)) (path3End 2 (by decide)) := by
  have h01 : path3.Adj 0 1 := by simp [path3]
  have h12 : path3.Adj 1 2 := by simp [path3]
  have hp : (SimpleGraph.Walk.cons h01 (.cons h12 .nil)).IsPath := by
    simp only [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil]
    refine ⟨⟨SimpleGraph.Walk.IsPath.nil, ?_⟩, ?_⟩ <;> decide
  refine ⟨fun h ↦ absurd (congrArg Subtype.val h) (by decide),
    .cons h01 (.cons h12 .nil), hp, ?_⟩
  intro w hw h0 h2
  have hw' : w = 0 ∨ w = 1 ∨ w = 2 := by simpa using hw
  rcases hw' with rfl | rfl | rfl
  · exact absurd rfl h0
  · rw [path3_neighborSet_one, Set.ncard_pair (by decide)]
  · exact absurd rfl h2

/-- The star with centre `0` and leaves `1`, `2`, `3`. -/
def star3 : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun i j ↦ i = 0 ∧ j ≠ 0

theorem star3_neighborSet_zero : star3.neighborSet 0 = {1, 2, 3} := by
  ext v
  fin_cases v <;> simp [star3]

theorem star3_neighborSet_ne {i : Fin 4} (hi : i ≠ 0) : star3.neighborSet i = {0} := by
  ext v
  fin_cases i <;> fin_cases v <;> simp_all [star3]

theorem star3_ncard_ne {i : Fin 4} (hi : i ≠ 0) : (star3.neighborSet i).ncard ≠ 2 := by
  rw [star3_neighborSet_ne hi, Set.ncard_singleton]
  decide

/-- The centre of the star has degree three and is kept. -/
example : (star3.neighborSet 0).ncard ≠ 2 := by
  rw [star3_neighborSet_zero, Set.ncard_insert_of_notMem (by decide),
    Set.ncard_pair (by decide)]
  decide

/-- No two leaves of the star are joined once its vertices of degree two are suppressed: every path
between them passes through the centre, which is kept. -/
example {i j : Fin 4} (hi : i ≠ 0) (hj : j ≠ 0) :
    ¬ star3.suppressDegreeTwo.Adj ⟨i, star3_ncard_ne hi⟩ ⟨j, star3_ncard_ne hj⟩ := by
  rintro ⟨hne, p, -, hdeg⟩
  cases p with
  | nil => exact hne rfl
  | @cons _ z _ h q =>
    have hz : z = 0 := by
      have : z ∈ star3.neighborSet i := h
      rw [star3_neighborSet_ne hi] at this
      exact this
    subst hz
    have h0 := hdeg 0 (by simp) (Ne.symm hi) (Ne.symm hj)
    rw [star3_neighborSet_zero, Set.ncard_insert_of_notMem (by decide),
      Set.ncard_pair (by decide)] at h0
    exact absurd h0 (by decide)

end MathlibExtTest.Combinatorics.GraphBlob
