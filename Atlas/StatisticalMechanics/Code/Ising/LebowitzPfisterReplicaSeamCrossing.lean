/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaCurrentGraph
import Code.Sharpness.SimonLieb









open Finset SimpleGraph

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]


def lpReplicaCurrentLeftEmbedding : V ↪ LPReplicaCurrentVertex V where
  toFun x := .inl (.inl x)
  inj' := fun _ _ h => Sum.inl.inj (Sum.inl.inj h)


def lpReplicaCurrentLeftSide : Finset (LPReplicaCurrentVertex V) :=
  insert lpReplicaCurrentGhost0
    (Finset.univ.map lpReplicaCurrentLeftEmbedding)

@[simp] theorem lpReplicaCurrentLeft_mem_leftSide (x : V) :
    (.inl (.inl x) : LPReplicaCurrentVertex V) ∈
      lpReplicaCurrentLeftSide := by
  simp [lpReplicaCurrentLeftSide, lpReplicaCurrentLeftEmbedding,
    lpReplicaCurrentGhost0]

@[simp] theorem lpReplicaCurrentRight_not_mem_leftSide (x : V) :
    (.inl (.inr x) : LPReplicaCurrentVertex V) ∉
      lpReplicaCurrentLeftSide := by
  simp [lpReplicaCurrentLeftSide, lpReplicaCurrentLeftEmbedding,
    lpReplicaCurrentGhost0]

@[simp] theorem lpReplicaCurrentGhost0_mem_leftSide :
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈
      lpReplicaCurrentLeftSide := by
  simp [lpReplicaCurrentLeftSide, lpReplicaCurrentGhost0]

@[simp] theorem lpReplicaCurrentGhost1_not_mem_leftSide :
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
      lpReplicaCurrentLeftSide := by
  simp [lpReplicaCurrentLeftSide, lpReplicaCurrentLeftEmbedding,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]

theorem lpReplicaCurrent_mem_leftSide_iff
    (z : LPReplicaCurrentVertex V) :
    z ∈ lpReplicaCurrentLeftSide ↔
      (∃ x : V, z = .inl (.inl x)) ∨
        z = lpReplicaCurrentGhost0 := by
  rcases z with (z | b)
  · rcases z with z | z <;>
      simp [lpReplicaCurrentLeftSide, lpReplicaCurrentLeftEmbedding,
        lpReplicaCurrentGhost0]
  · cases b <;>
      simp [lpReplicaCurrentLeftSide, lpReplicaCurrentLeftEmbedding,
        lpReplicaCurrentGhost0]

theorem lpReplicaCurrent_not_mem_leftSide_iff
    (z : LPReplicaCurrentVertex V) :
    z ∉ lpReplicaCurrentLeftSide ↔
      (∃ x : V, z = .inl (.inr x)) ∨
        z = lpReplicaCurrentGhost1 := by
  rcases z with (z | b)
  · rcases z with z | z <;>
      simp [lpReplicaCurrentLeftSide, lpReplicaCurrentLeftEmbedding,
        lpReplicaCurrentGhost1, lpReplicaCurrentGhost0]
  · cases b <;>
      simp [lpReplicaCurrentLeftSide, lpReplicaCurrentLeftEmbedding,
        lpReplicaCurrentGhost1, lpReplicaCurrentGhost0]



theorem lpReplicaCurrent_crossingEdge_eq_seam
    (G : SimpleGraph V) (sites : I -> V)
    {x y : LPReplicaCurrentVertex V}
    (hx : x ∈ lpReplicaCurrentLeftSide)
    (hy : y ∉ lpReplicaCurrentLeftSide)
    (hxy : (lpReplicaCurrentGraph G sites).Adj x y) :
    ∃ i : I, s(x, y) = lpReplicaCurrentSeamEdge sites i := by
  rcases (lpReplicaCurrent_mem_leftSide_iff x).mp hx with
      ⟨u, rfl⟩ | rfl
  · rcases (lpReplicaCurrent_not_mem_leftSide_iff y).mp hy with
        ⟨v, rfl⟩ | rfl
    · rw [lpReplicaCurrentGraph_adj_left_right_iff] at hxy
      obtain ⟨i, hiu, hiv⟩ := hxy
      subst u
      subst v
      exact ⟨i, rfl⟩
    · unfold lpReplicaCurrentGhost1 at hxy
      unfold lpReplicaCurrentGraph at hxy
      rw [SimpleGraph.fromRel_adj] at hxy
      simp [lpReplicaCurrentRel] at hxy
  · rcases (lpReplicaCurrent_not_mem_leftSide_iff y).mp hy with
        ⟨v, rfl⟩ | rfl
    · unfold lpReplicaCurrentGhost0 at hxy
      unfold lpReplicaCurrentGraph at hxy
      rw [SimpleGraph.fromRel_adj] at hxy
      simp [lpReplicaCurrentRel] at hxy
    · unfold lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 at hxy
      unfold lpReplicaCurrentGraph at hxy
      rw [SimpleGraph.fromRel_adj] at hxy
      simp [lpReplicaCurrentRel] at hxy



theorem lpReplicaCurrentWalk_firstSeam
    (G : SimpleGraph V) (sites : I -> V)
    {x y : LPReplicaCurrentVertex V}
    (w : (lpReplicaCurrentGraph G sites).Walk x y)
    (hx : x ∈ lpReplicaCurrentLeftSide)
    (hy : y ∉ lpReplicaCurrentLeftSide) :
    ∃ k i, 1 ≤ k ∧ k ≤ w.length ∧
      w.getVert k ∉ lpReplicaCurrentLeftSide ∧
      w.getVert (k - 1) ∈ lpReplicaCurrentLeftSide ∧
      s(w.getVert (k - 1), w.getVert k) =
        lpReplicaCurrentSeamEdge sites i ∧
      (∀ j < k, w.getVert j ∈ lpReplicaCurrentLeftSide) := by
  classical
  obtain ⟨k, hk1, hkle, hkout, hkin, hkadj, hprefix⟩ :=
    walk_firstExit w lpReplicaCurrentLeftSide hx hy
  obtain ⟨i, hi⟩ := lpReplicaCurrent_crossingEdge_eq_seam
    G sites hkin hkout hkadj
  exact ⟨k, i, hk1, hkle, hkout, hkin, hi, hprefix⟩



theorem lpReplicaCurrentGhostWalk_firstSeam
    (G : SimpleGraph V) (sites : I -> V)
    (w : (lpReplicaCurrentGraph G sites).Walk
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    ∃ k i, 1 ≤ k ∧ k ≤ w.length ∧
      w.getVert k ∉ lpReplicaCurrentLeftSide ∧
      w.getVert (k - 1) ∈ lpReplicaCurrentLeftSide ∧
      s(w.getVert (k - 1), w.getVert k) =
        lpReplicaCurrentSeamEdge sites i ∧
      (∀ j < k, w.getVert j ∈ lpReplicaCurrentLeftSide) := by
  exact lpReplicaCurrentWalk_firstSeam G sites w
    lpReplicaCurrentGhost0_mem_leftSide
    lpReplicaCurrentGhost1_not_mem_leftSide

end

end StatMech.Ising
