/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectTorusNet
import Code.FrontierD.FKRectTorusNetMonotonicity
import Code.FrontierD.FKRectRandomClusterEventFKG



namespace StatMech.FrontierD

noncomputable section


def fkRectOpenAdjacencyEvent (R : FKRectTorus)
    (x y : R.Vertex) : Set R.Configuration :=
  {omega | (fkRectOpenGraph R omega).Adj x y}

theorem fkRectOpenAdjacencyEvent_isIncreasing
    (R : FKRectTorus) (x y : R.Vertex) :
    IsIncreasing (fkRectOpenAdjacencyEvent R x y) := by
  intro omega tau hot hadj
  exact fkRectOpenGraph_mono R hot hadj



theorem fkRectVerticalCutGraph_mono (R : FKRectTorus)
    {omega tau : R.Configuration} (hot : omega ≤ tau) :
    fkRectVerticalCutGraph R omega ≤ fkRectVerticalCutGraph R tau := by
  intro x y hxy
  unfold fkRectVerticalCutGraph at hxy ⊢
  rw [SimpleGraph.deleteEdges_adj] at hxy ⊢
  exact ⟨fkRectOpenGraph_mono R hot hxy.1, hxy.2⟩

theorem fkRectVerticalCutGraph_le_openGraph (R : FKRectTorus)
    (omega : R.Configuration) :
    fkRectVerticalCutGraph R omega ≤ fkRectOpenGraph R omega := by
  intro x y hxy
  unfold fkRectVerticalCutGraph at hxy
  exact (SimpleGraph.deleteEdges_adj.mp hxy).1



theorem fkRectVerticalSeamIncrement_eq_zero_of_not_crosses
    (R : FKRectTorus) (x y : R.Vertex)
    (hnot : ¬ fkRectCrossesVerticalSeam R s(x, y)) :
    fkRectVerticalSeamIncrement R x y = 0 := by
  unfold fkRectVerticalSeamIncrement
  by_cases hpos : x.2.val + 1 = R.height ∧ y.2.val = 0
  · exact False.elim (hnot (Or.inr ⟨hpos.2, hpos.1⟩))
  by_cases hneg : x.2.val = 0 ∧ y.2.val + 1 = R.height
  · exact False.elim (hnot (Or.inl hneg))
  simp [hpos, hneg]


theorem fkRectVerticalSeamIncrement_ne_zero_of_crosses
    (R : FKRectTorus) (x y : R.Vertex)
    (hcross : fkRectCrossesVerticalSeam R s(x, y)) :
    fkRectVerticalSeamIncrement R x y ≠ 0 := by
  have hheight : R.height ≠ 1 :=
    Nat.ne_of_gt (lt_trans Nat.one_lt_two R.height_gt_two)
  rcases hcross with hcross | hcross
  · change x.2.val = 0 ∧ y.2.val + 1 = R.height at hcross
    have hfirst : ¬ (x.2.val + 1 = R.height ∧ y.2.val = 0) := by
      intro h
      omega
    unfold fkRectVerticalSeamIncrement
    rw [if_neg hfirst, if_pos hcross]
    norm_num
  · change y.2.val = 0 ∧ x.2.val + 1 = R.height at hcross
    have hfirst : x.2.val + 1 = R.height ∧ y.2.val = 0 :=
      ⟨hcross.2, hcross.1⟩
    unfold fkRectVerticalSeamIncrement
    rw [if_pos hfirst]
    norm_num


theorem fkRectVerticalCutWalk_winding_snd_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex} (p : (fkRectVerticalCutGraph R omega).Walk x y) :
    (fkRectWalkWinding R p).2 = 0 := by
  induction p with
  | nil => rfl
  | @cons u v w huv p ih =>
      have hnot : ¬ fkRectCrossesVerticalSeam R s(u, v) := by
        unfold fkRectVerticalCutGraph at huv
        exact (SimpleGraph.deleteEdges_adj.mp huv).2
      simp only [fkRectWalkWinding]
      rw [fkRectVerticalSeamIncrement_eq_zero_of_not_crosses R u v hnot,
        ih, zero_add]



theorem FKRectVerticalWindingWitness.exists_closedWalk_winding_snd_ne_zero
    (R : FKRectTorus) (omega : R.Configuration) (x y : R.Vertex)
    (h : FKRectVerticalWindingWitness R omega x y) :
    ∃ p : (fkRectOpenGraph R omega).Walk x x,
      (fkRectWalkWinding R p).2 ≠ 0 := by
  obtain ⟨p⟩ := h.2.2
  let p' := p.mapLe (fkRectVerticalCutGraph_le_openGraph R omega)
  let c := p'.concat h.1.symm
  refine ⟨c, ?_⟩
  have hpzero := fkRectVerticalCutWalk_winding_snd_eq_zero R omega p
  have hseamSwap : fkRectCrossesVerticalSeam R s(y, x) := by
    simpa only [Sym2.eq_swap] using h.2.1
  have hstep := fkRectVerticalSeamIncrement_ne_zero_of_crosses
    R y x hseamSwap
  rw [show c = p'.concat h.1.symm from rfl,
    SimpleGraph.Walk.concat_eq_append, fkRectWalkWinding_append,
    show fkRectWalkWinding R p' = fkRectWalkWinding R p from
      fkRectWalkWinding_mapLe R
        (fkRectVerticalCutGraph_le_openGraph R omega) p]
  simp only [fkRectWalkWinding]
  rw [hpzero, zero_add, add_zero]
  exact hstep


def fkRectVerticalCutConnectionEvent (R : FKRectTorus)
    (x y : R.Vertex) : Set R.Configuration :=
  {omega | (fkRectVerticalCutGraph R omega).Reachable x y}

theorem fkRectVerticalCutConnectionEvent_isIncreasing
    (R : FKRectTorus) (x y : R.Vertex) :
    IsIncreasing (fkRectVerticalCutConnectionEvent R x y) := by
  intro omega tau hot hreach
  exact hreach.mono (fkRectVerticalCutGraph_mono R hot)


theorem fkRectVerticalCutConnection_inter_subset_connection
    (R : FKRectTorus) (x y z : R.Vertex) :
    fkRectVerticalCutConnectionEvent R x y ∩
        fkRectVerticalCutConnectionEvent R y z ⊆
      fkRectVerticalCutConnectionEvent R x z := by
  rintro omega ⟨hxy, hyz⟩
  exact hxy.trans hyz



theorem fkRectCriticalVerticalCutConnectionMass_mul_le
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (x y z : R.Vertex) :
    fkRectCriticalEventMass R q
          (fkRectVerticalCutConnectionEvent R x y) *
        fkRectCriticalEventMass R q
          (fkRectVerticalCutConnectionEvent R y z) ≤
      fkRectCriticalEventMass R q
        (fkRectVerticalCutConnectionEvent R x z) := by
  calc
    _ ≤ fkRectCriticalEventMass R q
        (fkRectVerticalCutConnectionEvent R x y ∩
          fkRectVerticalCutConnectionEvent R y z) :=
      fkRectCriticalEventMass_mul_le_inter R hq
        (fkRectVerticalCutConnectionEvent_isIncreasing R x y)
        (fkRectVerticalCutConnectionEvent_isIncreasing R y z)
    _ ≤ fkRectCriticalEventMass R q
        (fkRectVerticalCutConnectionEvent R x z) :=
      fkRectCriticalEventMass_mono R (lt_of_lt_of_le zero_lt_one hq)
        (fkRectVerticalCutConnection_inter_subset_connection R x y z)


def fkRectVerticalWindingEvent (R : FKRectTorus) : Set R.Configuration :=
  {omega | ∃ x y : R.Vertex, FKRectVerticalWindingWitness R omega x y}

theorem fkRectVerticalWindingEvent_isIncreasing (R : FKRectTorus) :
    IsIncreasing (fkRectVerticalWindingEvent R) := by
  intro omega tau hot
  rintro ⟨x, y, hadj, hseam, hreach⟩
  exact ⟨x, y, fkRectOpenGraph_mono R hot hadj, hseam,
    hreach.mono (fkRectVerticalCutGraph_mono R hot)⟩



theorem fkRectOpenAdjacency_inter_verticalCutConnection_subset_winding
    (R : FKRectTorus) (x y : R.Vertex)
    (hseam : fkRectCrossesVerticalSeam R s(x, y)) :
    fkRectOpenAdjacencyEvent R x y ∩
        fkRectVerticalCutConnectionEvent R x y ⊆
      fkRectVerticalWindingEvent R := by
  rintro omega ⟨hadj, hreach⟩
  exact ⟨x, y, hadj, hseam, hreach⟩



theorem fkRectCriticalVerticalWindingMass_ge_fixedWitness
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (x y : R.Vertex) (hseam : fkRectCrossesVerticalSeam R s(x, y)) :
    fkRectCriticalEventMass R q (fkRectOpenAdjacencyEvent R x y) *
        fkRectCriticalEventMass R q
          (fkRectVerticalCutConnectionEvent R x y) ≤
      fkRectCriticalEventMass R q (fkRectVerticalWindingEvent R) := by
  calc
    _ ≤ fkRectCriticalEventMass R q
        (fkRectOpenAdjacencyEvent R x y ∩
          fkRectVerticalCutConnectionEvent R x y) :=
      fkRectCriticalEventMass_mul_le_inter R hq
        (fkRectOpenAdjacencyEvent_isIncreasing R x y)
        (fkRectVerticalCutConnectionEvent_isIncreasing R x y)
    _ ≤ fkRectCriticalEventMass R q (fkRectVerticalWindingEvent R) :=
      fkRectCriticalEventMass_mono R (lt_of_lt_of_le zero_lt_one hq)
        (fkRectOpenAdjacency_inter_verticalCutConnection_subset_winding
          R x y hseam)

end

end StatMech.FrontierD
