/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusNet
import Code.FrontierD.FKRectTorusEdgeFinset

open SimpleGraph

namespace StatMech.FrontierD

noncomputable section


theorem fkRectWalkWinding_append (R : FKRectTorus)
    {G : SimpleGraph R.Vertex} {x y z : R.Vertex}
    (p : G.Walk x y) (q : G.Walk y z) :
    fkRectWalkWinding R (p.append q) =
      ((fkRectWalkWinding R p).1 + (fkRectWalkWinding R q).1,
        (fkRectWalkWinding R p).2 + (fkRectWalkWinding R q).2) := by
  induction p with
  | nil => simp [fkRectWalkWinding]
  | @cons u v w huv p ih =>
      simp only [Walk.cons_append, fkRectWalkWinding]
      rw [ih]
      ext <;> simp only [Prod.fst, Prod.snd] <;> ring


theorem fkRectHorizontalSeamIncrement_swap (R : FKRectTorus)
    (x y : R.Vertex) :
    fkRectHorizontalSeamIncrement R y x =
      -fkRectHorizontalSeamIncrement R x y := by
  have hwidth : R.width ≠ 1 :=
    Nat.ne_of_gt (lt_trans Nat.one_lt_two R.width_gt_two)
  have hwidth' : 1 ≠ R.width := hwidth.symm
  unfold fkRectHorizontalSeamIncrement
  by_cases hA : x.1.val + 1 = R.width ∧ y.1.val = 0
  · have hB : ¬ (x.1.val = 0 ∧ y.1.val + 1 = R.width) := by
      intro hB
      omega
    have hAr : y.1.val = 0 ∧ x.1.val + 1 = R.width := ⟨hA.2, hA.1⟩
    have hBr : ¬ (y.1.val + 1 = R.width ∧ x.1.val = 0) := by
      simpa only [and_comm] using hB
    simp [hA, hB, hAr, hBr, hwidth, hwidth']
  · by_cases hB : x.1.val = 0 ∧ y.1.val + 1 = R.width
    · have hAr : ¬ (y.1.val = 0 ∧ x.1.val + 1 = R.width) := by
        simpa only [and_comm] using hA
      have hBr : y.1.val + 1 = R.width ∧ x.1.val = 0 := ⟨hB.2, hB.1⟩
      simp [hA, hB, hAr, hBr, hwidth, hwidth']
    · have hAr : ¬ (y.1.val = 0 ∧ x.1.val + 1 = R.width) := by
        simpa only [and_comm] using hA
      have hBr : ¬ (y.1.val + 1 = R.width ∧ x.1.val = 0) := by
        simpa only [and_comm] using hB
      simp [hA, hB, hAr, hBr, hwidth, hwidth']


theorem fkRectVerticalSeamIncrement_swap (R : FKRectTorus)
    (x y : R.Vertex) :
    fkRectVerticalSeamIncrement R y x =
      -fkRectVerticalSeamIncrement R x y := by
  have hheight : R.height ≠ 1 :=
    Nat.ne_of_gt (lt_trans Nat.one_lt_two R.height_gt_two)
  have hheight' : 1 ≠ R.height := hheight.symm
  unfold fkRectVerticalSeamIncrement
  by_cases hA : x.2.val + 1 = R.height ∧ y.2.val = 0
  · have hB : ¬ (x.2.val = 0 ∧ y.2.val + 1 = R.height) := by
      intro hB
      omega
    have hAr : y.2.val = 0 ∧ x.2.val + 1 = R.height := ⟨hA.2, hA.1⟩
    have hBr : ¬ (y.2.val + 1 = R.height ∧ x.2.val = 0) := by
      simpa only [and_comm] using hB
    simp [hA, hB, hAr, hBr, hheight, hheight']
  · by_cases hB : x.2.val = 0 ∧ y.2.val + 1 = R.height
    · have hAr : ¬ (y.2.val = 0 ∧ x.2.val + 1 = R.height) := by
        simpa only [and_comm] using hA
      have hBr : y.2.val + 1 = R.height ∧ x.2.val = 0 := ⟨hB.2, hB.1⟩
      simp [hA, hB, hAr, hBr, hheight, hheight']
    · have hAr : ¬ (y.2.val = 0 ∧ x.2.val + 1 = R.height) := by
        simpa only [and_comm] using hA
      have hBr : ¬ (y.2.val + 1 = R.height ∧ x.2.val = 0) := by
        simpa only [and_comm] using hB
      simp [hA, hB, hAr, hBr, hheight, hheight']


theorem fkRectWalkWinding_reverse (R : FKRectTorus)
    {G : SimpleGraph R.Vertex} {x y : R.Vertex} (p : G.Walk x y) :
    fkRectWalkWinding R p.reverse =
      (-(fkRectWalkWinding R p).1, -(fkRectWalkWinding R p).2) := by
  induction p with
  | nil => rfl
  | @cons u v w huv p ih =>
      rw [Walk.reverse_cons, fkRectWalkWinding_append, ih]
      simp only [fkRectWalkWinding, neg_add_rev]
      rw [fkRectHorizontalSeamIncrement_swap,
        fkRectVerticalSeamIncrement_swap]
      apply Prod.ext
      · simp only [Prod.fst]
        ring
      · simp only [Prod.snd]
        ring



theorem fkRectWalkWinding_conjugate (R : FKRectTorus)
    {G : SimpleGraph R.Vertex} {x y : R.Vertex}
    (r : G.Walk x y) (p : G.Walk y y) :
    fkRectWalkWinding R ((r.append p).append r.reverse) =
      fkRectWalkWinding R p := by
  rw [fkRectWalkWinding_append, fkRectWalkWinding_append,
    fkRectWalkWinding_reverse]
  apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> ring



theorem FKRectHasNet.of_connected_closedWalks (R : FKRectTorus)
    (omega : R.Configuration) {x y : R.Vertex}
    (hxy : (fkRectOpenGraph R omega).Reachable x y)
    (p : (fkRectOpenGraph R omega).Walk x x)
    (q : (fkRectOpenGraph R omega).Walk y y)
    (hind : FKRectWindingIndependent
      (fkRectWalkWinding R p) (fkRectWalkWinding R q)) :
    FKRectHasNet R omega := by
  obtain ⟨r⟩ := hxy
  refine ⟨x, p, (r.append q).append r.reverse, ?_⟩
  rwa [fkRectWalkWinding_conjugate]



theorem fkRectWalkWinding_mapLe (R : FKRectTorus)
    {G H : SimpleGraph R.Vertex} (hGH : G ≤ H)
    {x y : R.Vertex} (p : G.Walk x y) :
    fkRectWalkWinding R (p.mapLe hGH) = fkRectWalkWinding R p := by
  induction p with
  | nil => rfl
  | @cons u v w huv p ih =>
      simp only [Walk.map_cons, fkRectWalkWinding]
      change
        (fkRectHorizontalSeamIncrement R u v +
            (fkRectWalkWinding R (p.mapLe hGH)).1,
          fkRectVerticalSeamIncrement R u v +
            (fkRectWalkWinding R (p.mapLe hGH)).2) = _
      rw [ih]



theorem fkRectOpenGraph_mono (R : FKRectTorus)
    {omega tau : R.Configuration}
    (hopen : ∀ e, omega e = true → tau e = true) :
    fkRectOpenGraph R omega ≤ fkRectOpenGraph R tau := by
  intro x y hxy
  obtain ⟨e, he, hedge⟩ := hxy
  exact ⟨e, hopen e he, hedge⟩


theorem FKRectHasNet.mono (R : FKRectTorus)
    {omega tau : R.Configuration}
    (hopen : ∀ e, omega e = true → tau e = true)
    (hnet : FKRectHasNet R omega) :
    FKRectHasNet R tau := by
  obtain ⟨x, p, q, hpq⟩ := hnet
  let hG : fkRectOpenGraph R omega ≤ fkRectOpenGraph R tau :=
    fkRectOpenGraph_mono R hopen
  refine ⟨x, p.mapLe hG, q.mapLe hG, ?_⟩
  simpa only [fkRectWalkWinding_mapLe] using hpq


theorem fkRectNetIndicator_mono (R : FKRectTorus)
    {omega tau : R.Configuration}
    (hopen : ∀ e, omega e = true → tau e = true) :
    fkRectNetIndicator R omega ≤ fkRectNetIndicator R tau := by
  by_cases hnet : FKRectHasNet R omega
  · have hnet' := hnet.mono R hopen
    rw [(fkRectNetIndicator_eq_one_iff R omega).2 hnet,
      (fkRectNetIndicator_eq_one_iff R tau).2 hnet']
  · rw [(fkRectNetIndicator_eq_zero_iff R omega).2 hnet]
    exact Nat.zero_le _


theorem FKRectHasNet.mono_configurationOfEdges (R : FKRectTorus)
    {F A : Finset R.EdgeIndex} (hFA : F ⊆ A)
    (hnet : FKRectHasNet R (fkRectConfigurationOfEdges R F)) :
    FKRectHasNet R (fkRectConfigurationOfEdges R A) := by
  apply hnet.mono R
  intro e he
  rw [fkRectConfigurationOfEdges_apply] at he ⊢
  exact hFA he


theorem FKRectHasNet.insert (R : FKRectTorus)
    (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (hnet : FKRectHasNet R (fkRectConfigurationOfEdges R F)) :
    FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)) :=
  hnet.mono_configurationOfEdges R (Finset.subset_insert e F)


theorem fkRectWalkWinding_empty (R : FKRectTorus) {x y : R.Vertex}
    (p : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R ∅)).Walk x y) :
    fkRectWalkWinding R p = (0, 0) := by
  cases p with
  | nil => rfl
  | @cons u v w huv p =>
      simp [fkRectOpenGraph, fkRectConfigurationOfEdges] at huv


theorem not_FKRectHasNet_empty (R : FKRectTorus) :
    ¬ FKRectHasNet R (fkRectConfigurationOfEdges R ∅) := by
  rintro ⟨x, p, q, hpq⟩
  rw [fkRectWalkWinding_empty R p, fkRectWalkWinding_empty R q] at hpq
  exact hpq rfl

@[simp] theorem fkRectNetIndicator_empty (R : FKRectTorus) :
    fkRectNetIndicator R (fkRectConfigurationOfEdges R ∅) = 0 :=
  (fkRectNetIndicator_eq_zero_iff R _).2 (not_FKRectHasNet_empty R)

end

end StatMech.FrontierD
