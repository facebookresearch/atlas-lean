/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusNetMonotonicity
import Code.FrontierD.FKRectTorusConnected

open SimpleGraph

namespace StatMech.FrontierD

noncomputable section

theorem fkRectCyclicPred_iterate_zero_val {N : Nat} (hN : 0 < N)
    (n : Nat) (hn : n <= N) :
    ((SixVertexArrows.cyclicPred hN)^[n] (⟨0, hN⟩ : Fin N)).val =
      if n = 0 then 0 else N - n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hn' : n <= N := by omega
      simp only [SixVertexArrows.cyclicPred]
      rw [ih hn']
      by_cases hzero : n = 0
      · subst n
        simp only [ite_true, Nat.reduceAdd]
        rw [Nat.mod_eq_of_lt (by omega)]
        simp
      · simp only [hzero, ite_false]
        have hnlt : n < N := by omega
        have heq : N - n + N - 1 = (N - (n + 1)) + N := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        simp

theorem fkRectCyclicPred_val {N : Nat} (hN : 0 < N) (i : Fin N) :
    (SixVertexArrows.cyclicPred hN i).val =
      if i.val = 0 then N - 1 else i.val - 1 := by
  unfold SixVertexArrows.cyclicPred
  by_cases hi : i.val = 0
  · simp only [hi, ite_true, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega)]
  · simp only [hi, ite_false]
    have heq : i.val + N - 1 = (i.val - 1) + N := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private abbrev fkRectFullOpenGraph (R : FKRectTorus) :=
  fkRectOpenGraph R (fkRectConfigurationOfEdges R Finset.univ)

theorem fkRectFullOpenGraph_adj_verticalPred (R : FKRectTorus)
    (x : Fin R.width) (y : Fin R.height) :
    (fkRectFullOpenGraph R).Adj (x, y)
      (x, SixVertexArrows.cyclicPred R.height_pos y) := by
  change (fkRectOpenGraph R
    (fkRectConfigurationOfEdges R Finset.univ)).Adj _ _
  rw [fkRectOpenGraph_configurationOfEdges_univ]
  exact fkRectTorusGraph_adj_verticalPred R x y

theorem fkRectFullOpenGraph_adj_horizontalPred_diag_zero (R : FKRectTorus)
    (x : Fin R.width) :
    (fkRectFullOpenGraph R).Adj
      (x, (⟨0, R.height_pos⟩ : Fin R.height))
      (SixVertexArrows.cyclicPred R.width_pos x,
        SixVertexArrows.cyclicPred R.height_pos
          (⟨0, R.height_pos⟩ : Fin R.height)) := by
  change (fkRectOpenGraph R
    (fkRectConfigurationOfEdges R Finset.univ)).Adj _ _
  rw [fkRectOpenGraph_configurationOfEdges_univ]
  refine ⟨(false, (x, (⟨0, R.height_pos⟩ : Fin R.height))), ?_⟩
  simp [fkRectTorusIndexedEdge]

theorem fkRectHorizontalSeamIncrement_same_fst (R : FKRectTorus)
    (x : Fin R.width) (y z : Fin R.height) :
    fkRectHorizontalSeamIncrement R (x, y) (x, z) = 0 := by
  have hwidth := R.width_gt_two
  unfold fkRectHorizontalSeamIncrement
  change (if x.val + 1 = R.width ∧ x.val = 0 then 1
    else if x.val = 0 ∧ x.val + 1 = R.width then -1 else 0) = 0
  split <;> rename_i h
  · omega
  · split <;> rename_i h'
    · omega
    · rfl

theorem fkRectVerticalSeamIncrement_same_snd (R : FKRectTorus)
    (x z : Fin R.width) (y : Fin R.height) :
    fkRectVerticalSeamIncrement R (x, y) (z, y) = 0 := by
  have hheight := R.height_gt_two
  unfold fkRectVerticalSeamIncrement
  change (if y.val + 1 = R.height ∧ y.val = 0 then 1
    else if y.val = 0 ∧ y.val + 1 = R.height then -1 else 0) = 0
  split <;> rename_i h
  · omega
  · split <;> rename_i h'
    · omega
    · rfl

theorem fkRectHorizontalSeamIncrement_pred (R : FKRectTorus)
    (x : Fin R.width) (y z : Fin R.height) :
    fkRectHorizontalSeamIncrement R (x, y)
      (SixVertexArrows.cyclicPred R.width_pos x, z) =
        if x.val = 0 then -1 else 0 := by
  have hwidth := R.width_gt_two
  have hxlt := x.isLt
  unfold fkRectHorizontalSeamIncrement
  rw [show (SixVertexArrows.cyclicPred R.width_pos x).val =
      if x.val = 0 then R.width - 1 else x.val - 1 from
    fkRectCyclicPred_val R.width_pos x]
  by_cases hx : x.val = 0
  · have hsecond : R.width - 1 + 1 = R.width := by omega
    simp [hx, hsecond]
    omega
  · have hfirst : ¬ (x.val + 1 = R.width ∧ x.val - 1 = 0) := by
      omega
    simp [hx, hfirst]

theorem fkRectVerticalSeamIncrement_pred (R : FKRectTorus)
    (x z : Fin R.width) (y : Fin R.height) :
    fkRectVerticalSeamIncrement R (x, y)
      (z, SixVertexArrows.cyclicPred R.height_pos y) =
        if y.val = 0 then -1 else 0 := by
  have hheight := R.height_gt_two
  have hylt := y.isLt
  unfold fkRectVerticalSeamIncrement
  rw [show (SixVertexArrows.cyclicPred R.height_pos y).val =
      if y.val = 0 then R.height - 1 else y.val - 1 from
    fkRectCyclicPred_val R.height_pos y]
  by_cases hy : y.val = 0
  · have hsecond : R.height - 1 + 1 = R.height := by omega
    simp [hy, hsecond]
    omega
  · have hfirst : ¬ (y.val + 1 = R.height ∧ y.val - 1 = 0) := by
      omega
    simp [hy, hfirst]

theorem fkRectVerticalSeamIncrement_pred_zero (R : FKRectTorus)
    (x z : Fin R.width) :
    fkRectVerticalSeamIncrement R
      (x, (⟨0, R.height_pos⟩ : Fin R.height))
      (z, SixVertexArrows.cyclicPred R.height_pos
        (⟨0, R.height_pos⟩ : Fin R.height)) = -1 := by
  rw [fkRectVerticalSeamIncrement_pred]
  simp

theorem fkRectVerticalSeamIncrement_pred_zero_reverse (R : FKRectTorus)
    (x z : Fin R.width) :
    fkRectVerticalSeamIncrement R
      (z, SixVertexArrows.cyclicPred R.height_pos
        (⟨0, R.height_pos⟩ : Fin R.height))
      (x, (⟨0, R.height_pos⟩ : Fin R.height)) = 1 := by
  rw [fkRectVerticalSeamIncrement_swap,
    fkRectVerticalSeamIncrement_pred_zero]
  norm_num

noncomputable def fkRectVerticalFundamentalWalkAux (R : FKRectTorus)
    (x : Fin R.width) (y : Fin R.height) :
    (n : Nat) -> (fkRectFullOpenGraph R).Walk (x, y)
      (x, (SixVertexArrows.cyclicPred R.height_pos)^[n] y)
  | 0 => .nil
  | n + 1 => (fkRectVerticalFundamentalWalkAux R x y n).concat
      (by simpa only [Function.iterate_succ_apply'] using
        (fkRectFullOpenGraph_adj_verticalPred R x
          ((SixVertexArrows.cyclicPred R.height_pos)^[n] y)))

noncomputable def fkRectHorizontalFundamentalWalkAux (R : FKRectTorus)
    (x : Fin R.width) :
    (n : Nat) -> (fkRectFullOpenGraph R).Walk
      (x, (⟨0, R.height_pos⟩ : Fin R.height))
      ((SixVertexArrows.cyclicPred R.width_pos)^[n] x,
        (⟨0, R.height_pos⟩ : Fin R.height))
  | 0 => .nil
  | n + 1 =>
      ((fkRectHorizontalFundamentalWalkAux R x n).concat
        (fkRectFullOpenGraph_adj_horizontalPred_diag_zero R
          ((SixVertexArrows.cyclicPred R.width_pos)^[n] x))).concat
        (by simpa only [Function.iterate_succ_apply'] using
          (fkRectFullOpenGraph_adj_verticalPred R
            (SixVertexArrows.cyclicPred R.width_pos
              ((SixVertexArrows.cyclicPred R.width_pos)^[n] x))
          (⟨0, R.height_pos⟩ : Fin R.height)).symm)

theorem fkRectWalkWinding_concat (R : FKRectTorus)
    {G : SimpleGraph R.Vertex} {u v w : R.Vertex}
    (p : G.Walk u v) (h : G.Adj v w) :
    fkRectWalkWinding R (p.concat h) =
      ((fkRectWalkWinding R p).1 + fkRectHorizontalSeamIncrement R v w,
        (fkRectWalkWinding R p).2 + fkRectVerticalSeamIncrement R v w) := by
  rw [SimpleGraph.Walk.concat_eq_append, fkRectWalkWinding_append]
  simp [fkRectWalkWinding]

theorem fkRectVerticalFundamentalWalkAux_winding (R : FKRectTorus)
    (x : Fin R.width) (n : Nat) (hn : n <= R.height) :
    fkRectWalkWinding R
      (fkRectVerticalFundamentalWalkAux R x
        (⟨0, R.height_pos⟩ : Fin R.height) n) =
      (0, if n = 0 then 0 else -1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn' : n <= R.height := by omega
      rw [fkRectVerticalFundamentalWalkAux, fkRectWalkWinding_concat, ih hn']
      simp only [Function.iterate_succ_apply']
      rw [fkRectHorizontalSeamIncrement_same_fst, fkRectVerticalSeamIncrement_pred]
      have hval := fkRectCyclicPred_iterate_zero_val R.height_pos n hn'
      rw [hval]
      by_cases hzero : n = 0
      · simp [hzero]
      · have hnlt : n < R.height := by omega
        simp [hzero]
        omega

theorem fkRectHorizontalFundamentalWalkAux_winding (R : FKRectTorus)
    (n : Nat) (hn : n <= R.width) :
    fkRectWalkWinding R
      (fkRectHorizontalFundamentalWalkAux R
        (⟨0, R.width_pos⟩ : Fin R.width) n) =
      (if n = 0 then 0 else -1, 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn' : n <= R.width := by omega
      rw [fkRectHorizontalFundamentalWalkAux, fkRectWalkWinding_concat,
        fkRectWalkWinding_concat, ih hn']
      simp only [Function.iterate_succ_apply']
      rw [fkRectHorizontalSeamIncrement_same_fst,
        fkRectVerticalSeamIncrement_pred_zero_reverse,
        fkRectHorizontalSeamIncrement_pred,
        fkRectVerticalSeamIncrement_pred_zero]
      have hval := fkRectCyclicPred_iterate_zero_val R.width_pos n hn'
      rw [hval]
      by_cases hzero : n = 0
      · simp [hzero]
      · have hnlt : n < R.width := by omega
        simp [hzero]
        omega

theorem fkRectCyclicPred_iterate_zero_card {N : Nat} (hN : 0 < N) :
    (SixVertexArrows.cyclicPred hN)^[N] (⟨0, hN⟩ : Fin N) =
      (⟨0, hN⟩ : Fin N) := by
  apply Fin.ext
  rw [fkRectCyclicPred_iterate_zero_val hN N (le_refl N)]
  simp

private abbrev fkRectOrigin (R : FKRectTorus) : R.Vertex :=
  ((⟨0, R.width_pos⟩ : Fin R.width),
    (⟨0, R.height_pos⟩ : Fin R.height))

noncomputable def fkRectHorizontalFundamentalWalk (R : FKRectTorus) :
    (fkRectFullOpenGraph R).Walk (fkRectOrigin R) (fkRectOrigin R) :=
  (fkRectHorizontalFundamentalWalkAux R
    (⟨0, R.width_pos⟩ : Fin R.width) R.width).copy rfl (by
      unfold fkRectOrigin
      rw [fkRectCyclicPred_iterate_zero_card])

noncomputable def fkRectVerticalFundamentalWalk (R : FKRectTorus) :
    (fkRectFullOpenGraph R).Walk (fkRectOrigin R) (fkRectOrigin R) :=
  (fkRectVerticalFundamentalWalkAux R
    (⟨0, R.width_pos⟩ : Fin R.width)
    (⟨0, R.height_pos⟩ : Fin R.height) R.height).copy rfl (by
      unfold fkRectOrigin
      rw [fkRectCyclicPred_iterate_zero_card])

theorem fkRectWalkWinding_copy (R : FKRectTorus)
    {G : SimpleGraph R.Vertex} {u v u' v' : R.Vertex}
    (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    fkRectWalkWinding R (p.copy hu hv) = fkRectWalkWinding R p := by
  subst u'
  subst v'
  rfl

theorem fkRectHorizontalFundamentalWalk_winding (R : FKRectTorus) :
    fkRectWalkWinding R (fkRectHorizontalFundamentalWalk R) = (-1, 0) := by
  unfold fkRectHorizontalFundamentalWalk
  rw [fkRectWalkWinding_copy]
  rw [fkRectHorizontalFundamentalWalkAux_winding R R.width (le_refl _)]
  simp [ne_of_gt R.width_pos]

theorem fkRectVerticalFundamentalWalk_winding (R : FKRectTorus) :
    fkRectWalkWinding R (fkRectVerticalFundamentalWalk R) = (0, -1) := by
  unfold fkRectVerticalFundamentalWalk
  rw [fkRectWalkWinding_copy]
  rw [fkRectVerticalFundamentalWalkAux_winding R _ R.height (le_refl _)]
  simp [ne_of_gt R.height_pos]

theorem FKRectHasNet_univ (R : FKRectTorus) :
    FKRectHasNet R (fkRectConfigurationOfEdges R Finset.univ) := by
  refine ⟨fkRectOrigin R, fkRectHorizontalFundamentalWalk R,
    fkRectVerticalFundamentalWalk R, ?_⟩
  rw [fkRectHorizontalFundamentalWalk_winding,
    fkRectVerticalFundamentalWalk_winding]
  norm_num [FKRectWindingIndependent]

@[simp] theorem fkRectNetIndicator_univ (R : FKRectTorus) :
    fkRectNetIndicator R (fkRectConfigurationOfEdges R Finset.univ) = 1 :=
  (fkRectNetIndicator_eq_one_iff R _).2 (FKRectHasNet_univ R)

end

end StatMech.FrontierD
