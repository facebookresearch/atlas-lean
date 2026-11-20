/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.BeffaraDC.TorusSquareCrossing

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Onsager


noncomputable def torusSquareShiftCounterexampleConfig
    (L : ℕ) [Fact (2 < L)] : TorusAmbientConfig L :=
  fun e => decide (e = torusHorizontalEdge L 0 0)

theorem torusSquareShiftCounterexample_horizontal
    (L : ℕ) [Fact (2 < L)] :
    torusSquareHorizontalCrossing L 1
      (torusSquareShiftCounterexampleConfig L) := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  let x : ZMod L × ZMod L := (0, 0)
  let y : ZMod L × ZMod L := (1, 0)
  have hx : x ∈ torusSquareVertexSet L 1 := by
    simp [x, torusSquareVertexSet]
  have hy : y ∈ torusSquareVertexSet L 1 := by
    simp [y, torusSquareVertexSet, ZMod.val_one L]
  refine ⟨x, y, hx, hy, by simp [x],
    by simp [y, ZMod.val_one L], ?_⟩
  have hadj : (onsTorusGraph L).Adj x y := by
    change onsTorusAdj L (0, 0) (1, 0)
    exact Or.inr ⟨rfl, Or.inr (by ring)⟩
  apply SimpleGraph.Adj.reachable
  rw [SimpleGraph.induce_adj, FK.openSub_adj]
  refine ⟨hadj, ?_⟩
  have hedge : s(x, y) ∈ (onsTorusGraph L).edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset] using hadj
  rw [torusAmbientConfigExtend, dif_pos hedge]
  change torusSquareShiftCounterexampleConfig L ⟨s(x, y), hedge⟩ = true
  simp only [torusSquareShiftCounterexampleConfig, decide_eq_true_eq]
  apply Subtype.ext
  simp [x, y, torusHorizontalEdge_val]

theorem torusSquareShiftCounterexample_dual_vertical
    (L : ℕ) [Fact (2 < L)] :
    torusCellDualAmbientConfig L (torusSquareShiftCounterexampleConfig L) ∈
      torusSquareVerticalCrossingEvent L 1 := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  rw [mem_torusSquareVerticalCrossingEvent]
  let x : ZMod L × ZMod L := (0, 0)
  let y : ZMod L × ZMod L := (1, 0)
  have hx : x ∈ torusSquareVertexSet L 1 := by
    simp [x, torusSquareVertexSet]
  have hy : y ∈ torusSquareVertexSet L 1 := by
    simp [y, torusSquareVertexSet, ZMod.val_one L]
  refine ⟨x, y, hx, hy, by simp [x],
    by simp [y, ZMod.val_one L], ?_⟩
  have hadj : (onsTorusGraph L).Adj x y := by
    change onsTorusAdj L (0, 0) (1, 0)
    exact Or.inr ⟨rfl, Or.inr (by ring)⟩
  apply SimpleGraph.Adj.reachable
  rw [SimpleGraph.induce_adj, FK.openSub_adj]
  refine ⟨hadj, ?_⟩
  have hedge : s(x, y) ∈ (onsTorusGraph L).edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset] using hadj
  rw [torusAmbientConfigExtend, dif_pos hedge]
  change torusAmbientSwapConfig L
      (torusCellDualAmbientConfig L (torusSquareShiftCounterexampleConfig L))
      ⟨s(x, y), hedge⟩ = true
  unfold torusAmbientSwapConfig
  have hswap : (torusAmbientSwapEdgeEquiv L).symm ⟨s(x, y), hedge⟩ =
      torusVerticalEdge L 0 0 := by
    apply Subtype.ext
    simp [torusAmbientSwapEdgeEquiv, x, y, torusVerticalEdge_val]
  rw [hswap]
  simp only [torusCellDualAmbientConfig, torusCellCrossing_symm_vertical,
    Bool.not_eq_true']
  simp only [zero_add]
  change torusSquareShiftCounterexampleConfig L
      (torusHorizontalEdge L 0 1) = false
  simp only [torusSquareShiftCounterexampleConfig, decide_eq_false_iff_not]
  intro heq
  change torusEdgeOfCode L ((0, 1), .horizontal) =
    torusEdgeOfCode L ((0, 0), .horizontal) at heq
  have hcode := torusEdgeOfCode_injective L heq
  simp at hcode





theorem torus_concreteSquareCrossing_duality_iff_false
    (L : ℕ) [Fact (2 < L)] :
    ¬ ∀ omega : TorusAmbientConfig L,
      ¬ torusSquareHorizontalCrossing L 1 omega ↔
        torusCellDualAmbientConfig L omega ∈
          torusSquareVerticalCrossingEvent L 1 := by
  intro h
  exact ((h (torusSquareShiftCounterexampleConfig L)).mpr
    (torusSquareShiftCounterexample_dual_vertical L))
      (torusSquareShiftCounterexample_horizontal L)




theorem torus_squareCrossing_ge_one_div_one_add_q_of_cover
    (L : ℕ) [Fact (2 < L)] (horizontal : Finset (TorusAmbientConfig L))
    {q : ℝ} (hq1 : 1 ≤ q)
    (hdualCrossing : ∀ omega : TorusAmbientConfig L,
      omega ∉ horizontal →
        torusCellDualAmbientConfig L omega ∈
          torusAmbientRotatedEvent L horizontal) :
    1 / (1 + q) ≤
      torusAmbientEventProbability L (selfDualPoint q) q horizontal := by
  let vertical := torusAmbientRotatedEvent L horizontal
  let dualVertical := torusAmbientDualPullbackEvent L vertical
  have hcover : 1 ≤
      torusAmbientEventProbability L (selfDualPoint q) q horizontal +
        torusAmbientEventProbability L (selfDualPoint q) q dualVertical := by
    have hq : 0 < q := lt_of_lt_of_le one_pos hq1
    obtain ⟨hp, hp1⟩ := selfDualPoint_mem_Ioo hq
    have hprob (omega : TorusAmbientConfig L) :
        0 ≤ torusAmbientProbability L (selfDualPoint q) q omega := by
      unfold torusAmbientProbability
      exact (div_pos (torusAmbientFKWeight_pos L omega hp hp1 hq)
        (torusAmbientPartition_pos L hp hp1 hq)).le
    rw [← torusAmbientProbability_sum_one L hp hp1 hq]
    unfold torusAmbientEventProbability
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro omega _
    by_cases hh : omega ∈ horizontal
    · by_cases hd : omega ∈ dualVertical <;>
        simp [hh, hd, hprob omega]
    · have hd : omega ∈ dualVertical := by
        simpa [dualVertical, vertical] using hdualCrossing omega hh
      simp [hh, hd]
  have hdualLe :
      torusAmbientEventProbability L (selfDualPoint q) q dualVertical ≤
        q * torusAmbientEventProbability L (selfDualPoint q) q horizontal := by
    calc
      torusAmbientEventProbability L (selfDualPoint q) q dualVertical ≤
          q * torusAmbientEventProbability L (selfDualPoint q) q vertical :=
        torusAmbientDualPullbackEventProbability_le L vertical hq1
      _ = q * torusAmbientEventProbability L (selfDualPoint q) q horizontal := by
        rw [torusAmbientEventProbability_rotated]
  have hden : 0 < 1 + q := by linarith
  rw [div_le_iff₀ hden]
  nlinarith



theorem torus_concreteSquareCrossing_ge_one_div_one_add_q_of_cover
    (L : ℕ) [Fact (2 < L)] (n : ℕ) (_hn : 1 ≤ n) (_hnL : n < L)
    {q : ℝ} (hq1 : 1 ≤ q)
    (hdualCrossing : ∀ omega : TorusAmbientConfig L,
      ¬ torusSquareHorizontalCrossing L n omega →
        torusCellDualAmbientConfig L omega ∈
          torusSquareVerticalCrossingEvent L n) :
    1 / (1 + q) ≤
      torusAmbientEventProbability L (selfDualPoint q) q
        (torusSquareHorizontalCrossingEvent L n) := by
  apply torus_squareCrossing_ge_one_div_one_add_q_of_cover L
    (torusSquareHorizontalCrossingEvent L n) hq1
  intro omega hno
  have hno' : ¬ torusSquareHorizontalCrossing L n omega := by
    simpa only [mem_torusSquareHorizontalCrossingEvent] using hno
  simpa only [torusSquareVerticalCrossingEvent] using
    hdualCrossing omega hno'

end StatMech.BeffaraDC
