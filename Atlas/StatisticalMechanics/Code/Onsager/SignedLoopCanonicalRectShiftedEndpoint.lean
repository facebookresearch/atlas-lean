/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopCanonicalRectEndpoint
import Code.FrontierB.BoxGraphPath










open MeasureTheory Filter Topology

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Sharpness StatMech.FrontierB

noncomputable section


def ons_originPositiveBoxVertex (n : Nat) : sctBox 2 (n + 1) :=
  ⟨![0, 0], by
    intro i
    fin_cases i <;> simp⟩


def ons_neighborPositiveBoxVertex (n : Nat) : sctBox 2 (n + 1) :=
  ⟨![1, 0], by
    intro i
    fin_cases i <;> simp⟩

theorem ons_originPositiveBoxVertex_ne_neighbor (n : Nat) :
    ons_originPositiveBoxVertex n ≠ ons_neighborPositiveBoxVertex n := by
  intro h
  have h0 := congrFun (congrArg Subtype.val h) 0
  simp [ons_originPositiveBoxVertex, ons_neighborPositiveBoxVertex] at h0

theorem ons_originPositiveBoxVertex_adj_neighbor (n : Nat) :
    (sctBoxGraph 2 (n + 1)).Adj
      (ons_originPositiveBoxVertex n) (ons_neighborPositiveBoxVertex n) := by
  change (hypercubicLattice 2).Adj (![0, 0] : Site 2) ![1, 0]
  simp [hypercubicLattice_adj, Fin.sum_univ_two]


def ons_box2GraphIsoRect (n : Nat) :
    sctBoxGraph 2 n ≃g ons_rectDualGraph (2 * n) (2 * n) where
  toEquiv := ons_box2EquivRect n
  map_rel_iff' := by
    intro x y
    exact (ons_box2EquivRect_adj n x y).symm



def ons_rectDualPathOfBoxVertices (n : Nat) (x y : sctBox 2 n) (hxy : x ≠ y) :
    ons_RectDualPath (2 * n) (2 * n) where
  source := ons_box2GraphIsoRect n x
  target := ons_box2GraphIsoRect n y
  source_ne_target := fun h => hxy ((ons_box2GraphIsoRect n).injective h)
  walk := (StatMech.FrontierB.boxGraphPath 2 n x y).map
    (ons_box2GraphIsoRect n).toHom
  isPath := SimpleGraph.Walk.map_isPath_of_injective
    (f := (ons_box2GraphIsoRect n).toHom)
    (p := StatMech.FrontierB.boxGraphPath 2 n x y)
    (ons_box2GraphIsoRect n).injective
    (StatMech.FrontierB.boxGraphPath_isPath 2 n x y)



def ons_originNeighborRectDualPath (n : Nat) :
    ons_RectDualPath (2 * (n + 1)) (2 * (n + 1)) where
  source := ons_box2EquivRect (n + 1) (ons_originPositiveBoxVertex n)
  target := ons_box2EquivRect (n + 1) (ons_neighborPositiveBoxVertex n)
  source_ne_target := fun h =>
    ons_originPositiveBoxVertex_ne_neighbor n
      ((ons_box2EquivRect (n + 1)).injective h)
  walk := .cons
    ((ons_box2EquivRect_adj (n + 1) _ _).mp
      (ons_originPositiveBoxVertex_adj_neighbor n)) .nil
  isPath := by
    simp [ons_originPositiveBoxVertex_ne_neighbor]

@[simp] theorem ons_originNeighborRectDualPath_source_pullback (n : Nat) :
    ((ons_box2EquivRect (n + 1)).symm
      (ons_originNeighborRectDualPath n).source).1 = (![0, 0] : Site 2) := by
  simp [ons_originNeighborRectDualPath, ons_originPositiveBoxVertex]

@[simp] theorem ons_originNeighborRectDualPath_target_pullback (n : Nat) :
    ((ons_box2EquivRect (n + 1)).symm
      (ons_originNeighborRectDualPath n).target).1 = (![1, 0] : Site 2) := by
  simp [ons_originNeighborRectDualPath, ons_neighborPositiveBoxVertex]



def ons_fixedPairRectDualPath (N : Nat) (a b : Site 2)
    (ha : a ∈ box 2 N) (hb : b ∈ box 2 N) (hab : a ≠ b) (n : Nat) :
    ons_RectDualPath (2 * (n + 1)) (2 * (n + 1)) := by
  by_cases hN : N ≤ n + 1
  · exact ons_rectDualPathOfBoxVertices (n + 1)
      ⟨a, box_mono 2 hN ha⟩ ⟨b, box_mono 2 hN hb⟩
      (fun h => hab (congrArg Subtype.val h))
  · exact ons_originNeighborRectDualPath n

theorem ons_fixedPairRectDualPath_source_eventually
    (N : Nat) (a b : Site 2) (ha : a ∈ box 2 N) (hb : b ∈ box 2 N)
    (hab : a ≠ b) :
    ∀ᶠ n in atTop,
      ((ons_box2EquivRect (n + 1)).symm
        (ons_fixedPairRectDualPath N a b ha hb hab n).source).1 = a := by
  filter_upwards [eventually_ge_atTop N] with n hn
  have hN : N ≤ n + 1 := hn.trans (Nat.le_succ n)
  simp [ons_fixedPairRectDualPath, hN, ons_rectDualPathOfBoxVertices,
    ons_box2GraphIsoRect]

theorem ons_fixedPairRectDualPath_target_eventually
    (N : Nat) (a b : Site 2) (ha : a ∈ box 2 N) (hb : b ∈ box 2 N)
    (hab : a ≠ b) :
    ∀ᶠ n in atTop,
      ((ons_box2EquivRect (n + 1)).symm
        (ons_fixedPairRectDualPath N a b ha hb hab n).target).1 = b := by
  filter_upwards [eventually_ge_atTop N] with n hn
  have hN : N ≤ n + 1 := hn.trans (Nat.le_succ n)
  simp [ons_fixedPairRectDualPath, hN, ons_rectDualPathOfBoxVertices,
    ons_box2GraphIsoRect]




theorem ons_canonicalRectDualPathRatio_shifted_tendsto_freeState
    (beta : Real) (hbeta : 0 < beta)
    (path : ∀ n, ons_RectDualPath (2 * (n + 1)) (2 * (n + 1)))
    (a b : Site 2)
    (hsource : ∀ᶠ n in atTop,
      ((ons_box2EquivRect (n + 1)).symm (path n).source).1 = a)
    (htarget : ∀ᶠ n in atTop,
      ((ons_box2EquivRect (n + 1)).symm (path n).target).1 = b) :
    Tendsto (fun n => ons_rectDualPathRatio
        (ons_rectDualStraightLineEmbedding
          (2 * (n + 1)) (2 * (n + 1))) (path n) beta)
      atTop
      (nhds ((((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) ^ 2)) := by
  let f : Nat → Real := fun n =>
    ∫ spin, spinProd {a, b} spin
      ∂(freeMeasure 2 (n + 1) beta 0 : Measure (ConfigSpace (Site 2)))
  have hf : Tendsto f atTop
      (nhds (∫ spin, spinProd {a, b} spin
        ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2))))) := by
    simpa only [f] using
      (integral_freeMeasure_spinProd_tendsto_freeState
        2 beta hbeta.le ({a, b} : Finset (Site 2))).comp
          (tendsto_add_atTop_nat 1)
  have hfComplex : Tendsto (fun n => (f n : Complex)) atTop
      (nhds (((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex)) := by
    simpa only [Function.comp_apply] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hf
  apply (hfComplex.pow 2).congr'
  filter_upwards [hsource, htarget] with n hs ht
  rw [show ons_rectDualPathRatio
      (ons_rectDualStraightLineEmbedding
        (2 * (n + 1)) (2 * (n + 1))) (path n) beta =
      (isingExpectation
        (ons_rectDualGraph (2 * (n + 1)) (2 * (n + 1))) beta 0
        (fun spin => Ising.spin spin (path n).source *
          Ising.spin spin (path n).target) : Complex) ^ 2 by
    symm
    exact coe_ons_rectDualPath_finiteTwoPoint_sq_eq_canonicalKWDet_ratio
      (path n) hbeta]
  rw [show (isingExpectation
      (ons_rectDualGraph (2 * (n + 1)) (2 * (n + 1))) beta 0
      (fun spin => Ising.spin spin (path n).source *
        Ising.spin spin (path n).target) : Complex) =
      (((∫ spin, spinProd
        {((ons_box2EquivRect (n + 1)).symm (path n).source).1,
          ((ons_box2EquivRect (n + 1)).symm (path n).target).1} spin
        ∂(freeMeasure 2 (n + 1) beta 0 :
          Measure (ConfigSpace (Site 2)))) : Real) : Complex) by
    exact_mod_cast ons_rectDualPath_twoPoint_eq_freeMeasure
      (n + 1) beta (path n)]
  simp only [hs, ht, f]




theorem ons_originNeighborRectDualPathRatio_tendsto_freeState
    (beta : Real) (hbeta : 0 < beta) :
    Tendsto (fun n => ons_rectDualPathRatio
        (ons_rectDualStraightLineEmbedding
          (2 * (n + 1)) (2 * (n + 1)))
        (ons_originNeighborRectDualPath n) beta)
      atTop
      (nhds ((((∫ spin, spinProd
        {(![0, 0] : Site 2), (![1, 0] : Site 2)} spin
        ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) ^ 2)) := by
  apply ons_canonicalRectDualPathRatio_shifted_tendsto_freeState
    beta hbeta ons_originNeighborRectDualPath (![0, 0] : Site 2) ![1, 0]
  · filter_upwards with n
    exact ons_originNeighborRectDualPath_source_pullback n
  · filter_upwards with n
    exact ons_originNeighborRectDualPath_target_pullback n




theorem ons_fixedPairRectDualPathRatio_tendsto_freeState
    (beta : Real) (hbeta : 0 < beta)
    (N : Nat) (a b : Site 2) (ha : a ∈ box 2 N) (hb : b ∈ box 2 N)
    (hab : a ≠ b) :
    Tendsto (fun n => ons_rectDualPathRatio
        (ons_rectDualStraightLineEmbedding
          (2 * (n + 1)) (2 * (n + 1)))
        (ons_fixedPairRectDualPath N a b ha hb hab n) beta)
      atTop
      (nhds ((((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) ^ 2)) :=
  ons_canonicalRectDualPathRatio_shifted_tendsto_freeState beta hbeta
    (ons_fixedPairRectDualPath N a b ha hb hab) a b
    (ons_fixedPairRectDualPath_source_eventually N a b ha hb hab)
    (ons_fixedPairRectDualPath_target_eventually N a b ha hb hab)



theorem ons_canonicalRectDualPathCriticalRatio_shifted_tendsto_freeState
    (path : ∀ n, ons_RectDualPath (2 * (n + 1)) (2 * (n + 1)))
    (a b : Site 2)
    (hsource : ∀ᶠ n in atTop,
      ((ons_box2EquivRect (n + 1)).symm (path n).source).1 = a)
    (htarget : ∀ᶠ n in atTop,
      ((ons_box2EquivRect (n + 1)).symm (path n).target).1 = b) :
    Tendsto (fun n => ons_rectDualPathCriticalRatio
        (ons_rectDualStraightLineEmbedding
          (2 * (n + 1)) (2 * (n + 1))) (path n))
      atTop
      (nhds ((((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) ^ 2)) := by
  have hlimit := ons_canonicalRectDualPathRatio_shifted_tendsto_freeState
    ons_betaC ons_betaC_pos path a b hsource htarget
  apply hlimit.congr'
  filter_upwards with n
  simp only [ons_rectDualPathRatio, ons_rectDualPathCriticalRatio,
    tanh_ons_betaC]



theorem ons_originNeighborRectDualPathCriticalRatio_tendsto_freeState :
    Tendsto (fun n => ons_rectDualPathCriticalRatio
        (ons_rectDualStraightLineEmbedding
          (2 * (n + 1)) (2 * (n + 1)))
        (ons_originNeighborRectDualPath n))
      atTop
      (nhds ((((∫ spin, spinProd
        {(![0, 0] : Site 2), (![1, 0] : Site 2)} spin
        ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) ^ 2)) := by
  apply ons_canonicalRectDualPathCriticalRatio_shifted_tendsto_freeState
    ons_originNeighborRectDualPath (![0, 0] : Site 2) ![1, 0]
  · filter_upwards with n
    exact ons_originNeighborRectDualPath_source_pullback n
  · filter_upwards with n
    exact ons_originNeighborRectDualPath_target_pullback n



theorem ons_fixedPairRectDualPathCriticalRatio_tendsto_freeState
    (N : Nat) (a b : Site 2) (ha : a ∈ box 2 N) (hb : b ∈ box 2 N)
    (hab : a ≠ b) :
    Tendsto (fun n => ons_rectDualPathCriticalRatio
        (ons_rectDualStraightLineEmbedding
          (2 * (n + 1)) (2 * (n + 1)))
        (ons_fixedPairRectDualPath N a b ha hb hab n))
      atTop
      (nhds ((((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) ^ 2)) :=
  ons_canonicalRectDualPathCriticalRatio_shifted_tendsto_freeState
    (ons_fixedPairRectDualPath N a b ha hb hab) a b
    (ons_fixedPairRectDualPath_source_eventually N a b ha hb hab)
    (ons_fixedPairRectDualPath_target_eventually N a b ha hb hab)

end

end StatMech.Onsager
