/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.BeffaraDC.TorusCellRN
import Code.BeffaraDC.Duality
import Code.FK.FiniteVolumeShift

open SimpleGraph Set
open scoped BigOperators

namespace StatMech.BeffaraDC

open StatMech.Onsager


def torusCoordSwap (L : ℕ) : (ZMod L × ZMod L) ≃ (ZMod L × ZMod L) where
  toFun x := (x.2, x.1)
  invFun x := (x.2, x.1)
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

@[simp] theorem torusCoordSwap_apply (L : ℕ) (x : ZMod L × ZMod L) :
    torusCoordSwap L x = (x.2, x.1) := rfl

@[simp] theorem torusCoordSwap_symm (L : ℕ) :
    (torusCoordSwap L).symm = torusCoordSwap L := rfl


theorem onsTorusGraph_adj_coordSwap (L : ℕ) [Fact (2 < L)]
    (x y : ZMod L × ZMod L) :
    (onsTorusGraph L).Adj (torusCoordSwap L x) (torusCoordSwap L y) ↔
      (onsTorusGraph L).Adj x y := by
  change onsTorusAdj L (x.2, x.1) (y.2, y.1) ↔ onsTorusAdj L x y
  unfold onsTorusAdj
  tauto


theorem torusCoordSwap_mem_edgeFinset_iff (L : ℕ) [Fact (2 < L)]
    (e : Sym2 (ZMod L × ZMod L)) :
    Sym2.map (torusCoordSwap L) e ∈ (onsTorusGraph L).edgeFinset ↔
      e ∈ (onsTorusGraph L).edgeFinset := by
  induction e using Sym2.ind with
  | _ x y =>
      simp only [Sym2.map_mk, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      exact onsTorusGraph_adj_coordSwap L x y


noncomputable def torusAmbientSwapEdgeEquiv (L : ℕ) [Fact (2 < L)] :
    TorusAmbientEdge L ≃ TorusAmbientEdge L where
  toFun e := ⟨Sym2.map (torusCoordSwap L) e.1,
    (torusCoordSwap_mem_edgeFinset_iff L e.1).2 e.2⟩
  invFun e := ⟨Sym2.map (torusCoordSwap L) e.1,
    (torusCoordSwap_mem_edgeFinset_iff L e.1).2 e.2⟩
  left_inv e := by
    apply Subtype.ext
    change Sym2.map (torusCoordSwap L)
      (Sym2.map (torusCoordSwap L) e.1) = e.1
    induction e.1 using Sym2.ind with
    | _ x y => simp [torusCoordSwap]
  right_inv e := by
    apply Subtype.ext
    change Sym2.map (torusCoordSwap L)
      (Sym2.map (torusCoordSwap L) e.1) = e.1
    induction e.1 using Sym2.ind with
    | _ x y => simp [torusCoordSwap]


noncomputable def torusAmbientSwapConfig (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) : TorusAmbientConfig L :=
  fun e => omega ((torusAmbientSwapEdgeEquiv L).symm e)


noncomputable def torusAmbientSwapConfigEquiv (L : ℕ) [Fact (2 < L)] :
    TorusAmbientConfig L ≃ TorusAmbientConfig L where
  toFun := torusAmbientSwapConfig L
  invFun eta := fun e => eta (torusAmbientSwapEdgeEquiv L e)
  left_inv omega := by
    funext e
    simp [torusAmbientSwapConfig]
  right_inv omega := by
    funext e
    simp [torusAmbientSwapConfig]


theorem torusAmbientConfigExtend_swap (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    torusAmbientConfigExtend L (torusAmbientSwapConfig L omega) =
      FK.reCfgIso (torusCoordSwap L) (torusAmbientConfigExtend L omega) := by
  funext e
  by_cases he : e ∈ (onsTorusGraph L).edgeFinset
  · have hse : Sym2.map (torusCoordSwap L) e ∈
        (onsTorusGraph L).edgeFinset :=
      (torusCoordSwap_mem_edgeFinset_iff L e).2 he
    rw [torusAmbientConfigExtend, dif_pos he, FK.fvs_reCfgIso_apply,
      torusAmbientConfigExtend, dif_pos hse]
    unfold torusAmbientSwapConfig
    congr 2
  · have hse : Sym2.map (torusCoordSwap L) e ∉
        (onsTorusGraph L).edgeFinset := by
      intro h
      exact he ((torusCoordSwap_mem_edgeFinset_iff L e).1 h)
    rw [torusAmbientConfigExtend, dif_neg he, FK.fvs_reCfgIso_apply,
      torusAmbientConfigExtend, dif_neg hse]


theorem torusAmbientFKWeight_swap (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (omega : TorusAmbientConfig L) :
    torusAmbientFKWeight L p q (torusAmbientSwapConfig L omega) =
      torusAmbientFKWeight L p q omega := by
  unfold torusAmbientFKWeight
  rw [torusAmbientConfigExtend_swap]
  exact FK.fvs_fkWeight_reCfgIso (onsTorusGraph L) (onsTorusGraph L)
    (torusCoordSwap L) (fun x y => (onsTorusGraph_adj_coordSwap L x y).symm)
    p q (torusAmbientConfigExtend L omega)


theorem torusAmbientProbability_swap (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (omega : TorusAmbientConfig L) :
    torusAmbientProbability L p q (torusAmbientSwapConfig L omega) =
      torusAmbientProbability L p q omega := by
  unfold torusAmbientProbability
  rw [torusAmbientFKWeight_swap]




noncomputable def torusAmbientEventProbability (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (A : Finset (TorusAmbientConfig L)) : ℝ :=
  ∑ omega : TorusAmbientConfig L,
    if omega ∈ A then torusAmbientProbability L p q omega else 0



noncomputable def torusAmbientRotatedEvent (L : ℕ) [Fact (2 < L)]
    (A : Finset (TorusAmbientConfig L)) : Finset (TorusAmbientConfig L) :=
  Finset.univ.filter fun omega => torusAmbientSwapConfig L omega ∈ A

@[simp] theorem mem_torusAmbientRotatedEvent (L : ℕ) [Fact (2 < L)]
    {A : Finset (TorusAmbientConfig L)} {omega : TorusAmbientConfig L} :
    omega ∈ torusAmbientRotatedEvent L A ↔
      torusAmbientSwapConfig L omega ∈ A := by
  simp [torusAmbientRotatedEvent]



theorem torusAmbientEventProbability_rotated (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (A : Finset (TorusAmbientConfig L)) :
    torusAmbientEventProbability L p q (torusAmbientRotatedEvent L A) =
      torusAmbientEventProbability L p q A := by
  unfold torusAmbientEventProbability
  have hsum := Equiv.sum_comp (torusAmbientSwapConfigEquiv L)
    (fun omega : TorusAmbientConfig L =>
      if omega ∈ A then torusAmbientProbability L p q omega else 0)
  simpa [torusAmbientSwapConfigEquiv, mem_torusAmbientRotatedEvent,
    torusAmbientProbability_swap] using hsum


noncomputable def torusAmbientDualPullbackEvent (L : ℕ) [Fact (2 < L)]
    (A : Finset (TorusAmbientConfig L)) : Finset (TorusAmbientConfig L) :=
  Finset.univ.filter fun omega => torusCellDualAmbientConfig L omega ∈ A

@[simp] theorem mem_torusAmbientDualPullbackEvent (L : ℕ) [Fact (2 < L)]
    {A : Finset (TorusAmbientConfig L)} {omega : TorusAmbientConfig L} :
    omega ∈ torusAmbientDualPullbackEvent L A ↔
      torusCellDualAmbientConfig L omega ∈ A := by
  simp [torusAmbientDualPullbackEvent]


theorem torusAmbientProbability_le_q_mul_dual
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    {q : ℝ} (hq1 : 1 ≤ q) :
    torusAmbientProbability L (selfDualPoint q) q omega ≤
      q * torusAmbientProbability L (selfDualPoint q) q
        (torusCellDualAmbientConfig L omega) := by
  have hq : 0 < q := lt_of_lt_of_le one_pos hq1
  obtain ⟨hp, hp1⟩ := selfDualPoint_mem_Ioo hq
  have hdualpos : 0 < torusAmbientProbability L (selfDualPoint q) q
      (torusCellDualAmbientConfig L omega) := by
    unfold torusAmbientProbability
    exact div_pos (torusAmbientFKWeight_pos L _ hp hp1 hq)
      (torusAmbientPartition_pos L hp hp1 hq)
  have hr := (torusAmbientProbability_selfDual_ratio_mem L omega hq1).2
  rwa [div_le_iff₀ hdualpos] at hr



theorem torusAmbientDualPullbackEventProbability_le
    (L : ℕ) [Fact (2 < L)] (A : Finset (TorusAmbientConfig L))
    {q : ℝ} (hq1 : 1 ≤ q) :
    torusAmbientEventProbability L (selfDualPoint q) q
        (torusAmbientDualPullbackEvent L A) ≤
      q * torusAmbientEventProbability L (selfDualPoint q) q A := by
  unfold torusAmbientEventProbability
  calc
    (∑ omega : TorusAmbientConfig L,
        if omega ∈ torusAmbientDualPullbackEvent L A then
          torusAmbientProbability L (selfDualPoint q) q omega else 0) ≤
      ∑ omega : TorusAmbientConfig L,
        if torusCellDualAmbientConfig L omega ∈ A then
          q * torusAmbientProbability L (selfDualPoint q) q
            (torusCellDualAmbientConfig L omega) else 0 := by
        apply Finset.sum_le_sum
        intro omega _
        simp only [mem_torusAmbientDualPullbackEvent]
        split <;> simp_all [torusAmbientProbability_le_q_mul_dual L omega hq1]
    _ = q * ∑ eta : TorusAmbientConfig L,
        if eta ∈ A then torusAmbientProbability L (selfDualPoint q) q eta else 0 := by
      have hsum := Equiv.sum_comp (torusCellDualAmbientConfigEquiv L)
        (fun eta : TorusAmbientConfig L =>
          if eta ∈ A then torusAmbientProbability L (selfDualPoint q) q eta else 0)
      have hsum' : (∑ omega : TorusAmbientConfig L,
          if torusCellDualAmbientConfig L omega ∈ A then
            torusAmbientProbability L (selfDualPoint q) q
              (torusCellDualAmbientConfig L omega) else 0) =
          ∑ eta : TorusAmbientConfig L,
            if eta ∈ A then
              torusAmbientProbability L (selfDualPoint q) q eta else 0 := by
        simpa only [torusCellDualAmbientConfigEquiv] using hsum
      calc
        (∑ omega : TorusAmbientConfig L,
            if torusCellDualAmbientConfig L omega ∈ A then
              q * torusAmbientProbability L (selfDualPoint q) q
                (torusCellDualAmbientConfig L omega) else 0) =
          q * ∑ omega : TorusAmbientConfig L,
            if torusCellDualAmbientConfig L omega ∈ A then
              torusAmbientProbability L (selfDualPoint q) q
                (torusCellDualAmbientConfig L omega) else 0 := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro omega _
                  split <;> simp_all
        _ = q * ∑ eta : TorusAmbientConfig L,
            if eta ∈ A then
              torusAmbientProbability L (selfDualPoint q) q eta else 0 := by
                exact congrArg (fun x : ℝ => q * x) hsum'






def torusSquareVertexSet (L n : ℕ) : Set (ZMod L × ZMod L) :=
  {x | x.1.val ≤ n ∧ x.2.val ≤ n}



def torusSquareHorizontalCrossing (L : ℕ) [Fact (2 < L)] (n : ℕ)
    (omega : TorusAmbientConfig L) : Prop :=
  ∃ (x y : ZMod L × ZMod L)
      (hx : x ∈ torusSquareVertexSet L n)
      (hy : y ∈ torusSquareVertexSet L n),
    x.1.val = 0 ∧ y.1.val = n ∧
      ((FK.openSub (onsTorusGraph L) (torusAmbientConfigExtend L omega)).induce
        (torusSquareVertexSet L n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩


noncomputable def torusSquareHorizontalCrossingEvent
    (L : ℕ) [Fact (2 < L)] (n : ℕ) : Finset (TorusAmbientConfig L) := by
  classical
  exact Finset.univ.filter (torusSquareHorizontalCrossing L n)

@[simp] theorem mem_torusSquareHorizontalCrossingEvent
    (L : ℕ) [Fact (2 < L)] (n : ℕ) (omega : TorusAmbientConfig L) :
    omega ∈ torusSquareHorizontalCrossingEvent L n ↔
      torusSquareHorizontalCrossing L n omega := by
  classical
  simp [torusSquareHorizontalCrossingEvent]



noncomputable def torusSquareVerticalCrossingEvent
    (L : ℕ) [Fact (2 < L)] (n : ℕ) : Finset (TorusAmbientConfig L) :=
  torusAmbientRotatedEvent L (torusSquareHorizontalCrossingEvent L n)

@[simp] theorem mem_torusSquareVerticalCrossingEvent
    (L : ℕ) [Fact (2 < L)] (n : ℕ) (omega : TorusAmbientConfig L) :
    omega ∈ torusSquareVerticalCrossingEvent L n ↔
      torusSquareHorizontalCrossing L n (torusAmbientSwapConfig L omega) := by
  simp [torusSquareVerticalCrossingEvent]







theorem torus_squareCrossing_ge_one_div_one_add_q
    (L : ℕ) [Fact (2 < L)] (horizontal : Finset (TorusAmbientConfig L))
    {q : ℝ} (hq1 : 1 ≤ q)
    (hdualCrossing : ∀ omega : TorusAmbientConfig L,
      omega ∉ horizontal ↔
        torusCellDualAmbientConfig L omega ∈
          torusAmbientRotatedEvent L horizontal) :
    1 / (1 + q) ≤
      torusAmbientEventProbability L (selfDualPoint q) q horizontal := by
  let vertical := torusAmbientRotatedEvent L horizontal
  let dualVertical := torusAmbientDualPullbackEvent L vertical
  have hsum : torusAmbientEventProbability L (selfDualPoint q) q horizontal +
      torusAmbientEventProbability L (selfDualPoint q) q dualVertical = 1 := by
    unfold torusAmbientEventProbability
    rw [← Finset.sum_add_distrib]
    calc
      (∑ omega : TorusAmbientConfig L,
          ((if omega ∈ horizontal then
              torusAmbientProbability L (selfDualPoint q) q omega else 0) +
            if omega ∈ dualVertical then
              torusAmbientProbability L (selfDualPoint q) q omega else 0)) =
        ∑ omega : TorusAmbientConfig L,
          torusAmbientProbability L (selfDualPoint q) q omega := by
            apply Finset.sum_congr rfl
            intro omega _
            have hmem : omega ∈ dualVertical ↔ omega ∉ horizontal := by
              simpa [dualVertical, vertical] using (hdualCrossing omega).symm
            by_cases hh : omega ∈ horizontal <;> simp [hh, hmem]
      _ = 1 := by
        have hq : 0 < q := lt_of_lt_of_le one_pos hq1
        obtain ⟨hp, hp1⟩ := selfDualPoint_mem_Ioo hq
        exact torusAmbientProbability_sum_one L hp hp1 hq
  have hdualLe : torusAmbientEventProbability L (selfDualPoint q) q dualVertical ≤
      q * torusAmbientEventProbability L (selfDualPoint q) q horizontal := by
    calc
      torusAmbientEventProbability L (selfDualPoint q) q dualVertical ≤
          q * torusAmbientEventProbability L (selfDualPoint q) q vertical :=
        torusAmbientDualPullbackEventProbability_le L vertical hq1
      _ = q * torusAmbientEventProbability L (selfDualPoint q) q horizontal := by
        rw [torusAmbientEventProbability_rotated]
  exact dlt_square_crossing_estimate (by positivity) hsum hdualLe





theorem torus_concreteSquareCrossing_ge_one_div_one_add_q
    (L : ℕ) [Fact (2 < L)] (n : ℕ) (_hn : 1 ≤ n) (_hnL : n < L)
    {q : ℝ} (hq1 : 1 ≤ q)
    (hdualCrossing : ∀ omega : TorusAmbientConfig L,
      ¬ torusSquareHorizontalCrossing L n omega ↔
        torusCellDualAmbientConfig L omega ∈
          torusSquareVerticalCrossingEvent L n) :
    1 / (1 + q) ≤
      torusAmbientEventProbability L (selfDualPoint q) q
        (torusSquareHorizontalCrossingEvent L n) := by
  apply torus_squareCrossing_ge_one_div_one_add_q L
    (torusSquareHorizontalCrossingEvent L n) hq1
  intro omega
  simpa [torusSquareVerticalCrossingEvent] using hdualCrossing omega


theorem torus_squareCrossing_const_pos {q : ℝ} (hq1 : 1 ≤ q) :
    0 < 1 / (1 + q) := by
  positivity

end StatMech.BeffaraDC
