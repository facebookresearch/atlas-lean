/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopSourceRootedDerivative





open scoped BigOperators
open Finset SimpleGraph Filter

namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def onsDefectEdgeDart {u v : V} (huv : u ≠ v) :
    (onsDefectEdgeGraph G u v).Dart := by
  refine ⟨(u, v), ?_⟩
  rw [onsDefectEdgeGraph, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩



def onsDefectEdgeAddedWeight (u v : V) (x : Real)
    (edge : Sym2 V) : Complex :=
  if edge = s(u, v) then 1 else (x : Complex)



theorem coe_ons_defectEdgeX_eq_kwEvenPolynomial_added
    {u v : V} (huv : u ≠ v) (hnotAdj : ¬ G.Adj u v)
    (x z : Real) :
    (ons_defectEdgeX G u v x z : Complex) =
      kwEvenPolynomial (onsDefectEdgeGraph G u v)
        (kwScaleGraphEdgeWeight
          (onsDefectEdgeAddedWeight u v x)
          (onsDefectEdgeDart G huv).edge (z : Complex)) := by
  unfold kwEvenPolynomial
  unfold ons_defectEdgeX
  dsimp only
  have hedges : (onsDefectEdgeGraph G u v).edgeFinset =
      insert s(u, v) G.edgeFinset := by
    ext edge
    obtain ⟨⟨a, b⟩, hab⟩ := edge.exists_rep
    rw [← hab]
    simp only [SimpleGraph.mem_edgeFinset, onsDefectEdgeGraph,
      Finset.mem_insert]
    constructor
    · rintro (hold | hnew)
      · exact Or.inr hold
      · left
        rw [SimpleGraph.edge_adj] at hnew
        rcases hnew.1 with h | h
        · rcases h with ⟨rfl, rfl⟩
          rfl
        · rcases h with ⟨rfl, rfl⟩
          exact Sym2.eq_swap
    · rintro (hnew | hold)
      · right
        rw [Sym2.eq_iff] at hnew
        rw [SimpleGraph.edge_adj]
        rcases hnew with h | h
        · rcases h with ⟨rfl, rfl⟩
          exact ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
        · rcases h with ⟨rfl, rfl⟩
          exact ⟨Or.inr ⟨rfl, rfl⟩, huv.symm⟩
      · exact Or.inl hold
  rw [hedges]
  push_cast
  apply Finset.sum_congr rfl
  intro F hF
  let e : Sym2 V := s(u, v)
  have hselected : (onsDefectEdgeDart G huv).edge = e := rfl
  rw [hselected]
  by_cases heF : e ∈ F
  · rw [if_pos heF]
    have hrest : (∏ f ∈ F.erase e,
        kwScaleGraphEdgeWeight (onsDefectEdgeAddedWeight u v x)
          e (z : Complex) f) = (x : Complex) ^ (F.erase e).card := by
      calc
        _ = ∏ _f ∈ F.erase e, (x : Complex) := by
          apply Finset.prod_congr rfl
          intro f hf
          have hfe : f ≠ e := Finset.ne_of_mem_erase hf
          simp [kwScaleGraphEdgeWeight, onsDefectEdgeAddedWeight, hfe, e]
        _ = _ := by simp
    calc
      (z : Complex) * (x : Complex) ^ (F.erase e).card =
          (∏ f ∈ F.erase e,
            kwScaleGraphEdgeWeight (onsDefectEdgeAddedWeight u v x)
              e (z : Complex) f) *
            kwScaleGraphEdgeWeight (onsDefectEdgeAddedWeight u v x)
              e (z : Complex) e := by
        rw [hrest]
        simp [kwScaleGraphEdgeWeight, onsDefectEdgeAddedWeight, e]
        ring
      _ = ∏ f ∈ F,
          kwScaleGraphEdgeWeight (onsDefectEdgeAddedWeight u v x)
            e (z : Complex) f := Finset.prod_erase_mul _ _ heF
  · rw [if_neg heF]
    have hprod : (∏ f ∈ F,
        kwScaleGraphEdgeWeight (onsDefectEdgeAddedWeight u v x)
          e (z : Complex) f) = (x : Complex) ^ F.card := by
      calc
        _ = ∏ _f ∈ F, (x : Complex) := by
          apply Finset.prod_congr rfl
          intro f hf
          have hfe : f ≠ e := fun h => heF (h ▸ hf)
          simp [kwScaleGraphEdgeWeight, onsDefectEdgeAddedWeight, hfe, e]
        _ = _ := by simp
    rw [Finset.erase_eq_of_notMem heF, hprod]
    norm_num



theorem ons_kwAddedEdgeEvenBase_defect_eq_ons_X
    {u v : V} (huv : u ≠ v) (hnotAdj : ¬ G.Adj u v) (x : Real) :
    ons_kwAddedEdgeEvenBase (onsDefectEdgeGraph G u v)
        (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) =
      (ons_X G x : Complex) := by
  have hpoly := coe_ons_defectEdgeX_eq_kwEvenPolynomial_added
    G huv hnotAdj x 0
  rw [ons_defectEdgeX_eq G huv hnotAdj x 0] at hpoly
  push_cast at hpoly
  simpa [ons_kwAddedEdgeEvenBase] using hpoly.symm



theorem ons_kwAddedEdgeEvenSource_defect_eq_sourceX
    {u v : V} (huv : u ≠ v) (hnotAdj : ¬ G.Adj u v) (x : Real) :
    ons_kwAddedEdgeEvenSource (onsDefectEdgeGraph G u v)
        (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) =
      (ons_sourceX G {u, v} x : Complex) := by
  have hpoly := coe_ons_defectEdgeX_eq_kwEvenPolynomial_added
    G huv hnotAdj x 1
  rw [ons_defectEdgeX_eq G huv hnotAdj x 1,
    kwEvenPolynomial_scaleGraphEdge_affine] at hpoly
  rw [ons_kwAddedEdgeEvenBase_defect_eq_ons_X G huv hnotAdj x] at hpoly
  push_cast at hpoly
  linear_combination hpoly.symm




theorem ons_kwAddedEdgeRoot_zero_defect_eq_ons_X
    {u v : V} (huv : u ≠ v) (hnotAdj : ¬ G.Adj u v)
    (embedding : KWStraightLineEmbedding (onsDefectEdgeGraph G u v))
    {x : Real} (hx : 0 ≤ x)
    (q : Real) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖ons_kwAddedEdgeBaseMatrix (onsDefectEdgeGraph G u v) embedding
        (onsDefectEdgeAddedWeight u v x) dart next‖ ≤ q)
    (hsmall : q <
      (2 * (Fintype.card (onsDefectEdgeGraph G u v).Dart : Real) ^ 2)⁻¹)
    (hcard : (Fintype.card (onsDefectEdgeGraph G u v).Dart : Real) * q < 1) :
    ons_kwAddedEdgeRoot (onsDefectEdgeGraph G u v) embedding
        (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) 0 =
      (ons_X G x : Complex) := by
  let H := onsDefectEdgeGraph G u v
  let weight := onsDefectEdgeAddedWeight u v x
  let selected := onsDefectEdgeDart G huv
  let M := kwGraphTransition H
    (kwScaleGraphEdgeWeight weight selected.edge 0) embedding.turnPhase
  let root := ons_detWalkRoot M
  let X : Complex := ons_X G x
  letI : Nonempty H.Dart := ⟨selected⟩
  have hentry0 : ∀ dart next, ‖M dart next‖ ≤ q := by
    intro dart next
    dsimp only [M, H, weight, selected]
    rw [kwGraphTransition_scaleEdge_entry]
    by_cases hedge : dart.edge = (onsDefectEdgeDart G huv).edge
    · simpa [hedge] using hq
    · simpa [hedge] using hentry dart next
  have hnear : ‖root - 1‖ < 1 := by
    exact ons_detWalkRoot_norm_sub_one_lt_one M q hq hentry0 hcard
      (ons_geom_sum_lt_one_of_Sherman_small q hq hsmall)
  have hsq : root ^ 2 = X ^ 2 := by
    have hsquare := ons_kwAddedEdgeRoot_sq_eq_evenPolynomial_sq
      H embedding weight selected q hq hentry hcard 0 (by simp)
    rw [show kwEvenPolynomial H
        (kwScaleGraphEdgeWeight weight selected.edge 0) = X by
      exact ons_kwAddedEdgeEvenBase_defect_eq_ons_X G huv hnotAdj x]
      at hsquare
    exact hsquare
  have hfactor : (root - X) * (root + X) = 0 := by
    calc
      (root - X) * (root + X) = root ^ 2 - X ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hfactor with hsame | hopposite
  · exact sub_eq_zero.mp hsame
  · have hroot : root = -X := by linear_combination hopposite
    rw [hroot] at hnear
    have hXpos : 0 < ons_X G x := ons_X_pos G x hx
    have hcast : -X - 1 = ((-ons_X G x - 1 : Real) : Complex) := by
      simp [X]
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith)] at hnear
    linarith



theorem ons_kwAddedEdgeNormalizedSource_defect_eq_sourceX
    {u v : V} (huv : u ≠ v) (hnotAdj : ¬ G.Adj u v)
    (embedding : KWStraightLineEmbedding (onsDefectEdgeGraph G u v))
    {x : Real} (hx : 0 ≤ x)
    (hbranch : ons_kwAddedEdgeRoot (onsDefectEdgeGraph G u v) embedding
      (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) 0 =
        (ons_X G x : Complex)) :
    ons_kwAddedEdgeNormalizedSource (onsDefectEdgeGraph G u v) embedding
        (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) =
      (ons_sourceX G {u, v} x : Complex) := by
  unfold ons_kwAddedEdgeNormalizedSource
  rw [ons_kwAddedEdgeEvenBase_defect_eq_ons_X G huv hnotAdj x,
    ons_kwAddedEdgeEvenSource_defect_eq_sourceX G huv hnotAdj x,
    hbranch]
  have hX : (ons_X G x : Complex) ≠ 0 := by
    exact_mod_cast (ons_X_pos G x hx).ne'
  field_simp



theorem coe_ons_sourceX_eq_neg_deleted_mul_rooted_defect
    {u v : V} (huv : u ≠ v) (hnotAdj : ¬ G.Adj u v)
    (embedding : KWStraightLineEmbedding (onsDefectEdgeGraph G u v))
    {x : Real} (hx : 0 ≤ x)
    (q : Real) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖ons_kwAddedEdgeBaseMatrix (onsDefectEdgeGraph G u v) embedding
        (onsDefectEdgeAddedWeight u v x) dart next‖ ≤ q)
    (hsmall : q <
      (2 * (Fintype.card (onsDefectEdgeGraph G u v).Dart : Real) ^ 2)⁻¹)
    (hcard : (Fintype.card (onsDefectEdgeGraph G u v).Dart : Real) * q < 1)
    (hbranch : ons_kwAddedEdgeRoot (onsDefectEdgeGraph G u v) embedding
      (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) 0 =
        (ons_X G x : Complex)) :
    (ons_sourceX G {u, v} x : Complex) =
      -(ons_kwAddedEdgeDeletedRoot (onsDefectEdgeGraph G u v) embedding
          (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) *
        ons_kwAddedEdgeRootedSeries (onsDefectEdgeGraph G u v) embedding
          (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv)) := by
  rw [← ons_kwAddedEdgeNormalizedSource_defect_eq_sourceX
    G huv hnotAdj embedding hx hbranch]
  exact ons_kwAddedEdgeNormalizedSource_eq_neg_deleted_mul_rooted
    (onsDefectEdgeGraph G u v) embedding
    (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv)
    q hq hentry hsmall hcard


theorem coe_ons_sourceX_eq_neg_deleted_mul_rooted_defect_of_small
    {u v : V} (huv : u ≠ v) (hnotAdj : ¬ G.Adj u v)
    (embedding : KWStraightLineEmbedding (onsDefectEdgeGraph G u v))
    {x : Real} (hx : 0 ≤ x)
    (q : Real) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖ons_kwAddedEdgeBaseMatrix (onsDefectEdgeGraph G u v) embedding
        (onsDefectEdgeAddedWeight u v x) dart next‖ ≤ q)
    (hsmall : q <
      (2 * (Fintype.card (onsDefectEdgeGraph G u v).Dart : Real) ^ 2)⁻¹)
    (hcard : (Fintype.card (onsDefectEdgeGraph G u v).Dart : Real) * q < 1) :
    (ons_sourceX G {u, v} x : Complex) =
      -(ons_kwAddedEdgeDeletedRoot (onsDefectEdgeGraph G u v) embedding
          (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) *
        ons_kwAddedEdgeRootedSeries (onsDefectEdgeGraph G u v) embedding
          (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv)) := by
  exact coe_ons_sourceX_eq_neg_deleted_mul_rooted_defect G huv hnotAdj
    embedding hx q hq hentry hsmall hcard
    (ons_kwAddedEdgeRoot_zero_defect_eq_ons_X G huv hnotAdj embedding
      hx q hq hentry hsmall hcard)

end

end StatMech.Onsager
