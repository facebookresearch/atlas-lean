/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Sharpness.CurrentRep
import Code.Sharpness.BackboneProps
import Code.Ising.TwoReplica

open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Sharpness

open StatMech.Ising (bond)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]








noncomputable instance shb_pathLinearOrder (x y : V) : LinearOrder (G.Path x y) :=
  LinearOrder.lift' (Fintype.equivFin (G.Path x y)) (Fintype.equivFin _).injective






def shb_IsBackboneOf (n : Current V) (x y : V) (ω : G.Path x y) : Prop :=
  ∀ e ∈ ω.1.edges, Odd (n e)

instance (n : Current V) (x y : V) (ω : G.Path x y) :
    Decidable (shb_IsBackboneOf G n x y ω) := by
  unfold shb_IsBackboneOf; infer_instance


noncomputable def shb_backboneSet (n : Current V) (x y : V) : Finset (G.Path x y) :=
  Finset.univ.filter (fun ω => shb_IsBackboneOf G n x y ω)

@[simp]
theorem shb_mem_backboneSet (n : Current V) (x y : V) (ω : G.Path x y) :
    ω ∈ shb_backboneSet G n x y ↔ shb_IsBackboneOf G n x y ω := by
  unfold shb_backboneSet; simp [Finset.mem_filter]



theorem shb_isBackbonePath_mem_backboneSet (n : Current V) (x y : V)
    (p : IsBackbonePath G n x y) :
    (⟨p.1.mapLe (oddSubgraph_le G n), p.2.mapLe (oddSubgraph_le G n)⟩ : G.Path x y)
      ∈ shb_backboneSet G n x y := by
  rw [shb_mem_backboneSet]
  intro e he
  rw [Walk.edges_mapLe_eq_edges] at he
  exact isBackbonePath_edge_odd G p he



noncomputable def shb_backboneOf_imp_isBackbonePath (n : Current V) (x y : V) (ω : G.Path x y)
    (h : shb_IsBackboneOf G n x y ω) : IsBackbonePath G n x y := by
  refine ⟨ω.1.transfer (oddSubgraph G n) ?_, ω.2.transfer _⟩
  intro e he
  have hG : e ∈ G.edgeSet := ω.1.edges_subset_edgeSet he
  have hodd : Odd (n e) := h e he
  revert hG hodd
  refine Sym2.ind (fun a b => ?_) e
  intro hG hodd
  rw [SimpleGraph.mem_edgeSet] at hG ⊢
  exact ⟨hG, hodd⟩











theorem shb_adjP_oddEdges_imp_adj (n : Current V) {a b : V}
    (h : StatMech.Ising.adjP (StatMech.Ising.oddEdges G.edgeFinset n) a b) :
    (oddSubgraph G n).Adj a b := by
  obtain ⟨e, he, ha, hb, hne⟩ := h
  rw [StatMech.Ising.oddEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
  obtain ⟨heG, hodd⟩ := he
  have hee : e = s(a, b) := (Sym2.mem_and_mem_iff hne).mp ⟨ha, hb⟩
  rw [hee, SimpleGraph.mem_edgeSet] at heG
  rw [hee] at hodd
  exact ⟨heG, hodd⟩


theorem shb_connP_oddEdges_imp_reachable (n : Current V) {a b : V}
    (h : StatMech.Ising.connP (StatMech.Ising.oddEdges G.edgeFinset n) a b) :
    (oddSubgraph G n).Reachable a b := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hstep ih => exact ih.trans (shb_adjP_oddEdges_imp_adj G n hstep).reachable



theorem shb_sources_eq (n : Current V) :
    Sharpness.sources G n = StatMech.Ising.sources G.edgeFinset n := rfl



theorem shb_backbone_exists (n : Current V) {x y : V} (hxy : x ≠ y)
    (hsrc : Sharpness.sources G n = {x, y}) :
    Nonempty (IsBackbonePath G n x y) := by
  have hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    exact SimpleGraph.not_isDiag_of_mem_edgeSet G he
  have hsrc' : StatMech.Ising.sources G.edgeFinset n = {x, y} := by
    rw [← shb_sources_eq]; exact hsrc
  have hconn := StatMech.Ising.connOdd_of_sources G.edgeFinset n hnd hxy hsrc'
  exact (shb_connP_oddEdges_imp_reachable G n hconn).elim (fun w => ⟨w.toPath⟩)



theorem shb_backboneSet_nonempty_of_sources (n : Current V) {x y : V} (hxy : x ≠ y)
    (hsrc : Sharpness.sources G n = {x, y}) :
    (shb_backboneSet G n x y).Nonempty :=
  ⟨_, shb_isBackbonePath_mem_backboneSet G n x y (shb_backbone_exists G n hxy hsrc).some⟩




noncomputable def shb_backboneSelect (n : Current V) (x y : V) : Option (G.Path x y) :=
  if h : (shb_backboneSet G n x y).Nonempty then
    some ((shb_backboneSet G n x y).min' h) else none








theorem shb_weight_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (n : Current V) : 0 ≤ weight G β J n := by
  unfold weight
  apply Finset.prod_nonneg
  intro e _
  exact div_nonneg (pow_nonneg (mul_nonneg hβ (hJ e)) _) (by positivity)


theorem shb_summable_weight (β : ℝ) (J : Sym2 V → ℝ) :
    Summable (fun m : ↥G.edgeFinset → ℕ => weight G β J (ofEdgeFun G m)) := by
  have h := summable_weight_bond G β J (fun _ => true)
  refine h.congr (fun m => ?_)
  have hone : ∀ e : ↥G.edgeFinset, (bond (fun _ => true) e.1) = 1 := by
    intro e; refine Sym2.ind (fun a b => ?_) e.1; simp [bond]
  simp only [hone, one_pow, Finset.prod_const_one, mul_one]


theorem shb_summable_indicator (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (P : (↥G.edgeFinset → ℕ) → Prop) [DecidablePred P] :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      if P m then weight G β J (ofEdgeFun G m) else 0) := by
  refine (shb_summable_weight G β J).of_nonneg_of_le ?_ ?_
  · intro m; split <;> [exact shb_weight_nonneg G β J hβ hJ _; rfl]
  · intro m; split <;> [exact le_refl _; exact shb_weight_nonneg G β J hβ hJ _]





noncomputable def shb_backboneNum (β : ℝ) (J : Sym2 V → ℝ) (x y : V) (ω : G.Path x y) : ℝ :=
  ∑' m : ↥G.edgeFinset → ℕ,
    if Sharpness.sources G (ofEdgeFun G m) = {x, y}
        ∧ shb_backboneSelect G (ofEdgeFun G m) x y = some ω then
      weight G β J (ofEdgeFun G m) else 0


noncomputable def shb_rho (β : ℝ) (J : Sym2 V → ℝ) (x y : V) (ω : G.Path x y) : ℝ :=
  shb_backboneNum G β J x y ω / currentSum G β J ∅






theorem shb_indicator_eq_sum (β : ℝ) (J : Sym2 V → ℝ) {x y : V} (hxy : x ≠ y)
    (m : ↥G.edgeFinset → ℕ) :
    (if Sharpness.sources G (ofEdgeFun G m) = {x, y} then weight G β J (ofEdgeFun G m) else 0)
      = ∑ ω : G.Path x y,
          (if Sharpness.sources G (ofEdgeFun G m) = {x, y}
              ∧ shb_backboneSelect G (ofEdgeFun G m) x y = some ω then
            weight G β J (ofEdgeFun G m) else 0) := by
  set n := ofEdgeFun G m
  by_cases hs : Sharpness.sources G n = {x, y}
  · rw [if_pos hs]
    have hne : (shb_backboneSet G n x y).Nonempty :=
      shb_backboneSet_nonempty_of_sources G n hxy hs
    have hsel : shb_backboneSelect G n x y = some ((shb_backboneSet G n x y).min' hne) := by
      unfold shb_backboneSelect; rw [dif_pos hne]
    rw [Finset.sum_eq_single ((shb_backboneSet G n x y).min' hne)]
    · rw [if_pos ⟨hs, hsel⟩]
    · intro ω _ hne'
      rw [if_neg]
      rintro ⟨_, hsel'⟩
      rw [hsel] at hsel'
      exact hne' ((Option.some.injEq _ _).mp hsel').symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hs]
    refine (Finset.sum_eq_zero ?_).symm
    intro ω _
    rw [if_neg (fun h => hs h.1)]




theorem shb_currentSum_eq_sum_backboneNum (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) {x y : V} (hxy : x ≠ y) :
    currentSum G β J {x, y} = ∑ ω : G.Path x y, shb_backboneNum G β J x y ω := by
  unfold currentSum shb_backboneNum
  rw [← Summable.tsum_finsetSum (s := (Finset.univ : Finset (G.Path x y)))
        (f := fun ω (m : ↥G.edgeFinset → ℕ) =>
          if Sharpness.sources G (ofEdgeFun G m) = {x, y}
              ∧ shb_backboneSelect G (ofEdgeFun G m) x y = some ω then
            weight G β J (ofEdgeFun G m) else 0)
        (fun ω _ => shb_summable_indicator G β J hβ hJ _)]
  refine tsum_congr (fun m => ?_)
  exact shb_indicator_eq_sum G β J hxy m











theorem shb_P1 (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    {x y : V} (hxy : x ≠ y) :
    expectationJ G β J {x, y} = ∑ ω : G.Path x y, shb_rho G β J x y ω := by
  rw [current_representation, shb_currentSum_eq_sum_backboneNum G β J hβ hJ hxy]
  unfold shb_rho
  rw [Finset.sum_div]



theorem shb_P1_ising (β : ℝ) (hβ : 0 ≤ β) {x y : V} (hxy : x ≠ y) :
    StatMech.Ising.isingExpectation G β 0 (StatMech.Ising.spinProd {x, y})
      = ∑ ω : G.Path x y, shb_rho G β (fun _ => 1) x y ω := by
  rw [← expectationJ_one_eq_isingExpectation]
  exact shb_P1 G β (fun _ => 1) hβ (fun _ => zero_le_one) hxy














end Sharpness

end StatMech
