/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.Z2GaugeIsingAdapter

open scoped symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace StatMech.FrontierA

variable {E P V : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]

noncomputable local instance z2GaugeAffinePropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p


theorem plaquetteIncidenceCount_eq_filter_card
    (incidence : P → Finset E) (A : Finset P) (e : E) :
    plaquetteIncidenceCount incidence A e =
      (A.filter fun p => e ∈ incidence p).card := by
  unfold plaquetteIncidenceCount
  rw [card_eq_sum_ones, sum_filter]


theorem filter_symmDiff_eq
    (A B : Finset P) (q : P → Prop) [DecidablePred q] :
    (A ∆ B).filter q = A.filter q ∆ B.filter q := by
  ext p
  simp only [mem_filter, mem_symmDiff]
  tauto


theorem card_symmDiff_add_twice_inter (A B : Finset P) :
    (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  rw [symmDiff_def]
  change ((A \ B) ∪ (B \ A)).card + 2 * (A ∩ B).card = A.card + B.card
  rw [card_union_of_disjoint]
  · rw [card_sdiff, card_sdiff]
    have hA := card_le_card (inter_subset_left : A ∩ B ⊆ A)
    have hB := card_le_card (inter_subset_right : A ∩ B ⊆ B)
    simp only [inter_comm B A]
    omega
  · rw [disjoint_left]
    intro p hpA hpB
    simp only [mem_sdiff] at hpA hpB
    exact hpA.2 hpB.1



theorem even_plaquetteIncidenceCount_symmDiff_iff
    (incidence : P → Finset E) (A B : Finset P) (e : E) :
    Even (plaquetteIncidenceCount incidence (A ∆ B) e) ↔
      (Even (plaquetteIncidenceCount incidence A e) ↔
        Even (plaquetteIncidenceCount incidence B e)) := by
  rw [plaquetteIncidenceCount_eq_filter_card,
    plaquetteIncidenceCount_eq_filter_card,
    plaquetteIncidenceCount_eq_filter_card,
    filter_symmDiff_eq]
  let X := A.filter fun p => e ∈ incidence p
  let Y := B.filter fun p => e ∈ incidence p
  have hcard := card_symmDiff_add_twice_inter X Y
  have htwo : Even (2 * (X ∩ Y).card) := ⟨(X ∩ Y).card, by omega⟩
  constructor
  · intro hdiff
    have hsum : Even (X.card + Y.card) := by
      rw [← hcard]
      exact hdiff.add htwo
    exact Nat.even_add.mp hsum
  · intro hsame
    have hsum : Even (X.card + Y.card) := Nat.even_add.mpr hsame
    have hdiffPlus : Even ((X ∆ Y).card + 2 * (X ∩ Y).card) := by
      rw [hcard]
      exact hsum
    exact (Nat.even_add.mp hdiffPlus).mpr htwo


theorem mem_gaugeClosedSurfaceFamily_iff
    (incidence : P → Finset E) (A : Finset P) :
    A ∈ gaugeClosedSurfaceFamily incidence ↔
      IsClosedPlaquetteSet incidence A := by
  unfold gaugeClosedSurfaceFamily
  simp



theorem mem_gaugeWilsonSurfaceFamily_iff
    (incidence : P → Finset E) (L : Finset E) (A : Finset P) :
    A ∈ gaugeWilsonSurfaceFamily incidence L ↔
      HasWilsonBoundary incidence A L := by
  unfold gaugeWilsonSurfaceFamily
  simp



theorem hasWilsonBoundary_iff_symmDiff_closed
    (incidence : P → Finset E) (L : Finset E) (D A : Finset P)
    (hD : HasWilsonBoundary incidence D L) :
    HasWilsonBoundary incidence A L ↔
      IsClosedPlaquetteSet incidence (A ∆ D) := by
  have hparity : HasWilsonBoundary incidence A L ↔
      ∀ e, Even (plaquetteIncidenceCount incidence A e) ↔
        Even (plaquetteIncidenceCount incidence D e) := by
    constructor
    · intro hA e
      have hAe := hA e
      have hDe := hD e
      by_cases he : e ∈ L
      · simp only [he, if_true, Nat.even_add_one] at hAe hDe
        tauto
      · simp only [he, if_false, add_zero] at hAe hDe
        tauto
    · intro hsame e
      have hDe := hD e
      have hsameE := hsame e
      by_cases he : e ∈ L
      · simp only [he, if_true, Nat.even_add_one] at hDe ⊢
        tauto
      · simp only [he, if_false, add_zero] at hDe ⊢
        tauto
  rw [hparity]
  unfold IsClosedPlaquetteSet
  constructor
  · intro hsame e
    exact (even_plaquetteIncidenceCount_symmDiff_iff incidence A D e).2
      (hsame e)
  · intro hclosed e
    exact (even_plaquetteIncidenceCount_symmDiff_iff incidence A D e).1
      (hclosed e)



noncomputable def gaugeWilsonClosedEquiv
    (incidence : P → Finset E) (L : Finset E) (D : Finset P)
    (hD : HasWilsonBoundary incidence D L) :
    {A : Finset P // A ∈ gaugeWilsonSurfaceFamily incidence L} ≃
      {B : Finset P // B ∈ gaugeClosedSurfaceFamily incidence} where
  toFun A := ⟨A.1 ∆ D,
    (mem_gaugeClosedSurfaceFamily_iff incidence _).2
      ((hasWilsonBoundary_iff_symmDiff_closed incidence L D A.1 hD).1
        ((mem_gaugeWilsonSurfaceFamily_iff incidence L A.1).1 A.2))⟩
  invFun B := ⟨B.1 ∆ D,
    (mem_gaugeWilsonSurfaceFamily_iff incidence L _).2
      ((hasWilsonBoundary_iff_symmDiff_closed incidence L D (B.1 ∆ D) hD).2
        (by simpa using
          (mem_gaugeClosedSurfaceFamily_iff incidence B.1).1 B.2))⟩
  left_inv A := by
    apply Subtype.ext
    simp
  right_inv B := by
    apply Subtype.ext
    simp


theorem map_symmDiff_embedding
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (f : alpha ↪ beta) (A B : Finset alpha) :
    (A ∆ B).map f = A.map f ∆ B.map f := by
  rw [symmDiff_def, symmDiff_def]
  change ((A \ B) ∪ (B \ A)).map f =
    (A.map f \ B.map f) ∪ (B.map f \ A.map f)
  rw [Finset.map_union, Finset.map_sdiff, Finset.map_sdiff]



noncomputable def cutSpaceShiftEquiv
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset (Sym2 V)) :
    {delta : Finset (Sym2 V) // delta ∈ StatMech.Ising.cutSpace G} ≃
      {gamma : Finset (Sym2 V) //
        gamma ∈ shiftedDualCutFamily (G := G) D} where
  toFun delta := ⟨delta.1 ∆ D, by
    unfold shiftedDualCutFamily
    rw [Finset.mem_image]
    exact ⟨delta.1, delta.2, rfl⟩⟩
  invFun gamma := ⟨gamma.1 ∆ D, by
    have hmem := gamma.2
    unfold shiftedDualCutFamily at hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨delta, hdelta, hgamma⟩ := hmem
    have hcancel : gamma.1 ∆ D = delta := by
      rw [← hgamma]
      simp
    simpa only [hcancel] using hdelta⟩
  left_inv delta := by
    apply Subtype.ext
    simp
  right_inv gamma := by
    apply Subtype.ext
    simp



noncomputable def gaugeWilsonShiftedCutEquiv
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (incidence : P → Finset E) (L : Finset E)
    (dualEdge : P ≃ G.edgeFinset)
    (closedEquiv :
      {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃
        {delta : Finset (Sym2 V) // delta ∈ StatMech.Ising.cutSpace G})
    (D : Finset P) (hD : HasWilsonBoundary incidence D L) :
    {A : Finset P // A ∈ gaugeWilsonSurfaceFamily incidence L} ≃
      {gamma : Finset (Sym2 V) // gamma ∈ shiftedDualCutFamily
        (G := G) (D.map (dualPlaquetteEmbedding dualEdge))} :=
  (gaugeWilsonClosedEquiv incidence L D hD).trans
    (closedEquiv.trans
      (cutSpaceShiftEquiv G (D.map (dualPlaquetteEmbedding dualEdge))))



theorem gaugeWilsonShiftedCutEquiv_apply
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (incidence : P → Finset E) (L : Finset E)
    (dualEdge : P ≃ G.edgeFinset)
    (closedEquiv :
      {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃
        {delta : Finset (Sym2 V) // delta ∈ StatMech.Ising.cutSpace G})
    (hclosed : ∀ A,
      (closedEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge))
    (D : Finset P) (hD : HasWilsonBoundary incidence D L)
    (A : {A : Finset P // A ∈ gaugeWilsonSurfaceFamily incidence L}) :
    (gaugeWilsonShiftedCutEquiv incidence L dualEdge closedEquiv D hD A).1 =
      A.1.map (dualPlaquetteEmbedding dualEdge) := by
  change (closedEquiv
      ((gaugeWilsonClosedEquiv incidence L D hD) A)).1 ∆
        D.map (dualPlaquetteEmbedding dualEdge) =
    A.1.map (dualPlaquetteEmbedding dualEdge)
  rw [hclosed]
  change (A.1 ∆ D).map (dualPlaquetteEmbedding dualEdge) ∆
      D.map (dualPlaquetteEmbedding dualEdge) =
    A.1.map (dualPlaquetteEmbedding dualEdge)
  rw [map_symmDiff_embedding]
  simp



theorem gaugeWilsonExpectation_eq_dualDisorderRatio_of_sheet
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (incidence : P → Finset E) (K : P → ℝ) (hK : ∀ p, 0 < K p)
    (L : Finset E) (dualEdge : P ≃ G.edgeFinset)
    (closedEquiv :
      {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃
        {delta : Finset (Sym2 V) // delta ∈ StatMech.Ising.cutSpace G})
    (hclosed : ∀ A,
      (closedEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge))
    (D : Finset P) (hD : HasWilsonBoundary incidence D L) :
    gaugeWilsonExpectation incidence K L =
      (∑ gamma ∈ shiftedDualCutFamily (G := G)
          (D.map (dualPlaquetteEmbedding dualEdge)),
          ∏ e ∈ gamma, Real.exp (-2 * dualIsingCoupling dualEdge K e)) /
        (∑ delta ∈ StatMech.Ising.cutSpace G,
          ∏ e ∈ delta, Real.exp (-2 * dualIsingCoupling dualEdge K e)) := by
  exact gaugeWilsonExpectation_eq_dualDisorderRatio incidence K hK L
    (D.map (dualPlaquetteEmbedding dualEdge)) dualEdge closedEquiv hclosed
    (gaugeWilsonShiftedCutEquiv incidence L dualEdge closedEquiv D hD)
    (gaugeWilsonShiftedCutEquiv_apply incidence L dualEdge closedEquiv hclosed D hD)

end StatMech.FrontierA
