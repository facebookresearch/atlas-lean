/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Code.FrontierA.Z2GaugeWilsonAffine
import Code.Ising.KWClosedWalkParity

open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

local instance cycleCompletePropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def gaugeToggle {alpha : Type*} [DecidableEq alpha]
    (a : alpha) (S : Finset alpha) : Finset alpha :=
  if a ∈ S then S.erase a else insert a S

@[simp] theorem mem_gaugeToggle {alpha : Type*} [DecidableEq alpha]
    (a b : alpha) (S : Finset alpha) :
    b ∈ gaugeToggle a S ↔ (b = a ∧ b ∉ S) ∨ (b ≠ a ∧ b ∈ S) := by
  by_cases ha : a ∈ S
  · by_cases hba : b = a
    · subst b
      simp [gaugeToggle, ha]
    · simp [gaugeToggle, ha, hba]
  · by_cases hba : b = a
    · subst b
      simp [gaugeToggle, ha]
    · simp [gaugeToggle, ha, hba]


def walkOddSupport : {x y : V} -> G.Walk x y -> Finset (Sym2 V)
  | _, _, .nil => ∅
  | _, _, .cons (u := u) (v := v) _ p =>
      gaugeToggle s(u, v) (walkOddSupport p)

@[simp] theorem walkOddSupport_nil (x : V) :
    walkOddSupport G (.nil : G.Walk x x) = ∅ := rfl

@[simp] theorem walkOddSupport_cons {u v w : V} (h : G.Adj u v)
    (p : G.Walk v w) :
    walkOddSupport G (.cons h p) = gaugeToggle s(u, v) (walkOddSupport G p) :=
  rfl

theorem walkOddSupport_subset_edgeFinset {x y : V} (p : G.Walk x y) :
    walkOddSupport G p ⊆ G.edgeFinset := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      intro e he
      rw [walkOddSupport_cons, mem_gaugeToggle] at he
      rcases he with ⟨rfl, _⟩ | ⟨_, he⟩
      · simpa using h
      · exact ih he



private theorem filter_gaugeToggle_eq_of_not_mem
    {alpha : Type*} [DecidableEq alpha] (A S : Finset alpha) {a : alpha}
    (ha : a ∉ A) :
    A.filter (fun b => b ∈ gaugeToggle a S) = A.filter (fun b => b ∈ S) := by
  ext b
  by_cases hba : b = a
  · subst b
    simp [ha]
  · simp [mem_gaugeToggle, hba]


private theorem filter_gaugeToggle_eq_toggle_of_mem
    {alpha : Type*} [DecidableEq alpha] (A S : Finset alpha) {a : alpha}
    (ha : a ∈ A) :
    A.filter (fun b => b ∈ gaugeToggle a S) =
      gaugeToggle a (A.filter (fun b => b ∈ S)) := by
  ext b
  by_cases hba : b = a
  · subst b
    simp [ha, mem_gaugeToggle]
  · simp [mem_gaugeToggle, hba]


private theorem even_card_gaugeToggle_iff_not_even
    {alpha : Type*} [DecidableEq alpha] (a : alpha) (S : Finset alpha) :
    Even (gaugeToggle a S).card ↔ ¬ Even S.card := by
  by_cases ha : a ∈ S
  · rw [gaugeToggle, if_pos ha, card_erase_of_mem ha]
    rw [Nat.even_sub (by exact card_pos.mpr ⟨a, ha⟩)]
    simp
  · rw [gaugeToggle, if_neg ha, card_insert_of_notMem ha,
      Nat.even_add_one]



theorem even_filter_walkOddSupport_iff_walkParity_false
    (A : Finset (Sym2 V)) {x y : V} (p : G.Walk x y) :
    Even (A.filter (fun e => e ∈ walkOddSupport G p)).card ↔
      walkParity G A p = false := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      by_cases he : s(u, v) ∈ A
      · rw [walkOddSupport_cons,
          filter_gaugeToggle_eq_toggle_of_mem A (walkOddSupport G p) he,
          even_card_gaugeToggle_iff_not_even, walkParity_cons]
        rw [ih]
        cases walkParity G A p <;> simp [he]
      · rw [walkOddSupport_cons,
          filter_gaugeToggle_eq_of_not_mem A (walkOddSupport G p) he,
          walkParity_cons, ih]
        simp [he]


abbrev CycleCompleteConstraint :=
  {A : Finset (Sym2 V) // A ⊆ G.edgeFinset ∧ A ∉ cutSpace G}

theorem exists_odd_closed_walk [Nonempty V] (hG : G.Preconnected)
    (q : CycleCompleteConstraint G) :
    ∃ (x : V) (p : G.Walk x x), walkParity G q.1 p = true := by
  have hnot : ¬ EvenOnCycles G q.1 := by
    intro heven
    exact q.2.2 ((evenOnCycles_iff_mem_cutSpace hG q.2.1).mp heven)
  simp only [EvenOnCycles, not_forall] at hnot
  obtain ⟨x, hx⟩ := hnot
  obtain ⟨p, hp⟩ := hx
  refine ⟨x, p, ?_⟩
  cases hpar : walkParity G q.1 p <;> simp_all

noncomputable def cycleCompleteWitnessVertex [Nonempty V]
    (hG : G.Preconnected) (q : CycleCompleteConstraint G) : V :=
  Classical.choose (exists_odd_closed_walk G hG q)

noncomputable def cycleCompleteWitnessWalk [Nonempty V]
    (hG : G.Preconnected) (q : CycleCompleteConstraint G) :
    G.Walk (cycleCompleteWitnessVertex G hG q)
      (cycleCompleteWitnessVertex G hG q) :=
  Classical.choose (Classical.choose_spec (exists_odd_closed_walk G hG q))

theorem cycleCompleteWitnessWalk_odd [Nonempty V]
    (hG : G.Preconnected) (q : CycleCompleteConstraint G) :
    walkParity G q.1 (cycleCompleteWitnessWalk G hG q) = true :=
  Classical.choose_spec (Classical.choose_spec (exists_odd_closed_walk G hG q))



noncomputable def cycleCompleteIncidence [Nonempty V]
    (hG : G.Preconnected) :
    G.edgeFinset -> Finset (CycleCompleteConstraint G) :=
  fun e => Finset.univ.filter
    (fun q => e.1 ∈ walkOddSupport G (cycleCompleteWitnessWalk G hG q))

theorem cycleComplete_incidenceCount_eq [Nonempty V]
    (hG : G.Preconnected) (A : Finset G.edgeFinset)
    (q : CycleCompleteConstraint G) :
    plaquetteIncidenceCount (cycleCompleteIncidence G hG) A q =
      (A.filter (fun e =>
        e.1 ∈ walkOddSupport G (cycleCompleteWitnessWalk G hG q))).card := by
  rw [plaquetteIncidenceCount, card_filter]
  apply Finset.sum_congr rfl
  intro e he
  simp [cycleCompleteIncidence]


def graphEdgeEmbedding : G.edgeFinset ↪ Sym2 V :=
  Function.Embedding.subtype _


def cycleCompleteEdgeSet (A : Finset G.edgeFinset) : Finset (Sym2 V) :=
  A.map (graphEdgeEmbedding G)

theorem cycleCompleteEdgeSet_subset (A : Finset G.edgeFinset) :
    cycleCompleteEdgeSet G A ⊆ G.edgeFinset := by
  intro e he
  rw [cycleCompleteEdgeSet, Finset.mem_map] at he
  obtain ⟨p, _, rfl⟩ := he
  exact p.2

theorem cycleComplete_incidence_even_iff_walkParity [Nonempty V]
    (hG : G.Preconnected) (A : Finset G.edgeFinset)
    (q : CycleCompleteConstraint G) :
    Even (plaquetteIncidenceCount (cycleCompleteIncidence G hG) A q) ↔
      walkParity G (cycleCompleteEdgeSet G A)
        (cycleCompleteWitnessWalk G hG q) = false := by
  rw [cycleComplete_incidenceCount_eq]
  rw [← even_filter_walkOddSupport_iff_walkParity_false G
    (cycleCompleteEdgeSet G A) (cycleCompleteWitnessWalk G hG q)]
  apply iff_of_eq
  congr 1
  rw [cycleCompleteEdgeSet, Finset.filter_map, Finset.card_map]
  rfl



theorem cycleComplete_isClosed_iff_mem_cutSpace [Nonempty V]
    (hG : G.Preconnected) (A : Finset G.edgeFinset) :
    IsClosedPlaquetteSet (cycleCompleteIncidence G hG) A ↔
      cycleCompleteEdgeSet G A ∈ cutSpace G := by
  constructor
  · intro hclosed
    by_contra hnot
    let q : CycleCompleteConstraint G :=
      ⟨cycleCompleteEdgeSet G A, cycleCompleteEdgeSet_subset G A, hnot⟩
    have heven := hclosed q
    have hfalse : walkParity G (cycleCompleteEdgeSet G A)
        (cycleCompleteWitnessWalk G hG q) = false :=
      (cycleComplete_incidence_even_iff_walkParity G hG A q).mp heven
    have htrue := cycleCompleteWitnessWalk_odd G hG q
    rw [htrue] at hfalse
    simp at hfalse
  · intro hcut q
    apply (cycleComplete_incidence_even_iff_walkParity G hG A q).mpr
    exact evenOnCycles_of_mem_cutSpace hcut _ _


def cycleCompleteEdgePreimage (delta : Finset (Sym2 V)) :
    Finset G.edgeFinset :=
  G.edgeFinset.attach.filter (fun e => e.1 ∈ delta)

@[simp] theorem mem_cycleCompleteEdgePreimage
    (delta : Finset (Sym2 V)) (p : G.edgeFinset) :
    p ∈ cycleCompleteEdgePreimage G delta ↔ p.1 ∈ delta := by
  simp [cycleCompleteEdgePreimage]

theorem cycleCompleteEdgeSet_preimage
    {delta : Finset (Sym2 V)} (hdelta : delta ⊆ G.edgeFinset) :
    cycleCompleteEdgeSet G (cycleCompleteEdgePreimage G delta) = delta := by
  ext e
  constructor
  · intro he
    rw [cycleCompleteEdgeSet, Finset.mem_map] at he
    obtain ⟨p, hp, rfl⟩ := he
    exact (mem_cycleCompleteEdgePreimage G delta p).mp hp
  · intro he
    rw [cycleCompleteEdgeSet, Finset.mem_map]
    exact ⟨⟨e, hdelta he⟩,
      (mem_cycleCompleteEdgePreimage G delta _).mpr he, rfl⟩

theorem cycleCompleteEdgePreimage_set (A : Finset G.edgeFinset) :
    cycleCompleteEdgePreimage G (cycleCompleteEdgeSet G A) = A := by
  ext p
  rw [mem_cycleCompleteEdgePreimage, cycleCompleteEdgeSet, Finset.mem_map]
  constructor
  · rintro ⟨q, hq, hqp⟩
    have : q = p := Subtype.ext hqp
    simpa [this] using hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem cutSpace_member_subset {delta : Finset (Sym2 V)}
    (hdelta : delta ∈ cutSpace G) : delta ⊆ G.edgeFinset := by
  rw [cutSpace, Finset.mem_image] at hdelta
  obtain ⟨s, _, rfl⟩ := hdelta
  exact Finset.filter_subset _ _

theorem mem_cycleCompleteClosedFamily_iff [Nonempty V]
    (hG : G.Preconnected) (A : Finset G.edgeFinset) :
    A ∈ gaugeClosedSurfaceFamily (cycleCompleteIncidence G hG) ↔
      IsClosedPlaquetteSet (cycleCompleteIncidence G hG) A := by
  unfold gaugeClosedSurfaceFamily
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Finset.mem_powerset.mpr
      (by intro p hp; exact Finset.mem_attach _ _), h⟩



noncomputable def cycleCompleteSurfaceEquiv [Nonempty V]
    (hG : G.Preconnected) :
    {A : Finset G.edgeFinset //
        A ∈ gaugeClosedSurfaceFamily (cycleCompleteIncidence G hG)} ≃
      {delta : Finset (Sym2 V) // delta ∈ cutSpace G} where
  toFun A := ⟨cycleCompleteEdgeSet G A.1,
    (cycleComplete_isClosed_iff_mem_cutSpace G hG A.1).mp
      ((mem_cycleCompleteClosedFamily_iff G hG A.1).mp A.2)⟩
  invFun delta := ⟨cycleCompleteEdgePreimage G delta.1, by
    apply (mem_cycleCompleteClosedFamily_iff G hG _).mpr
    apply (cycleComplete_isClosed_iff_mem_cutSpace G hG _).mpr
    rw [cycleCompleteEdgeSet_preimage G]
    · exact delta.2
    · exact cutSpace_member_subset G delta.2⟩
  left_inv A := by
    apply Subtype.ext
    exact cycleCompleteEdgePreimage_set G A.1
  right_inv delta := by
    apply Subtype.ext
    apply cycleCompleteEdgeSet_preimage G
    exact cutSpace_member_subset G delta.2

@[simp] theorem cycleCompleteSurfaceEquiv_apply [Nonempty V]
    (hG : G.Preconnected)
    (A : {A : Finset G.edgeFinset //
      A ∈ gaugeClosedSurfaceFamily (cycleCompleteIncidence G hG)}) :
    (cycleCompleteSurfaceEquiv G hG A).1 = cycleCompleteEdgeSet G A.1 :=
  rfl

theorem cycleCompleteEdgeSet_eq_dualPlaquetteMap
    (A : Finset G.edgeFinset) :
    cycleCompleteEdgeSet G A =
      A.map (dualPlaquetteEmbedding (Equiv.refl G.edgeFinset)) := by
  rfl



theorem cycleComplete_gaugePartition_isingDuality [Nonempty V]
    (hG : G.Preconnected) (K : G.edgeFinset → ℝ)
    (hK : ∀ p, 0 < K p) :
    (Real.exp (∑ e ∈ G.edgeFinset,
          dualIsingCoupling (Equiv.refl G.edgeFinset) K e) * 2) *
        gaugePartition (cycleCompleteIncidence G hG) K =
      ((2 : ℝ) ^ Fintype.card (CycleCompleteConstraint G) *
          ∏ p : G.edgeFinset, Real.cosh (K p)) *
        ZJ G.edgeFinset
          (dualIsingCoupling (Equiv.refl G.edgeFinset) K) (fun _ => 0) := by
  apply gaugePartition_isingDuality hG
    (cycleCompleteIncidence G hG) K hK
    (Equiv.refl G.edgeFinset) (cycleCompleteSurfaceEquiv G hG)
  intro A
  exact cycleCompleteEdgeSet_eq_dualPlaquetteMap G A.1



theorem cycleComplete_gaugeWilsonExpectation_eq_dualDisorderRatio [Nonempty V]
    (hG : G.Preconnected) (K : G.edgeFinset → ℝ)
    (hK : ∀ p, 0 < K p)
    (L : Finset (CycleCompleteConstraint G))
    (D : Finset G.edgeFinset)
    (hD : HasWilsonBoundary (cycleCompleteIncidence G hG) D L) :
    gaugeWilsonExpectation (cycleCompleteIncidence G hG) K L =
      (∑ gamma ∈ shiftedDualCutFamily (G := G)
          (D.map (dualPlaquetteEmbedding (Equiv.refl G.edgeFinset))),
          ∏ e ∈ gamma, Real.exp (-2 * dualIsingCoupling
            (Equiv.refl G.edgeFinset) K e)) /
        (∑ delta ∈ cutSpace G,
          ∏ e ∈ delta, Real.exp (-2 * dualIsingCoupling
            (Equiv.refl G.edgeFinset) K e)) := by
  apply gaugeWilsonExpectation_eq_dualDisorderRatio_of_sheet
    (cycleCompleteIncidence G hG) K hK L (Equiv.refl G.edgeFinset)
    (cycleCompleteSurfaceEquiv G hG)
    (fun A => cycleCompleteEdgeSet_eq_dualPlaquetteMap G A.1) D hD

end

end StatMech.FrontierA
