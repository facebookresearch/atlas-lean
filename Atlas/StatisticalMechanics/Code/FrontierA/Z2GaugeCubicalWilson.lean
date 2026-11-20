/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.FrontierA.Z2GaugeWilsonAffine

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace StatMech.FrontierA

noncomputable section

local instance cubicalPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p


structure CubicalVertex (a b c : Nat) where
  x : Fin (a + 1)
  y : Fin (b + 1)
  z : Fin (c + 1)
  deriving DecidableEq, Fintype



inductive CubicalEdge (a b c : Nat)
  | x : Fin a → Fin (b + 1) → Fin (c + 1) → CubicalEdge a b c
  | y : Fin (a + 1) → Fin b → Fin (c + 1) → CubicalEdge a b c
  | z : Fin (a + 1) → Fin (b + 1) → Fin c → CubicalEdge a b c
  deriving DecidableEq, Fintype


inductive CubicalPlaquette (a b c : Nat)
  | xy : Fin a → Fin b → Fin (c + 1) → CubicalPlaquette a b c
  | xz : Fin a → Fin (b + 1) → Fin c → CubicalPlaquette a b c
  | yz : Fin (a + 1) → Fin b → Fin c → CubicalPlaquette a b c
  deriving DecidableEq, Fintype


def cubicalPlaquetteIncidence {a b c : Nat} :
    CubicalPlaquette a b c → Finset (CubicalEdge a b c)
  | .xy i j k =>
      {.x i j.castSucc k, .x i j.succ k,
        .y i.castSucc j k, .y i.succ j k}
  | .xz i j k =>
      {.x i j k.castSucc, .x i j k.succ,
        .z i.castSucc j k, .z i.succ j k}
  | .yz i j k =>
      {.y i j k.castSucc, .y i j k.succ,
        .z i j.castSucc k, .z i j.succ k}


def cubicalEdgeEndpoints {a b c : Nat} :
    CubicalEdge a b c → Finset (CubicalVertex a b c)
  | .x i j k =>
      {⟨i.castSucc, j, k⟩, ⟨i.succ, j, k⟩}
  | .y i j k =>
      {⟨i, j.castSucc, k⟩, ⟨i, j.succ, k⟩}
  | .z i j k =>
      {⟨i, j, k.castSucc⟩, ⟨i, j, k.succ⟩}


def cubicalVertexStar {a b c : Nat} (v : CubicalVertex a b c) :
    Finset (CubicalEdge a b c) :=
  Finset.univ.filter fun e => v ∈ cubicalEdgeEndpoints e



theorem cubical_hasEvenPlaquetteStarIncidence {a b c : Nat} :
    HasEvenPlaquetteStarIncidence
      (cubicalPlaquetteIncidence (a := a) (b := b) (c := c))
      cubicalVertexStar := by
  rintro ⟨x, y, z⟩ p
  simp only [cubicalVertexStar, Finset.inter_filter, Finset.inter_univ,
    Finset.card_filter]
  cases p with
  | xy i j k =>
      have hi : i.castSucc ≠ i.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      have hj : j.castSucc ≠ j.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      by_cases h00 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.castSucc, j.castSucc, k⟩
      · rw [h00]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h10 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.succ, j.castSucc, k⟩
      · rw [h10]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h01 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.castSucc, j.succ, k⟩
      · rw [h01]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h11 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.succ, j.succ, k⟩
      · rw [h11]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      simp [cubicalPlaquetteIncidence, cubicalEdgeEndpoints, hi, hj]
      all_goals split_ifs <;> norm_num <;> aesop
  | xz i j k =>
      have hi : i.castSucc ≠ i.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      have hk : k.castSucc ≠ k.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      by_cases h00 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.castSucc, j, k.castSucc⟩
      · rw [h00]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h10 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.succ, j, k.castSucc⟩
      · rw [h10]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h01 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.castSucc, j, k.succ⟩
      · rw [h01]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h11 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.succ, j, k.succ⟩
      · rw [h11]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      simp [cubicalPlaquetteIncidence, cubicalEdgeEndpoints, hi, hk]
      all_goals split_ifs <;> norm_num <;> aesop
  | yz i j k =>
      have hj : j.castSucc ≠ j.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      have hk : k.castSucc ≠ k.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      by_cases h00 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i, j.castSucc, k.castSucc⟩
      · rw [h00]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h10 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i, j.succ, k.castSucc⟩
      · rw [h10]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h01 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i, j.castSucc, k.succ⟩
      · rw [h01]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h11 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i, j.succ, k.succ⟩
      · rw [h11]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      simp [cubicalPlaquetteIncidence, cubicalEdgeEndpoints, hj, hk]
      all_goals split_ifs <;> norm_num <;> aesop



theorem cubicalGaugeAction_localGaugeTransform_eq {a b c : Nat}
    (K : CubicalPlaquette a b c → Real)
    (v : CubicalVertex a b c)
    (omega : GaugeConfig (CubicalEdge a b c)) :
    gaugeAction cubicalPlaquetteIncidence K
        (localGaugeTransform cubicalVertexStar v omega) =
      gaugeAction cubicalPlaquetteIncidence K omega :=
  gaugeAction_localGaugeTransform_eq cubicalPlaquetteIncidence
    cubicalVertexStar cubical_hasEvenPlaquetteStarIncidence K v omega




def gaugeSurfaceBoundary {E P : Type*} [Fintype E] [DecidableEq E]
    [DecidableEq P] (incidence : P → Finset E) (A : Finset P) : Finset E :=
  Finset.univ.filter fun e => ¬ Even (plaquetteIncidenceCount incidence A e)

@[simp] theorem mem_gaugeSurfaceBoundary {E P : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq P]
    (incidence : P → Finset E) (A : Finset P) (e : E) :
    e ∈ gaugeSurfaceBoundary incidence A ↔
      ¬ Even (plaquetteIncidenceCount incidence A e) := by
  simp [gaugeSurfaceBoundary]



theorem isClosedPlaquetteSet_iff_gaugeSurfaceBoundary_eq_empty
    {E P : Type*} [Fintype E] [DecidableEq E] [DecidableEq P]
    (incidence : P → Finset E) (A : Finset P) :
    IsClosedPlaquetteSet incidence A ↔
      gaugeSurfaceBoundary incidence A = ∅ := by
  constructor
  · intro hclosed
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨e, he⟩
    exact (mem_gaugeSurfaceBoundary incidence A e).mp he (hclosed e)
  · intro hempty e
    by_contra hodd
    have hmem : e ∈ gaugeSurfaceBoundary incidence A := by
      simpa using hodd
    rw [hempty] at hmem
    simp at hmem



theorem hasWilsonBoundary_gaugeSurfaceBoundary {E P : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq P]
    (incidence : P → Finset E) (A : Finset P) :
    HasWilsonBoundary incidence A (gaugeSurfaceBoundary incidence A) := by
  intro e
  by_cases heven : Even (plaquetteIncidenceCount incidence A e)
  · have hnotmem : e ∉ gaugeSurfaceBoundary incidence A := by
      simpa using heven
    simp only [hnotmem, if_false, add_zero]
    exact heven
  · have hmem : e ∈ gaugeSurfaceBoundary incidence A := by
      simpa using heven
    simp only [hmem, if_true]
    exact Nat.even_add_one.mpr heven



theorem gaugeSurfaceBoundary_singleton {E P : Type*}
    [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P]
    (incidence : P → Finset E) (p : P) :
    gaugeSurfaceBoundary incidence {p} = incidence p := by
  ext e
  rw [mem_gaugeSurfaceBoundary, plaquetteIncidenceCount_eq_filter_card]
  by_cases he : e ∈ incidence p
  · have hfilter : ({q ∈ ({p} : Finset P) | e ∈ incidence q}) = {p} := by
      apply Finset.filter_eq_self.mpr
      intro q hq
      simp only [mem_singleton] at hq
      subst q
      exact he
    rw [hfilter]
    norm_num [he]
  · have hfilter : ({q ∈ ({p} : Finset P) | e ∈ incidence q}) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro q hq
      simp only [mem_singleton] at hq
      subst q
      exact he
    rw [hfilter]
    norm_num [he]


def cubicalXYSheet {a b c : Nat} (k : Fin (c + 1)) :
    Finset (CubicalPlaquette a b c) :=
  (Finset.univ : Finset (Fin a × Fin b)).image
    fun ij => CubicalPlaquette.xy ij.1 ij.2 k




def cubicalXYLoop {a b c : Nat} (k : Fin (c + 1)) :
    Finset (CubicalEdge a b c) :=
  gaugeSurfaceBoundary cubicalPlaquetteIncidence (cubicalXYSheet k)



theorem cubicalXYSheet_hasWilsonBoundary {a b c : Nat}
    (k : Fin (c + 1)) :
    HasWilsonBoundary (cubicalPlaquetteIncidence (a := a) (b := b) (c := c))
      (cubicalXYSheet k) (cubicalXYLoop k) :=
  hasWilsonBoundary_gaugeSurfaceBoundary _ _



theorem cubicalXYWilsonExpectation_eq_dualDisorderRatio
    {a b c : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c → Real)
    (hK : ∀ p, 0 < K p)
    (dualEdge : CubicalPlaquette a b c ≃ G.edgeFinset)
    (closedEquiv :
      {A : Finset (CubicalPlaquette a b c) //
          A ∈ gaugeClosedSurfaceFamily cubicalPlaquetteIncidence} ≃
        {delta : Finset (Sym2 V) // delta ∈ StatMech.Ising.cutSpace G})
    (hclosed : ∀ A,
      (closedEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge)) :
    gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) =
      (∑ gamma ∈ shiftedDualCutFamily (G := G)
          ((cubicalXYSheet k).map (dualPlaquetteEmbedding dualEdge)),
          ∏ e ∈ gamma,
            Real.exp (-2 * dualIsingCoupling dualEdge K e)) /
        (∑ delta ∈ StatMech.Ising.cutSpace G,
          ∏ e ∈ delta,
            Real.exp (-2 * dualIsingCoupling dualEdge K e)) := by
  apply gaugeWilsonExpectation_eq_dualDisorderRatio_of_sheet
    cubicalPlaquetteIncidence K hK (cubicalXYLoop k) dualEdge
    closedEquiv hclosed (cubicalXYSheet k)
  exact cubicalXYSheet_hasWilsonBoundary k

end

end StatMech.FrontierA
