/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Foundations.FractionalHall
import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers









namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveStrictRouteFractionalHallDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



def LPReplicaAggregateRankFiveStrictRouteRelated
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q) : Prop :=
  ∃ d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z),
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
      G sites hsite q hcard z d = y

local instance lpReplicaAggregateRankFiveStrictRouteRelatedDecidable
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    DecidableRel
      (LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard) :=
  fun _ _ => Classical.propDecidable _


noncomputable def LPReplicaAggregateRankFiveStrictRouteWeight
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q) : Real := by
  classical
  exact if LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z y then
    ((lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z).card : Real)⁻¹
  else 0

theorem LPReplicaAggregateRankFiveStrictRouteWeight_nonneg
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    0 ≤ LPReplicaAggregateRankFiveStrictRouteWeight
      G sites hsite q hcard z y := by
  classical
  unfold LPReplicaAggregateRankFiveStrictRouteWeight
  split
  · positivity
  · exact le_rfl

theorem LPReplicaAggregateRankFiveStrictRouteWeight_eq_zero_of_not_related
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (hnot : ¬ LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z y) :
    LPReplicaAggregateRankFiveStrictRouteWeight
      G sites hsite q hcard z y = 0 := by
  classical
  simp [LPReplicaAggregateRankFiveStrictRouteWeight, hnot]



noncomputable def LPReplicaAggregateRankFiveStrictRouteIncomingDegree
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (degree : Nat) (y : LPReplicaAggregateDecoratedTarget G sites q) :
    Finset (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) := by
  classical
  exact Finset.univ.filter fun z =>
    LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard z y ∧
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card = degree

theorem mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (degree : Nat) (y : LPReplicaAggregateDecoratedTarget G sites q)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard degree y ↔
      LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z y ∧
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
          G sites hsite q z).card = degree := by
  classical
  simp [LPReplicaAggregateRankFiveStrictRouteIncomingDegree]



noncomputable def LPReplicaAggregateRankFiveStrictRouteIncoming
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    Finset (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) := by
  classical
  exact Finset.univ.filter fun z =>
    LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z y

theorem mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    z ∈ LPReplicaAggregateRankFiveStrictRouteIncoming
        G sites hsite q hcard y ↔
      LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard z y := by
  classical
  simp [LPReplicaAggregateRankFiveStrictRouteIncoming]



theorem LPReplicaAggregateRankFiveStrictRouteIncomingDegree_subset_incoming
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (degree : Nat) (y : LPReplicaAggregateDecoratedTarget G sites q) :
    LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard degree y ⊆
      LPReplicaAggregateRankFiveStrictRouteIncoming
        G sites hsite q hcard y := by
  intro z hz
  rw [mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff]
  exact (mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff
    G sites hsite q hcard degree y z).mp hz |>.1

set_option maxHeartbeats 8000000 in



theorem LPReplicaAggregateRankFiveStrictRouteIncoming_card_le_candidates
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z))
    (hzd :
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
        G sites hsite q hcard z d = y) :
    (LPReplicaAggregateRankFiveStrictRouteIncoming
        G sites hsite q hcard y).card ≤
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card := by
  classical
  let Incoming := LPReplicaAggregateRankFiveStrictRouteIncoming
    G sites hsite q hcard y
  have hrelated (w : ↑Incoming) :
      LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard w.1 y :=
    (mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff
      G sites hsite q hcard y w.1).mp w.2
  let route (w : ↑Incoming) :
      ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q w.1) := Classical.choose (hrelated w)
  have hroute (w : ↑Incoming) :
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
        G sites hsite q hcard w.1 (route w) = y :=
    Classical.choose_spec (hrelated w)
  have htransfer (w : ↑Incoming) :
      ∃ e : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
          G sites hsite q z),
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
            G sites hsite q z e =
          lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
            G sites hsite q w.1 (route w) := by
    have hw :=
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_spatialWitness
        G sites hsite q hcard w.1 (route w)
    rw [hroute w, ← hzd] at hw
    exact
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidate_of_spatialWitness
        G sites hsite q hcard z d _ hw
  let encode (w : ↑Incoming) :
      ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z) := Classical.choose (htransfer w)
  have hencode (w : ↑Incoming) :
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
          G sites hsite q z (encode w) =
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
          G sites hsite q w.1 (route w) :=
    Classical.choose_spec (htransfer w)
  have hinjective : Function.Injective encode := by
    intro w v henc
    apply Subtype.ext
    apply
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSource_eq_of_spatialSlot_eq_of_target_eq
        G sites hsite q hcard w.1 v.1 (route w) (route v)
    · rw [← hencode w, ← hencode v, henc]
    · exact (hroute w).trans (hroute v).symm
  have hcardFiber : Fintype.card ↑Incoming ≤
      Fintype.card
        ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
          G sites hsite q z) :=
    Fintype.card_le_of_injective encode hinjective
  simpa only [Fintype.card_coe] using hcardFiber


theorem LPReplicaAggregateRankFiveStrictRouteWeight_sum_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    ∑ y : LPReplicaAggregateDecoratedTarget G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight
          G sites hsite q hcard z y = 1 := by
  classical
  let C :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z
  let f : ↑C -> LPReplicaAggregateDecoratedTarget G sites q :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
      G sites hsite q hcard z
  let R : Finset (LPReplicaAggregateDecoratedTarget G sites q) :=
    Finset.univ.image f
  have hf : Function.Injective f :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_injective
      G sites hsite q hcard z
  have hrelated (y : LPReplicaAggregateDecoratedTarget G sites q) :
      LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z y ↔ y ∈ R := by
    simp only [LPReplicaAggregateRankFiveStrictRouteRelated, R,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d, rfl⟩
    · rintro ⟨d, hd⟩
      exact ⟨d, hd⟩
  have hcardR : R.card = C.card := by
    change (Finset.univ.image f).card = C.card
    rw [Finset.card_image_iff.mpr]
    · simp
    · exact fun _ _ _ _ h => hf h
  have hpos : 0 < C.card :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_pos
      G sites hsite q hcard z
  calc
    (∑ y : LPReplicaAggregateDecoratedTarget G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight
          G sites hsite q hcard z y) =
        ∑ _y ∈ R, (C.card : Real)⁻¹ := by
      change ∑ y, (if
        LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z y then (C.card : Real)⁻¹ else 0) = _
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          hrelated]
      · intro y _
        rfl
    _ = (R.card : Real) * (C.card : Real)⁻¹ := by simp
    _ = (C.card : Real) * (C.card : Real)⁻¹ := by rw [hcardR]
    _ = 1 := by
      exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hpos))




theorem LPReplicaAggregateRankFiveStrictRouteWeight_sum_source
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    (∑ z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight
          G sites hsite q hcard z y) =
      ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 1 y).card : Real) +
        ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
          G sites hsite q hcard 2 y).card : Real) / 2 := by
  classical
  have hpoint
      (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
      LPReplicaAggregateRankFiveStrictRouteWeight
          G sites hsite q hcard z y =
        (if z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree
            G sites hsite q hcard 1 y then 1 else 0) +
          (if z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree
              G sites hsite q hcard 2 y then (2 : Real)⁻¹ else 0) := by
    have hdegree :=
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_eq_one_or_two
        G sites hsite q hcard z
    rcases hdegree with hdegree | hdegree
    · by_cases hrelated : LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z y
      · simp [LPReplicaAggregateRankFiveStrictRouteWeight,
          LPReplicaAggregateRankFiveStrictRouteIncomingDegree,
          hrelated, hdegree]
      · simp [LPReplicaAggregateRankFiveStrictRouteWeight,
          LPReplicaAggregateRankFiveStrictRouteIncomingDegree,
          hrelated, hdegree]
    · by_cases hrelated : LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z y
      · simp [LPReplicaAggregateRankFiveStrictRouteWeight,
          LPReplicaAggregateRankFiveStrictRouteIncomingDegree,
          hrelated, hdegree]
      · simp [LPReplicaAggregateRankFiveStrictRouteWeight,
          LPReplicaAggregateRankFiveStrictRouteIncomingDegree,
          hrelated, hdegree]
  calc
    (∑ z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight
          G sites hsite q hcard z y) =
        ∑ z,
          ((if z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree
              G sites hsite q hcard 1 y then 1 else 0) +
            (if z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree
                G sites hsite q hcard 2 y then (2 : Real)⁻¹ else 0)) := by
      apply Finset.sum_congr rfl
      intro z _
      exact hpoint z
    _ = (∑ z, if z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree
            G sites hsite q hcard 1 y then (1 : Real) else 0) +
        ∑ z, if z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree
            G sites hsite q hcard 2 y then (2 : Real)⁻¹ else 0 :=
      Finset.sum_add_distrib
    _ = ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
          G sites hsite q hcard 1 y).card : Real) +
        ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
          G sites hsite q hcard 2 y).card : Real) / 2 := by
      simp [div_eq_mul_inv]



def LPReplicaAggregateRankFiveStrictRouteTargetLoad
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) : Prop :=
  ∀ y : LPReplicaAggregateDecoratedTarget G sites q,
    ∑ z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q,
      LPReplicaAggregateRankFiveStrictRouteWeight
        G sites hsite q hcard z y ≤ 1


theorem LPReplicaAggregateRankFiveStrictRouteTargetLoad_iff_integer
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    LPReplicaAggregateRankFiveStrictRouteTargetLoad
        G sites hsite q hcard ↔
      ∀ y : LPReplicaAggregateDecoratedTarget G sites q,
        2 * (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
          G sites hsite q hcard 1 y).card +
          (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
            G sites hsite q hcard 2 y).card ≤ 2 := by
  constructor
  · intro hload y
    have hy := hload y
    rw [LPReplicaAggregateRankFiveStrictRouteWeight_sum_source] at hy
    have hreal :
        (2 : Real) *
            ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
              G sites hsite q hcard 1 y).card : Real) +
          ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
            G sites hsite q hcard 2 y).card : Real) ≤ 2 := by
      linarith [hy]
    exact_mod_cast hreal
  · intro hinteger
    unfold LPReplicaAggregateRankFiveStrictRouteTargetLoad
    intro y
    rw [LPReplicaAggregateRankFiveStrictRouteWeight_sum_source]
    have hreal :
        (2 : Real) *
            ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
              G sites hsite q hcard 1 y).card : Real) +
          ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
            G sites hsite q hcard 2 y).card : Real) ≤ 2 := by
      exact_mod_cast hinteger y
    linarith




theorem LPReplicaAggregateRankFiveStrictRouteTargetLoad_iff_classification
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    LPReplicaAggregateRankFiveStrictRouteTargetLoad
        G sites hsite q hcard ↔
      ∀ y : LPReplicaAggregateDecoratedTarget G sites q,
        ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
              G sites hsite q hcard 1 y).card = 0 ∧
            (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
              G sites hsite q hcard 2 y).card ≤ 2) ∨
          ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
                G sites hsite q hcard 1 y).card = 1 ∧
            (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
              G sites hsite q hcard 2 y).card = 0) := by
  rw [LPReplicaAggregateRankFiveStrictRouteTargetLoad_iff_integer]
  constructor
  · intro h y
    specialize h y
    omega
  · intro h y
    rcases h y with h | h <;> omega



theorem LPReplicaAggregateRankFiveStrictRouteIncoming_classification
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
          G sites hsite q hcard 1 y).card = 0 ∧
        (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
          G sites hsite q hcard 2 y).card ≤ 2) ∨
      ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
            G sites hsite q hcard 1 y).card = 1 ∧
        (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
          G sites hsite q hcard 2 y).card = 0) := by
  classical
  let D1 := LPReplicaAggregateRankFiveStrictRouteIncomingDegree
    G sites hsite q hcard 1 y
  let D2 := LPReplicaAggregateRankFiveStrictRouteIncomingDegree
    G sites hsite q hcard 2 y
  let Incoming := LPReplicaAggregateRankFiveStrictRouteIncoming
    G sites hsite q hcard y
  have hsub1 : D1 ⊆ Incoming := by
    exact LPReplicaAggregateRankFiveStrictRouteIncomingDegree_subset_incoming
      G sites hsite q hcard 1 y
  have hsub2 : D2 ⊆ Incoming := by
    exact LPReplicaAggregateRankFiveStrictRouteIncomingDegree_subset_incoming
      G sites hsite q hcard 2 y
  by_cases h1 : D1.Nonempty
  · obtain ⟨z, hz1⟩ := h1
    have hzData :=
      (mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff
        G sites hsite q hcard 1 y z).mp hz1
    obtain ⟨d, hdTarget⟩ := hzData.1
    have hIncoming :=
      LPReplicaAggregateRankFiveStrictRouteIncoming_card_le_candidates
        G sites hsite q hcard y z d hdTarget
    change Incoming.card ≤
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card at hIncoming
    rw [hzData.2] at hIncoming
    have hD1le : D1.card ≤ 1 :=
      (Finset.card_le_card hsub1).trans hIncoming
    have hD1pos : 0 < D1.card := Finset.card_pos.mpr ⟨z, hz1⟩
    have hD1 : D1.card = 1 := by omega
    have hD2 : D2.card = 0 := by
      by_contra hne
      have hpos : 0 < D2.card := Nat.pos_of_ne_zero hne
      obtain ⟨w, hw2⟩ := Finset.card_pos.mp hpos
      have hwData :=
        (mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff
          G sites hsite q hcard 2 y w).mp hw2
      have hwz : w = z := Finset.card_le_one.mp hIncoming
        w (hsub2 hw2) z (hsub1 hz1)
      subst w
      omega
    exact Or.inr ⟨hD1, hD2⟩
  · have hD1 : D1.card = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp h1]
      rfl
    have hD2 : D2.card ≤ 2 := by
      by_cases h2 : D2.Nonempty
      · obtain ⟨z, hz2⟩ := h2
        have hzData :=
          (mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff
            G sites hsite q hcard 2 y z).mp hz2
        obtain ⟨d, hdTarget⟩ := hzData.1
        have hIncoming :=
          LPReplicaAggregateRankFiveStrictRouteIncoming_card_le_candidates
            G sites hsite q hcard y z d hdTarget
        change Incoming.card ≤
          (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
            G sites hsite q z).card at hIncoming
        rw [hzData.2] at hIncoming
        exact (Finset.card_le_card hsub2).trans hIncoming
      · rw [Finset.not_nonempty_iff_eq_empty.mp h2]
        simp
    exact Or.inl ⟨hD1, hD2⟩


theorem lpReplicaAggregateRankFiveStrictRouteTargetLoad
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    LPReplicaAggregateRankFiveStrictRouteTargetLoad
      G sites hsite q hcard := by
  rw [LPReplicaAggregateRankFiveStrictRouteTargetLoad_iff_classification]
  exact LPReplicaAggregateRankFiveStrictRouteIncoming_classification
    G sites hsite q hcard



theorem LPReplicaAggregateRankFiveStrictRouteHall_of_targetLoad
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (hload : LPReplicaAggregateRankFiveStrictRouteTargetLoad
      G sites hsite q hcard) :
    ∀ sources : Finset
        (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q),
      sources.card ≤
        (Finset.univ.filter fun target :
          LPReplicaAggregateDecoratedTarget G sites q =>
            ∃ source ∈ sources,
              LPReplicaAggregateRankFiveStrictRouteRelated
                G sites hsite q hcard source target).card := by
  classical
  apply finiteRelationHall_of_fractionalWeights
    (LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard)
    (LPReplicaAggregateRankFiveStrictRouteWeight
      G sites hsite q hcard)
  · exact LPReplicaAggregateRankFiveStrictRouteWeight_nonneg
      G sites hsite q hcard
  · exact LPReplicaAggregateRankFiveStrictRouteWeight_eq_zero_of_not_related
      G sites hsite q hcard
  · intro source
    rw [LPReplicaAggregateRankFiveStrictRouteWeight_sum_target
      G sites hsite q hcard source]
  · exact hload



theorem LPReplicaAggregateRankFiveStrictRouteHall
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    ∀ sources : Finset
        (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q),
      sources.card ≤
        (Finset.univ.filter fun target :
          LPReplicaAggregateDecoratedTarget G sites q =>
            ∃ source ∈ sources,
              LPReplicaAggregateRankFiveStrictRouteRelated
                G sites hsite q hcard source target).card :=
  LPReplicaAggregateRankFiveStrictRouteHall_of_targetLoad
    G sites hsite q hcard
      (lpReplicaAggregateRankFiveStrictRouteTargetLoad
        G sites hsite q hcard)

end

end StatMech.Ising
