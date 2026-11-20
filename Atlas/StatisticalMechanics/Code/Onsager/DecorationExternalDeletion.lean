/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationFormalSupport









namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_decPhaseBucketE
    (L : ℕ) [NeZero L] (decWeight : ons_DecEdge L → ℂ)
    (a b : Fin 2) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (n + 1) → ons_Dart L =>
        (∃ i, loop i = e) ∧
          ¬ ∃ j, loop j = ons_dartRev L e),
    ons_loopWeight
      (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)) loop

noncomputable def ons_decPhaseBucketN
    (L : ℕ) [NeZero L] (decWeight : ons_DecEdge L → ℂ)
    (a b : Fin 2) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (n + 1) → ons_Dart L =>
        ¬ (∃ i, loop i = e) ∧
          ¬ ∃ j, loop j = ons_dartRev L e),
    ons_loopWeight
      (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)) loop

noncomputable def ons_decMaskPhaseBucketE
    (L : ℕ) [NeZero L] (decWeight : ons_DecEdge L → ℂ)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (n + 1) → ons_Dart L =>
        (∃ i, loop i = e) ∧
          ¬ ∃ j, loop j = ons_dartRev L e),
    ons_loopWeight
      (ons_maskMatrix forbidden
        (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))) loop

noncomputable def ons_decMaskPhaseBucketN
    (L : ℕ) [NeZero L] (decWeight : ons_DecEdge L → ℂ)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (n + 1) → ons_Dart L =>
        ¬ (∃ i, loop i = e) ∧
          ¬ ∃ j, loop j = ons_dartRev L e),
    ons_loopWeight
      (ons_maskMatrix forbidden
      (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))) loop

def ons_scaleDecEdgeWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ)
    (edge : ons_DecEdge L) (t : ℂ) : ons_DecEdge L → ℂ :=
  fun f => if f = edge then t * decWeight f else decWeight f

@[simp] theorem ons_scaleDecEdgeWeight_external
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (t : ℂ) (e : ons_Dart L) :
    ons_scaleDecEdgeWeight decWeight
        s(e, ons_dartRev L e) t s(e, ons_dartRev L e) =
      t * decWeight s(e, ons_dartRev L e) := by
  simp [ons_scaleDecEdgeWeight]

@[simp] theorem ons_scaleDecEdgeWeight_chain
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (t : ℂ)
    (e : ons_Dart L) (site : ZMod L × ZMod L) (i : Fin 3) :
    ons_scaleDecEdgeWeight decWeight s(e, ons_dartRev L e) t
        (ons_decChainEdge site i) =
      decWeight (ons_decChainEdge site i) := by
  rw [ons_scaleDecEdgeWeight, if_neg]
  intro hedge
  apply ons_decChainEdge_not_external L site i
  exact ⟨e, hedge⟩

theorem ons_decTransitionWeight_scaleExternal
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (t : ℂ)
    (e d₂ d₁ : ons_Dart L) :
    ons_decTransitionWeight L
        (ons_scaleDecEdgeWeight decWeight
          s(e, ons_dartRev L e) t) d₂ d₁ =
      if d₁ = e ∨ d₁ = ons_dartRev L e then
        t * ons_decTransitionWeight L decWeight d₂ d₁
      else ons_decTransitionWeight L decWeight d₂ d₁ := by
  unfold ons_decTransitionWeight
  have hchain :
      (∏ i ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2,
        ons_scaleDecEdgeWeight decWeight
          s(e, ons_dartRev L e) t
          (ons_decChainEdge d₂.1 i)) =
        ∏ i ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2,
          decWeight (ons_decChainEdge d₂.1 i) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact ons_scaleDecEdgeWeight_chain
      L decWeight t e d₂.1 i
  rw [hchain]
  unfold ons_scaleDecEdgeWeight
  have hext :
      s(d₁, ons_dartRev L d₁) = s(e, ons_dartRev L e) ↔
        d₁ = e ∨ d₁ = ons_dartRev L e :=
    ons_externalDecoratedEdge_eq_iff L e d₁
  by_cases hd : d₁ = e ∨ d₁ = ons_dartRev L e
  · rw [if_pos (hext.mpr hd), if_pos hd]
    ring
  · rw [if_neg (fun h => hd (hext.mp h)), if_neg hd]

theorem ons_KWmatDecorationWeightedPhase_scaleExternal
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega u v t : ℂ) (e : ons_Dart L) :
    ons_KWmatDecorationWeightedPhase L
        (ons_scaleDecEdgeWeight decWeight
          s(e, ons_dartRev L e) t) omega u v =
      ons_scaleColumns
        ({e, ons_dartRev L e} : Finset (ons_Dart L)) t
        (ons_KWmatDecorationWeightedPhase L decWeight omega u v) := by
  ext d₂ d₁
  simp only [ons_KWmatDecorationWeightedPhase, ons_scaleColumns]
  rw [ons_decTransitionWeight_scaleExternal]
  by_cases hd : d₁ = e ∨ d₁ = ons_dartRev L e
  · simp only [hd, if_true, Finset.mem_insert,
      Finset.mem_singleton]
    split <;> ring
  · simp only [hd, if_false, Finset.mem_insert,
      Finset.mem_singleton]

theorem ons_decLoopSum_both_zero
    (L : ℕ) [NeZero L] [Fact (2 < L)] (n : ℕ)
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (e : ons_Dart L) :
    (∑ loop ∈ (Finset.univ :
        Finset (Fin (n + 1) → ons_Dart L)).filter
        (fun loop => (∃ i, loop i = e) ∧
          ∃ j, loop j = ons_dartRev L e),
      ons_loopWeight
        (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) loop) = 0 := by
  have hset :
      ((Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter
        (fun loop => (∃ i, loop i = e) ∧
          ∃ j, loop j = ons_dartRev L e)) =
        ons_loopSetBoth (n := n + 1) e (ons_dartRev L e) := by
    ext loop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ons_mem_loopSetBoth]
  rw [hset]
  exact ons_KWmatDecorationWeightedPhase_lemma5
    L decWeight ons_turnRoot ons_turnRoot_sq a b e

theorem ons_decMaskLoopSum_both_zero
    (L : ℕ) [NeZero L] [Fact (2 < L)] (n : ℕ)
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    (∑ loop ∈ (Finset.univ :
        Finset (Fin (n + 1) → ons_Dart L)).filter
        (fun loop => (∃ i, loop i = e) ∧
          ∃ j, loop j = ons_dartRev L e),
      ons_loopWeight
        (ons_maskMatrix forbidden
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) loop) = 0 := by
  have hset :
      ((Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter
        (fun loop => (∃ i, loop i = e) ∧
          ∃ j, loop j = ons_dartRev L e)) =
        ons_loopSetBoth (n := n + 1) e (ons_dartRev L e) := by
    ext loop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ons_mem_loopSetBoth]
  rw [hset]
  exact ons_KWmatDecorationWeightedPhase_mask_lemma5
    L decWeight ons_turnRoot ons_turnRoot_sq a b
      forbidden hforbidden e

theorem ons_decLoopSum_orientation_symm
    (L : ℕ) [NeZero L] [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (e : ons_Dart L) :
    (∑ loop ∈ Finset.univ.filter
        (fun loop : Fin n → ons_Dart L =>
          (∃ i, loop i = e) ∧
            ¬ ∃ j, loop j = ons_dartRev L e),
      ons_loopWeight
        (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) loop) =
      ∑ loop ∈ Finset.univ.filter
        (fun loop : Fin n → ons_Dart L =>
          (∃ i, loop i = ons_dartRev L e) ∧
            ¬ ∃ j, loop j = e),
      ons_loopWeight
        (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) loop := by
  refine Finset.sum_nbij' (ons_loopRev L) (ons_loopRev L)
    ?_ ?_ ?_ ?_ ?_
  · intro loop hloop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hloop ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hloop
    constructor
    · rw [ons_visits_loopRev, ons_dartRev_involutive L e]
      exact ⟨i, hie⟩
    · rwa [ons_visits_loopRev]
  · intro loop hloop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hloop ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hloop
    constructor
    · rw [ons_visits_loopRev]
      exact ⟨i, hie⟩
    · rwa [ons_visits_loopRev, ons_dartRev_involutive L e]
  · exact fun loop _ => ons_loopRev_involutive L n loop
  · exact fun loop _ => ons_loopRev_involutive L n loop
  · intro loop hloop
    exact (ons_loopWeight_KWmatDecorationWeightedPhase_loopRev
      L decWeight a b loop).symm

theorem ons_decMaskLoopSum_orientation_symm
    (L : ℕ) [NeZero L] [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    (∑ loop ∈ Finset.univ.filter
        (fun loop : Fin n → ons_Dart L =>
          (∃ i, loop i = e) ∧
            ¬ ∃ j, loop j = ons_dartRev L e),
      ons_loopWeight
        (ons_maskMatrix forbidden
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) loop) =
      ∑ loop ∈ Finset.univ.filter
        (fun loop : Fin n → ons_Dart L =>
          (∃ i, loop i = ons_dartRev L e) ∧
            ¬ ∃ j, loop j = e),
      ons_loopWeight
        (ons_maskMatrix forbidden
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) loop := by
  refine Finset.sum_nbij' (ons_loopRev L) (ons_loopRev L)
    ?_ ?_ ?_ ?_ ?_
  · intro loop hloop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hloop ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hloop
    constructor
    · rw [ons_visits_loopRev, ons_dartRev_involutive L e]
      exact ⟨i, hie⟩
    · rwa [ons_visits_loopRev]
  · intro loop hloop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hloop ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hloop
    constructor
    · rw [ons_visits_loopRev]
      exact ⟨i, hie⟩
    · rwa [ons_visits_loopRev, ons_dartRev_involutive L e]
  · exact fun loop _ => ons_loopRev_involutive L n loop
  · exact fun loop _ => ons_loopRev_involutive L n loop
  · intro loop hloop
    exact (ons_loopWeight_KWmatDecorationWeightedPhase_mask_loopRev
      L decWeight a b forbidden hforbidden loop).symm

theorem ons_decLoopSum_two_bucket
    (L : ℕ) [NeZero L] [Fact (2 < L)] {n : ℕ}
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (e : ons_Dart L) :
    (∑ loop : Fin (n + 1) → ons_Dart L,
      ons_loopWeight
        (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) loop) =
      2 * ons_decPhaseBucketE L decWeight a b e n +
        ons_decPhaseBucketN L decWeight a b e n := by
  let M := ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  let P : (Fin (n + 1) → ons_Dart L) → Prop :=
    fun loop => ∃ i, loop i = e
  let Q : (Fin (n + 1) → ons_Dart L) → Prop :=
    fun loop => ∃ j, loop j = ons_dartRev L e
  have hsplit := ons_sum_split_by_two P Q
    (fun loop => ons_loopWeight M loop)
  have hboth := ons_decLoopSum_both_zero
    L n decWeight a b e
  have hsymm := ons_decLoopSum_orientation_symm
    (L := L) (n := n + 1) decWeight a b e
  have hset :
      Finset.univ.filter
          (fun loop : Fin (n + 1) → ons_Dart L =>
            (∃ i, loop i = ons_dartRev L e) ∧
              ¬ ∃ j, loop j = e) =
        Finset.univ.filter
          (fun loop : Fin (n + 1) → ons_Dart L =>
            ¬ (∃ i, loop i = e) ∧
              ∃ j, loop j = ons_dartRev L e) := by
    ext loop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hset] at hsymm
  simp only [P, Q, M] at hsplit
  unfold ons_decPhaseBucketE ons_decPhaseBucketN
  linear_combination hsplit + hboth - hsymm

theorem ons_decMaskLoopSum_two_bucket
    (L : ℕ) [NeZero L] [Fact (2 < L)] {n : ℕ}
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    (∑ loop : Fin (n + 1) → ons_Dart L,
      ons_loopWeight
        (ons_maskMatrix forbidden
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) loop) =
      2 * ons_decMaskPhaseBucketE L decWeight a b forbidden e n +
        ons_decMaskPhaseBucketN L decWeight a b forbidden e n := by
  let M := ons_maskMatrix forbidden
    (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b))
  let P : (Fin (n + 1) → ons_Dart L) → Prop :=
    fun loop => ∃ i, loop i = e
  let Q : (Fin (n + 1) → ons_Dart L) → Prop :=
    fun loop => ∃ j, loop j = ons_dartRev L e
  have hsplit := ons_sum_split_by_two P Q
    (fun loop => ons_loopWeight M loop)
  have hboth := ons_decMaskLoopSum_both_zero
    L n decWeight a b forbidden hforbidden e
  have hsymm := ons_decMaskLoopSum_orientation_symm
    (L := L) (n := n + 1) decWeight a b
      forbidden hforbidden e
  have hset :
      Finset.univ.filter
          (fun loop : Fin (n + 1) → ons_Dart L =>
            (∃ i, loop i = ons_dartRev L e) ∧
              ¬ ∃ j, loop j = e) =
        Finset.univ.filter
          (fun loop : Fin (n + 1) → ons_Dart L =>
            ¬ (∃ i, loop i = e) ∧
              ∃ j, loop j = ons_dartRev L e) := by
    ext loop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hset] at hsymm
  simp only [P, Q, M] at hsplit
  unfold ons_decMaskPhaseBucketE ons_decMaskPhaseBucketN
  linear_combination hsplit + hboth - hsymm

theorem ons_detWalkRoot_decoration_mask_delete_pair
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (q : ℝ) (hq : 0 ≤ q)
    (hentryM : ∀ d₂ d₁,
      ‖ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) d₂ d₁‖ ≤ q)
    (hsmall : q <
      (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1)
    (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    ons_detWalkRoot
        (ons_maskMatrix forbidden
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) =
      ons_detWalkRoot
          (ons_maskMatrix
            (({e, ons_dartRev L e} : Finset (ons_Dart L)) ∪ forbidden)
            (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))) *
        (1 - ∑' s, ons_firstReturnWeight
          (ons_maskMatrix forbidden
            (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)))
          e (ons_dartRev L e) s) := by
  let M := ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  let MF := ons_maskMatrix forbidden M
  let pair : Finset (ons_Dart L) := {e, ons_dartRev L e}
  have hentry : ∀ d₂ d₁ : ons_Dart L, ‖MF d₂ d₁‖ ≤ q := by
    intro d₂ d₁
    simp only [MF, ons_maskMatrix]
    split
    · simpa using hq
    · exact hentryM d₂ d₁
  have hfirst :
      Summable (fun s =>
        ‖ons_firstReturnWeight MF e (ons_dartRev L e) s‖) ∧
      (∑' s, ‖ons_firstReturnWeight MF e
        (ons_dartRev L e) s‖) < 1 :=
    ons_firstReturnWeight_small MF e (ons_dartRev L e)
      q hq hentry hsmall
  have her : e ≠ ons_dartRev L e := (ons_dartRev_ne L e).symm
  have hB : Summable fun n : ℕ =>
      ons_decMaskPhaseBucketE L decWeight a b forbidden e n /
        ((n : ℂ) + 1) := by
    simpa only [ons_decMaskPhaseBucketE, MF, M, not_exists] using
      ons_summable_loopBucketSeries MF e (ons_dartRev L e)
        her hfirst.1 hfirst.2
  have hN : Summable fun n : ℕ =>
      ons_decMaskPhaseBucketN L decWeight a b forbidden e n /
        ((n : ℂ) + 1) := by
    let P : (n : ℕ) → (Fin (n + 1) → ons_Dart L) → Prop :=
      fun _ loop =>
        ¬ (∃ i, loop i = e) ∧
          ¬ ∃ j, loop j = ons_dartRev L e
    have hs := ons_summable_filteredLoopSeries MF q hq hentry hcard P
    simpa only [ons_decMaskPhaseBucketN, MF, M, P] using hs
  have hseries :
      (∑' n : ℕ,
        (∑ loop : Fin (n + 1) → ons_Dart L,
          ons_loopWeight MF loop) / ((n : ℂ) + 1)) =
      2 * (∑' n : ℕ,
        ons_decMaskPhaseBucketE L decWeight a b forbidden e n /
          ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_decMaskPhaseBucketN L decWeight a b forbidden e n /
          ((n : ℂ) + 1)) := by
    rw [tsum_congr (fun n : ℕ => congrArg (· / ((n : ℂ) + 1))
      (ons_decMaskLoopSum_two_bucket
        (L := L) (n := n) decWeight a b
          forbidden hforbidden e))]
    have heq : (fun n : ℕ =>
        (2 * ons_decMaskPhaseBucketE L decWeight a b forbidden e n +
          ons_decMaskPhaseBucketN L decWeight a b forbidden e n) /
            ((n : ℂ) + 1)) =
        (fun n : ℕ => 2 *
          (ons_decMaskPhaseBucketE L decWeight a b forbidden e n /
            ((n : ℂ) + 1)) +
          ons_decMaskPhaseBucketN L decWeight a b forbidden e n /
            ((n : ℂ) + 1)) := by
      funext n
      ring
    rw [heq, (hB.mul_left 2).tsum_add hN, tsum_mul_left]
  have hlam :
      Complex.exp (-(∑' n : ℕ,
        ons_decMaskPhaseBucketE L decWeight a b forbidden e n /
          ((n : ℂ) + 1))) =
      1 - ∑' s, ons_firstReturnWeight MF e
        (ons_dartRev L e) s := by
    let z := ∑' s, ons_firstReturnWeight MF e
      (ons_dartRev L e) s
    have hz : ‖z‖ < 1 :=
      lt_of_le_of_lt (norm_tsum_le_tsum_norm hfirst.1) hfirst.2
    have hgeom := ons_loopBucketSeries_eq_geometric
      MF e (ons_dartRev L e) her hfirst.1 hfirst.2
    rw [show (∑' n : ℕ,
        ons_decMaskPhaseBucketE L decWeight a b forbidden e n /
          ((n : ℂ) + 1)) =
        ∑' k : ℕ, z ^ (k + 1) / (k + 1) by
      simpa only [ons_decMaskPhaseBucketE, MF, M,
        not_exists, z] using hgeom]
    exact ons_lemma4_exp hz
  have hNroot :
      Complex.exp (-(∑' n : ℕ,
        ons_decMaskPhaseBucketN L decWeight a b forbidden e n /
          ((n : ℂ) + 1)) / 2) =
      ons_detWalkRoot (ons_maskMatrix (pair ∪ forbidden) M) := by
    have hmask : ons_maskMatrix pair MF =
        ons_maskMatrix (pair ∪ forbidden) M := by
      simp only [MF]
      exact ons_maskMatrix_union pair forbidden M
    rw [← hmask]
    unfold ons_detWalkRoot
    apply congrArg Complex.exp
    congr 1
    apply congrArg Neg.neg
    apply tsum_congr
    intro n
    apply congrArg (· / ((n : ℂ) + 1))
    have hsum := ons_loopSum_maskMatrix (n := n + 1) pair MF
    have hset :
        Finset.univ.filter
            (fun loop : Fin (n + 1) → ons_Dart L =>
              ¬ ∃ k, loop k ∈ pair) =
          Finset.univ.filter
            (fun loop : Fin (n + 1) → ons_Dart L =>
              ¬ (∃ i, loop i = e) ∧
                ¬ ∃ j, loop j = ons_dartRev L e) := by
      ext loop
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        pair, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hset] at hsum
    simpa only [ons_loopWeight, ons_decMaskPhaseBucketN,
      MF, M] using hsum.symm
  change ons_detWalkRoot MF =
    ons_detWalkRoot (ons_maskMatrix (pair ∪ forbidden) M) *
      (1 - ∑' s, ons_firstReturnWeight MF e
        (ons_dartRev L e) s)
  change Complex.exp (-(∑' n : ℕ,
      (∑ loop : Fin (n + 1) → ons_Dart L,
        ∏ k : Fin (n + 1), MF (loop k) (loop (k + 1))) /
          ((n : ℂ) + 1)) / 2) =
    ons_detWalkRoot (ons_maskMatrix (pair ∪ forbidden) M) *
      (1 - ∑' s, ons_firstReturnWeight MF e
        (ons_dartRev L e) s)
  simp only [ons_loopWeight] at hseries
  rw [hseries]
  rw [show -(2 * (∑' n : ℕ,
        ons_decMaskPhaseBucketE L decWeight a b forbidden e n /
          ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_decMaskPhaseBucketN L decWeight a b forbidden e n /
          ((n : ℂ) + 1))) / 2 =
      (-(∑' n : ℕ,
        ons_decMaskPhaseBucketN L decWeight a b forbidden e n /
          ((n : ℂ) + 1)) / 2) +
      (-(∑' n : ℕ,
        ons_decMaskPhaseBucketE L decWeight a b forbidden e n /
          ((n : ℂ) + 1))) by ring,
    Complex.exp_add, hNroot, hlam]

theorem ons_detWalkRoot_decoration_scaleExternal_affine
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (q : ℝ) (hq : 0 ≤ q) (t : ℂ) (e : ons_Dart L)
    (hentryScaled : ∀ d₂ d₁,
      ‖ons_KWmatDecorationWeightedPhase L
        (ons_scaleDecEdgeWeight decWeight
          s(e, ons_dartRev L e) t)
        ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)
        d₂ d₁‖ ≤ q)
    (hsmall : q <
      (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
    ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight
            s(e, ons_dartRev L e) t)
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) =
      ons_detWalkRoot
          (ons_maskMatrix
            ({e, ons_dartRev L e} : Finset (ons_Dart L))
            (ons_KWmatDecorationWeightedPhase L decWeight
              ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) *
        (1 - t * ∑' s, ons_firstReturnWeight
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))
          e (ons_dartRev L e) s) := by
  let M := ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  let Mt := ons_KWmatDecorationWeightedPhase L
    (ons_scaleDecEdgeWeight decWeight
      s(e, ons_dartRev L e) t)
    ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)
  change ons_detWalkRoot Mt =
    ons_detWalkRoot
        (ons_maskMatrix
          ({e, ons_dartRev L e} : Finset (ons_Dart L)) M) *
      (1 - t * ∑' s, ons_firstReturnWeight M
        e (ons_dartRev L e) s)
  have hdel := ons_detWalkRoot_decoration_mask_delete_pair
    L (ons_scaleDecEdgeWeight decWeight
      s(e, ons_dartRev L e) t)
    a b q hq hentryScaled hsmall hcard
    (∅ : Finset (ons_Dart L)) (by simp) e
  have hmaskEmpty (A : Matrix (ons_Dart L) (ons_Dart L) ℂ) :
      ons_maskMatrix (∅ : Finset (ons_Dart L)) A = A := by
    ext d₂ d₁
    simp [ons_maskMatrix]
  rw [hmaskEmpty] at hdel
  simp only [Finset.union_empty] at hdel
  have hscale : Mt =
      ons_scaleColumns
        ({e, ons_dartRev L e} : Finset (ons_Dart L)) t M := by
    simpa only [M, Mt] using
      ons_KWmatDecorationWeightedPhase_scaleExternal
        L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) t e
  have hmask :
      ons_maskMatrix
          ({e, ons_dartRev L e} : Finset (ons_Dart L)) Mt =
        ons_maskMatrix
          ({e, ons_dartRev L e} : Finset (ons_Dart L)) M := by
    rw [hscale]
    exact ons_mask_scaleColumns_absorb _ _ _ _ Finset.Subset.rfl
  have hsum :
      (∑' s, ons_firstReturnWeight Mt e (ons_dartRev L e) s) =
        t * ∑' s, ons_firstReturnWeight M e
          (ons_dartRev L e) s := by
    rw [hscale]
    exact ons_tsum_firstReturnWeight_scale M e
      (ons_dartRev L e) t
  change ons_detWalkRoot Mt = _ at hdel
  rw [hdel, hmask, hsum]

end StatMech.Onsager
