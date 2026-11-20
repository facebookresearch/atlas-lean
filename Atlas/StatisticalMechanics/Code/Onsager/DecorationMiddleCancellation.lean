/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.AugmentedTurnCancellation









namespace StatMech.Onsager

open Matrix BigOperators

def ons_decMiddleAugRev (L : ℕ) :
    ons_Dart L ⊕ Fin 2 → ons_Dart L ⊕ Fin 2
  | .inl d => .inl (ons_dartRev L d)
  | .inr side => .inr (side + 1)

def ons_decMiddleAugDir {L : ℕ} :
    ons_Dart L ⊕ Fin 2 → Fin 4
  | .inl d => d.2
  | .inr side => ons_decMiddleDir side

noncomputable def ons_decMiddleRowWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ)
    (t : ℂ) (site : ZMod L × ZMod L) :
    ons_Dart L ⊕ Fin 2 → ℂ
  | .inl _ => 1
  | .inr _ => t * decWeight (ons_decChainEdge site 1)

noncomputable def ons_decMiddleColWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ) :
    ons_Dart L ⊕ Fin 2 → ℂ
  | .inl d => decWeight s(d, ons_dartRev L d)
  | .inr _ => 1



noncomputable def ons_decMiddleInternalFactor
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (site : ZMod L × ZMod L) :
    (ons_Dart L ⊕ Fin 2) → (ons_Dart L ⊕ Fin 2) → ℂ
  | .inl d₂, .inl d₁ =>
      if d₂.1 = ons_dirStep L d₁.2 d₁.1 then
        ∏ i ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2,
          ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 1) 0 (ons_decChainEdge d₂.1 i)
      else 0
  | .inl d₂, .inr side =>
      if d₂.1 = site ∧ ons_decMiddleSide d₂.2 = side then
        ons_decMiddleDestFactor decWeight site d₂.2
      else 0
  | .inr side, .inl d₁ =>
      if site = ons_dirStep L d₁.2 d₁.1 ∧
          ons_decMiddleSide d₁.2 = side then
        ons_decMiddleSourceFactor decWeight site d₁.2
      else 0
  | .inr _, .inr _ => 0

theorem ons_decMiddleAugRev_involutive (L : ℕ) :
    Function.Involutive (ons_decMiddleAugRev L) := by
  rintro (d | side)
  · exact congrArg Sum.inl (ons_dartRev_involutive L d)
  · fin_cases side <;> rfl

theorem ons_decMiddleAugDir_rev
    (L : ℕ) (state : ons_Dart L ⊕ Fin 2) :
    ons_decMiddleAugDir (ons_decMiddleAugRev L state) =
      ons_decMiddleAugDir state + 2 := by
  rcases state with d | side
  · rfl
  · fin_cases side <;> rfl

theorem ons_decMiddleAugRev_ne
    (L : ℕ) [Fact (2 < L)]
    (state : ons_Dart L ⊕ Fin 2) :
    ons_decMiddleAugRev L state ≠ state := by
  rcases state with d | side
  · intro h
    apply ons_dartRev_ne L d
    exact Sum.inl_injective h
  · intro h
    have hs : side + 1 = side := Sum.inr_injective h
    fin_cases side <;> norm_num at hs

@[simp] theorem ons_scaleMiddle_external
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (site : ZMod L × ZMod L) (t : ℂ) (d : ons_Dart L) :
    ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 1) t
        s(d, ons_dartRev L d) =
      decWeight s(d, ons_dartRev L d) := by
  unfold ons_scaleDecEdgeWeight
  rw [if_neg]
  intro heq
  apply ons_decChainEdge_not_external L site 1
  exact ⟨d, heq.symm⟩

theorem ons_decMiddleStateWeight_rev
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (t : ℂ)
    (site : ZMod L × ZMod L)
    (state : ons_Dart L ⊕ Fin 2) :
    ons_decMiddleRowWeight decWeight t site
        (ons_decMiddleAugRev L state) *
      ons_decMiddleColWeight decWeight
        (ons_decMiddleAugRev L state) =
    ons_decMiddleRowWeight decWeight t site state *
      ons_decMiddleColWeight decWeight state := by
  rcases state with d | side
  · simp only [ons_decMiddleAugRev, ons_decMiddleRowWeight,
      ons_decMiddleColWeight, one_mul]
    rw [ons_dartRev_involutive]
    congr 1
    exact Sym2.eq_swap
  · fin_cases side <;>
      simp [ons_decMiddleAugRev, ons_decMiddleRowWeight,
        ons_decMiddleColWeight]

theorem ons_decMiddleInternalFactor_rev
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (site : ZMod L × ZMod L)
    (x y : ons_Dart L ⊕ Fin 2) :
    ons_decMiddleInternalFactor L decWeight site
        (ons_decMiddleAugRev L y) (ons_decMiddleAugRev L x) =
      ons_decMiddleInternalFactor L decWeight site x y := by
  rcases x with d₂ | side₂ <;> rcases y with d₁ | side₁
  · rcases d₂ with ⟨p₂, mu₂⟩
    rcases d₁ with ⟨p₁, mu₁⟩
    fin_cases mu₂ <;> fin_cases mu₁ <;>
      simp [ons_decMiddleInternalFactor, ons_decMiddleAugRev,
        ons_dartRev, ons_dirStep, ons_decChainPathIndices_comm, eq_comm] <;>
      split_ifs with h <;> simp_all
  · rcases d₂ with ⟨p₂, mu₂⟩
    fin_cases mu₂ <;> fin_cases side₁ <;>
      simp [ons_decMiddleInternalFactor, ons_decMiddleAugRev,
        ons_dartRev, ons_dirStep, ons_decMiddleSide,
        ons_decMiddleDestFactor, ons_decMiddleSourceFactor, eq_comm]
  · rcases d₁ with ⟨p₁, mu₁⟩
    fin_cases side₂ <;> fin_cases mu₁ <;>
      simp [ons_decMiddleInternalFactor, ons_decMiddleAugRev,
        ons_dartRev, ons_dirStep, ons_decMiddleSide,
        ons_decMiddleDestFactor, ons_decMiddleSourceFactor, eq_comm]
  · simp [ons_decMiddleInternalFactor, ons_decMiddleAugRev]



theorem ons_decMiddleAugmented_factor
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t : ℂ) (site : ZMod L × ZMod L) :
    ons_decMiddleAugmented L decWeight omega 1 1 t site =
      ons_stateWeightedReversibleTurnMatrix ons_decMiddleAugDir omega
        (ons_decMiddleRowWeight decWeight t site)
        (ons_decMiddleColWeight decWeight)
        (ons_decMiddleInternalFactor L decWeight site) := by
  ext x y
  rcases x with d₂ | side₂ <;> rcases y with d₁ | side₁
  · simp only [ons_decMiddleAugmented, Matrix.fromBlocks_apply₁₁,
      ons_stateWeightedReversibleTurnMatrix, ons_decMiddleAugDir,
      ons_decMiddleRowWeight, ons_decMiddleColWeight,
      ons_decMiddleInternalFactor, one_mul]
    unfold ons_KWmatDecorationWeightedPhase ons_decTransitionWeight
    by_cases hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1
    · rw [if_pos hstep, if_pos hstep]
      simp only [ons_dirPhase_one_one, one_mul]
      rw [ons_scaleMiddle_external]
    · simp [hstep]
  · simp [ons_decMiddleAugmented,
      ons_stateWeightedReversibleTurnMatrix,
      ons_decMiddleRowWeight, ons_decMiddleColWeight,
      ons_decMiddleInternalFactor, ons_decMiddleAugDir,
      ons_decMiddleU]
  · simp [ons_decMiddleAugmented,
      ons_stateWeightedReversibleTurnMatrix,
      ons_decMiddleRowWeight, ons_decMiddleColWeight,
      ons_decMiddleInternalFactor, ons_decMiddleAugDir,
      ons_decMiddleV, ons_dirPhase_one_one]
    ring
  · simp [ons_decMiddleAugmented,
      ons_stateWeightedReversibleTurnMatrix,
      ons_decMiddleRowWeight, ons_decMiddleColWeight,
      ons_decMiddleInternalFactor]

theorem ons_decMiddleAugmented_lemma5
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I)
    (site : ZMod L × ZMod L)
    (state : ons_Dart L ⊕ Fin 2) :
    ∑ loop ∈ ons_loopSetBoth (n := n) state
        (ons_decMiddleAugRev L state),
      ons_loopWeight
        (ons_decMiddleAugmented L decWeight omega 1 1 t site) loop = 0 := by
  rw [ons_decMiddleAugmented_factor]
  exact ons_stateWeightedReversibleTurnMatrix_lemma5
    (ons_decMiddleAugRev L) (ons_decMiddleAugRev_involutive L)
    ons_decMiddleAugDir (ons_decMiddleAugDir_rev L)
    omega homega hI
    (ons_decMiddleRowWeight decWeight t site)
    (ons_decMiddleColWeight decWeight)
    (ons_decMiddleStateWeight_rev L decWeight t site)
    (ons_decMiddleInternalFactor L decWeight site)
    (ons_decMiddleInternalFactor_rev L decWeight site)
    state (ons_decMiddleAugRev_ne L state)

theorem ons_loopWeight_decMiddleAugmented_loopRev
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I)
    (site : ZMod L × ZMod L)
    (loop : Fin n → ons_Dart L ⊕ Fin 2) :
    ons_loopWeight
        (ons_decMiddleAugmented L decWeight omega 1 1 t site)
        (ons_involutiveLoopRev (ons_decMiddleAugRev L) loop) =
      ons_loopWeight
        (ons_decMiddleAugmented L decWeight omega 1 1 t site) loop := by
  rw [ons_decMiddleAugmented_factor]
  exact ons_loopWeight_stateWeightedReversibleTurnMatrix_loopRev
    (ons_decMiddleAugRev L) ons_decMiddleAugDir
    (ons_decMiddleAugDir_rev L) omega homega hI
    (ons_decMiddleRowWeight decWeight t site)
    (ons_decMiddleColWeight decWeight)
    (ons_decMiddleStateWeight_rev L decWeight t site)
    (ons_decMiddleInternalFactor L decWeight site)
    (ons_decMiddleInternalFactor_rev L decWeight site) loop

theorem ons_decMiddleAugmented_mask_lemma5
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I)
    (site : ZMod L × ZMod L)
    (forbidden : Finset (ons_Dart L ⊕ Fin 2))
    (hforbidden : ∀ state,
      ons_decMiddleAugRev L state ∈ forbidden ↔ state ∈ forbidden)
    (state : ons_Dart L ⊕ Fin 2) :
    ∑ loop ∈ ons_loopSetBoth (n := n) state
        (ons_decMiddleAugRev L state),
      ons_loopWeight
        (ons_maskMatrix forbidden
          (ons_decMiddleAugmented L decWeight omega 1 1 t site)) loop = 0 := by
  rw [ons_decMiddleAugmented_factor,
    ons_mask_stateWeightedReversibleTurnMatrix]
  exact ons_stateWeightedReversibleTurnMatrix_lemma5
    (ons_decMiddleAugRev L) (ons_decMiddleAugRev_involutive L)
    ons_decMiddleAugDir (ons_decMiddleAugDir_rev L)
    omega homega hI
    (ons_decMiddleRowWeight decWeight t site)
    (ons_decMiddleColWeight decWeight)
    (ons_decMiddleStateWeight_rev L decWeight t site)
    (ons_maskedReversibleFactor forbidden
      (ons_decMiddleInternalFactor L decWeight site))
    (ons_maskedReversibleFactor_rev
      (ons_decMiddleAugRev L) forbidden hforbidden
      (ons_decMiddleInternalFactor L decWeight site)
      (ons_decMiddleInternalFactor_rev L decWeight site))
    state (ons_decMiddleAugRev_ne L state)

theorem ons_loopWeight_decMiddleAugmented_mask_loopRev
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I)
    (site : ZMod L × ZMod L)
    (forbidden : Finset (ons_Dart L ⊕ Fin 2))
    (hforbidden : ∀ state,
      ons_decMiddleAugRev L state ∈ forbidden ↔ state ∈ forbidden)
    (loop : Fin n → ons_Dart L ⊕ Fin 2) :
    ons_loopWeight
        (ons_maskMatrix forbidden
          (ons_decMiddleAugmented L decWeight omega 1 1 t site))
        (ons_involutiveLoopRev (ons_decMiddleAugRev L) loop) =
      ons_loopWeight
        (ons_maskMatrix forbidden
          (ons_decMiddleAugmented L decWeight omega 1 1 t site)) loop := by
  rw [ons_decMiddleAugmented_factor,
    ons_mask_stateWeightedReversibleTurnMatrix]
  exact ons_loopWeight_stateWeightedReversibleTurnMatrix_loopRev
    (ons_decMiddleAugRev L) ons_decMiddleAugDir
    (ons_decMiddleAugDir_rev L) omega homega hI
    (ons_decMiddleRowWeight decWeight t site)
    (ons_decMiddleColWeight decWeight)
    (ons_decMiddleStateWeight_rev L decWeight t site)
    (ons_maskedReversibleFactor forbidden
      (ons_decMiddleInternalFactor L decWeight site))
    (ons_maskedReversibleFactor_rev
      (ons_decMiddleAugRev L) forbidden hforbidden
      (ons_decMiddleInternalFactor L decWeight site)
      (ons_decMiddleInternalFactor_rev L decWeight site)) loop

end StatMech.Onsager
