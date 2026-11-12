/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.MvSeriesAnalyticUniqueness









namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_decMiddleBalanced
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (omega t lambda : ℂ) (site : ZMod L × ZMod L) :
    Matrix (ons_Dart L ⊕ Fin 2) (ons_Dart L ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks
    (ons_KWmatDecorationWeightedPhase L
      (ons_scaleDecEdgeWeight decWeight
        (ons_decChainEdge site 1) 0) omega 1 1)
    ((t * lambda) • ons_decMiddleU L decWeight omega site)
    (lambda⁻¹ • ons_decMiddleV L decWeight omega 1 1 site)
    0

noncomputable def ons_decMiddleBalancedRowWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ) (lambda : ℂ)
    (site : ZMod L × ZMod L) : ons_Dart L ⊕ Fin 2 → ℂ
  | .inl _ => 1
  | .inr _ => lambda⁻¹ * decWeight (ons_decChainEdge site 1)

noncomputable def ons_decMiddleBalancedColWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ) (t lambda : ℂ) :
    ons_Dart L ⊕ Fin 2 → ℂ
  | .inl d => decWeight s(d, ons_dartRev L d)
  | .inr _ => t * lambda

theorem ons_decMiddleBalanced_factor
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t lambda : ℂ) (site : ZMod L × ZMod L) :
    ons_decMiddleBalanced L decWeight omega t lambda site =
      ons_stateWeightedReversibleTurnMatrix ons_decMiddleAugDir omega
        (ons_decMiddleBalancedRowWeight decWeight lambda site)
        (ons_decMiddleBalancedColWeight decWeight t lambda)
        (ons_decMiddleInternalFactor L decWeight site) := by
  ext x y
  rcases x with d₂ | side₂ <;> rcases y with d₁ | side₁
  · simp only [ons_decMiddleBalanced, Matrix.fromBlocks_apply₁₁,
      ons_stateWeightedReversibleTurnMatrix, ons_decMiddleAugDir,
      ons_decMiddleBalancedRowWeight, ons_decMiddleBalancedColWeight,
      ons_decMiddleInternalFactor, one_mul]
    unfold ons_KWmatDecorationWeightedPhase ons_decTransitionWeight
    by_cases hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1
    · rw [if_pos hstep, if_pos hstep]
      simp only [ons_dirPhase_one_one, one_mul]
      rw [ons_scaleMiddle_external]
    · simp [hstep]
  · simp [ons_decMiddleBalanced,
      ons_stateWeightedReversibleTurnMatrix,
      ons_decMiddleBalancedRowWeight, ons_decMiddleBalancedColWeight,
      ons_decMiddleInternalFactor, ons_decMiddleAugDir,
      ons_decMiddleU]
    ring
  · simp [ons_decMiddleBalanced,
      ons_stateWeightedReversibleTurnMatrix,
      ons_decMiddleBalancedRowWeight, ons_decMiddleBalancedColWeight,
      ons_decMiddleInternalFactor, ons_decMiddleAugDir,
      ons_decMiddleV, ons_dirPhase_one_one]
    ring
  · simp [ons_decMiddleBalanced,
      ons_stateWeightedReversibleTurnMatrix,
      ons_decMiddleBalancedRowWeight, ons_decMiddleBalancedColWeight,
      ons_decMiddleInternalFactor]

theorem ons_decMiddleBalanced_det
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t lambda : ℂ) (homega : omega ≠ 0) (hlambda : lambda ≠ 0)
    (site : ZMod L × ZMod L) :
    (1 - ons_decMiddleBalanced L decWeight omega t lambda site).det =
      (1 - ons_KWmatDecorationWeightedPhase L
        (ons_scaleDecEdgeWeight decWeight
          (ons_decChainEdge site 1) t) omega 1 1).det := by
  let M₀ := ons_KWmatDecorationWeightedPhase L
    (ons_scaleDecEdgeWeight decWeight
      (ons_decChainEdge site 1) 0) omega 1 1
  let U := ons_decMiddleU L decWeight omega site
  let V := ons_decMiddleV L decWeight omega 1 1 site
  have hblock :
      1 - ons_decMiddleBalanced L decWeight omega t lambda site =
        Matrix.fromBlocks (1 - M₀) (-((t * lambda) • U))
          (-(lambda⁻¹ • V)) 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [ons_decMiddleBalanced, M₀, U, V, Matrix.one_apply]
  have hmul : (-((t * lambda) • U)) * (-(lambda⁻¹ • V)) =
      t • (U * V) := by
    ext i j
    simp [Matrix.mul_apply]
    field_simp [hlambda]
  rw [hblock, Matrix.det_fromBlocks_one₂₂, hmul]
  have hrank :=
    ons_KWmatDecorationWeightedPhase_scaleMiddle_rankTwo
      L decWeight omega 1 1 t homega site
  have hrank' :
      ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 1) t) omega 1 1 =
        M₀ + t • (U * V) := by
    simpa only [M₀, U, V] using hrank
  rw [show 1 - M₀ - t • (U * V) =
      1 - (M₀ + t • (U * V)) by abel]
  rw [← hrank']

theorem ons_loopWeight_decMiddleBalanced_eq_row
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t lambda : ℂ) (hlambda : lambda ≠ 0)
    (site : ZMod L × ZMod L)
    (loop : Fin n → ons_Dart L ⊕ Fin 2) :
    ons_loopWeight
        (ons_decMiddleBalanced L decWeight omega t lambda site) loop =
      ons_loopWeight
        (ons_decMiddleAugmented L decWeight omega 1 1 t site) loop := by
  rw [ons_decMiddleBalanced_factor, ons_decMiddleAugmented_factor,
    ons_loopWeight_stateWeightedReversibleTurnMatrix,
    ons_loopWeight_stateWeightedReversibleTurnMatrix]
  congr 2
  apply Finset.prod_congr rfl
  intro k hk
  rcases hstate : loop k with d | side
  · simp [ons_decMiddleBalancedRowWeight,
      ons_decMiddleBalancedColWeight,
      ons_decMiddleRowWeight, ons_decMiddleColWeight]
  · simp [ons_decMiddleBalancedRowWeight,
      ons_decMiddleBalancedColWeight,
      ons_decMiddleRowWeight, ons_decMiddleColWeight]
    field_simp [hlambda]

theorem ons_decMiddleBalanced_scaleColumns
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (omega t lambda : ℂ) (site : ZMod L × ZMod L) :
    ons_decMiddleBalanced L decWeight omega t lambda site =
      ons_scaleColumns
        ({Sum.inr 0, Sum.inr 1} :
          Finset (ons_Dart L ⊕ Fin 2)) t
        (ons_decMiddleBalanced L decWeight omega 1 lambda site) := by
  ext x y
  rcases x with d₂ | side₂ <;> rcases y with d₁ | side₁
  · simp [ons_decMiddleBalanced, ons_scaleColumns]
  · fin_cases side₁ <;>
      simp [ons_decMiddleBalanced, ons_scaleColumns] <;> ring
  · simp [ons_decMiddleBalanced, ons_scaleColumns]
  · fin_cases side₁ <;>
      simp [ons_decMiddleBalanced, ons_scaleColumns]

theorem ons_decMiddleBalanced_lemma5
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t lambda : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I) (hlambda : lambda ≠ 0)
    (site : ZMod L × ZMod L)
    (state : ons_Dart L ⊕ Fin 2) :
    ∑ loop ∈ ons_loopSetBoth (n := n) state
        (ons_decMiddleAugRev L state),
      ons_loopWeight
        (ons_decMiddleBalanced L decWeight omega t lambda site) loop = 0 := by
  calc
    (∑ loop ∈ ons_loopSetBoth (n := n) state
        (ons_decMiddleAugRev L state),
      ons_loopWeight
        (ons_decMiddleBalanced L decWeight omega t lambda site) loop) =
      ∑ loop ∈ ons_loopSetBoth (n := n) state
        (ons_decMiddleAugRev L state),
      ons_loopWeight
        (ons_decMiddleAugmented L decWeight omega 1 1 t site) loop := by
          apply Finset.sum_congr rfl
          intro loop hloop
          exact ons_loopWeight_decMiddleBalanced_eq_row
            L decWeight omega t lambda hlambda site loop
    _ = 0 := ons_decMiddleAugmented_lemma5
      L decWeight omega t homega hI site state

theorem ons_loopWeight_decMiddleBalanced_loopRev
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t lambda : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I) (hlambda : lambda ≠ 0)
    (site : ZMod L × ZMod L)
    (loop : Fin n → ons_Dart L ⊕ Fin 2) :
    ons_loopWeight
        (ons_decMiddleBalanced L decWeight omega t lambda site)
        (ons_involutiveLoopRev (ons_decMiddleAugRev L) loop) =
      ons_loopWeight
        (ons_decMiddleBalanced L decWeight omega t lambda site) loop := by
  calc
    ons_loopWeight
        (ons_decMiddleBalanced L decWeight omega t lambda site)
        (ons_involutiveLoopRev (ons_decMiddleAugRev L) loop) =
      ons_loopWeight
        (ons_decMiddleAugmented L decWeight omega 1 1 t site)
        (ons_involutiveLoopRev (ons_decMiddleAugRev L) loop) :=
      ons_loopWeight_decMiddleBalanced_eq_row
        L decWeight omega t lambda hlambda site _
    _ = ons_loopWeight
        (ons_decMiddleAugmented L decWeight omega 1 1 t site) loop :=
      ons_loopWeight_decMiddleAugmented_loopRev
        L decWeight omega t homega hI site loop
    _ = ons_loopWeight
        (ons_decMiddleBalanced L decWeight omega t lambda site) loop :=
      (ons_loopWeight_decMiddleBalanced_eq_row
        L decWeight omega t lambda hlambda site loop).symm

theorem ons_detWalkRoot_decMiddleBalanced_affine
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t lambda : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I) (hlambda : lambda ≠ 0)
    (site : ZMod L × ZMod L)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ x y,
      ‖ons_decMiddleBalanced L decWeight omega t lambda site x y‖ ≤ q)
    (hsmall : q <
      (2 * (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) * q < 1) :
    ons_detWalkRoot
        (ons_decMiddleBalanced L decWeight omega t lambda site) =
      ons_detWalkRoot
          (ons_maskMatrix
            ({Sum.inr 0, Sum.inr 1} :
              Finset (ons_Dart L ⊕ Fin 2))
            (ons_decMiddleBalanced L decWeight omega 1 lambda site)) *
        (1 - t * ∑' s, ons_firstReturnWeight
          (ons_decMiddleBalanced L decWeight omega 1 lambda site)
          (Sum.inr 0) (Sum.inr 1) s) := by
  let Mt := ons_decMiddleBalanced L decWeight omega t lambda site
  let M := ons_decMiddleBalanced L decWeight omega 1 lambda site
  let e : ons_Dart L ⊕ Fin 2 := Sum.inr 0
  let r : ons_Dart L ⊕ Fin 2 := Sum.inr 1
  have hboth : ∀ n : ℕ,
      (∑ loop ∈ ons_loopSetBoth (n := n + 1) e r,
        ons_loopWeight Mt loop) = 0 := by
    intro n
    simpa only [e, r, Mt, ons_decMiddleAugRev] using
      ons_decMiddleBalanced_lemma5
        (n := n + 1) L decWeight omega t lambda
        homega hI hlambda site e
  have hsymm : ∀ n : ℕ,
      (∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (n + 1) → ons_Dart L ⊕ Fin 2 ↦
            (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = r),
        ons_loopWeight Mt loop) =
        ∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (n + 1) → ons_Dart L ⊕ Fin 2 ↦
            (∃ i, loop i = r) ∧ ¬ ∃ j, loop j = e),
          ons_loopWeight Mt loop := by
    intro n
    simpa only [e, r, Mt, ons_decMiddleAugRev] using
      ons_matrixLoopSum_orientation_symm_of_loopRev
        (n := n + 1) (ons_decMiddleAugRev L)
        (ons_decMiddleAugRev_involutive L) Mt
        (ons_loopWeight_decMiddleBalanced_loopRev
          L decWeight omega t lambda homega hI hlambda site) e
  have hdel := ons_detWalkRoot_matrix_delete_pair Mt e r
    (by simp [e, r]) q hq hentry hsmall hcard hboth hsymm
  have hscale : Mt =
      ons_scaleColumns ({e, r} : Finset (ons_Dart L ⊕ Fin 2)) t M := by
    simpa only [Mt, M, e, r] using
      ons_decMiddleBalanced_scaleColumns L decWeight omega t lambda site
  have hmask :
      ons_maskMatrix ({e, r} : Finset (ons_Dart L ⊕ Fin 2)) Mt =
        ons_maskMatrix ({e, r} : Finset (ons_Dart L ⊕ Fin 2)) M := by
    rw [hscale]
    exact ons_mask_scaleColumns_absorb _ _ _ _ Finset.Subset.rfl
  have hsum : (∑' s, ons_firstReturnWeight Mt e r s) =
      t * ∑' s, ons_firstReturnWeight M e r s := by
    rw [hscale]
    exact ons_tsum_firstReturnWeight_scale M e r t
  simpa only [Mt, M, e, r] using hdel.trans (by rw [hmask, hsum])

theorem norm_ons_decMiddleDestFactor_le_one
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ)
    (site : ZMod L × ZMod L)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ 1) (mu : Fin 4) :
    ‖ons_decMiddleDestFactor decWeight site mu‖ ≤ 1 := by
  fin_cases mu <;> simp [ons_decMiddleDestFactor, hall]

theorem norm_ons_decMiddleSourceFactor_le_one
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ)
    (site : ZMod L × ZMod L)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ 1) (mu : Fin 4) :
    ‖ons_decMiddleSourceFactor decWeight site mu‖ ≤ 1 := by
  fin_cases mu <;> simp [ons_decMiddleSourceFactor, hall]

theorem norm_ons_decMiddleU_le_one
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (site : ZMod L × ZMod L)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
    (d : ons_Dart L) (side : Fin 2) :
    ‖ons_decMiddleU L decWeight ons_turnRoot site d side‖ ≤ 1 := by
  unfold ons_decMiddleU
  split
  · rw [norm_mul]
    calc
      ‖ons_decMiddleDestFactor decWeight site d.2‖ *
          ‖ons_turnW ons_turnRoot (ons_decMiddleDir side) d.2‖ ≤
        1 * 1 := mul_le_mul
          (norm_ons_decMiddleDestFactor_le_one decWeight site hall d.2)
          (norm_ons_turnW_turnRoot_le_one _ _)
          (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  · simp

theorem norm_ons_decMiddleV_le_sq
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (site : ZMod L × ZMod L) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ r)
    (side : Fin 2) (d : ons_Dart L) :
    ‖ons_decMiddleV L decWeight ons_turnRoot 1 1 site side d‖ ≤ r ^ 2 := by
  have hallOne : ∀ edge, ‖decWeight edge‖ ≤ 1 :=
    fun edge ↦ (hall edge).trans hr1
  unfold ons_decMiddleV
  split
  · simp only [ons_dirPhase_one_one, norm_mul, norm_one, mul_one]
    have hsource := norm_ons_decMiddleSourceFactor_le_one
      decWeight site hallOne d.2
    have hturn := norm_ons_turnW_turnRoot_le_one
      d.2 (ons_decMiddleDir side)
    have hmiddle := hall (ons_decChainEdge site 1)
    have hexternal := hall s(d, ons_dartRev L d)
    calc
      ‖decWeight (ons_decChainEdge site 1)‖ *
            ‖decWeight s(d, ons_dartRev L d)‖ *
          ‖ons_decMiddleSourceFactor decWeight site d.2‖ *
        ‖ons_turnW ons_turnRoot d.2 (ons_decMiddleDir side)‖ ≤
          r * r * 1 * 1 := by gcongr
      _ = r ^ 2 := by ring
  · simp [hr0]

theorem norm_ons_decMiddleBalanced_entry_le
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (t lambda : ℂ) (hlambda : lambda ≠ 0)
    (site : ZMod L × ZMod L)
    (hlambdaOne : ‖lambda‖ ≤ 1)
    (ht : ‖t‖ ≤ 2)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ ‖lambda‖)
    (x y : ons_Dart L ⊕ Fin 2) :
    ‖ons_decMiddleBalanced L decWeight ons_turnRoot t lambda site x y‖ ≤
      2 * ‖lambda‖ := by
  have hlambda0 : 0 ≤ ‖lambda‖ := norm_nonneg _
  have hallOne : ∀ edge, ‖decWeight edge‖ ≤ 1 :=
    fun edge ↦ (hall edge).trans hlambdaOne
  rcases x with d₂ | side₂ <;> rcases y with d₁ | side₁
  · simp only [ons_decMiddleBalanced, Matrix.fromBlocks_apply₁₁]
    unfold ons_KWmatDecorationWeightedPhase
    split
    · simp only [ons_dirPhase_one_one, one_mul, norm_mul]
      have hscaledAll : ∀ edge,
          ‖ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 1) 0 edge‖ ≤ 1 := by
        intro edge
        unfold ons_scaleDecEdgeWeight
        split
        · simp
        · exact hallOne edge
      have hscaledExt : ∀ d,
          ‖ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 1) 0 s(d, ons_dartRev L d)‖ ≤
              ‖lambda‖ := by
        intro d
        rw [ons_scaleMiddle_external]
        exact hall _
      have htransition := norm_ons_decTransitionWeight_le
        L (ons_scaleDecEdgeWeight decWeight
          (ons_decChainEdge site 1) 0)
        ‖lambda‖ hlambda0 hscaledAll hscaledExt d₂ d₁
      have hturn := norm_ons_turnW_turnRoot_le_one d₁.2 d₂.2
      nlinarith [mul_le_mul htransition hturn
        (norm_nonneg _) hlambda0]
    · simp [hlambda0]
  · simp only [ons_decMiddleBalanced, Matrix.fromBlocks_apply₁₂,
      Matrix.smul_apply, smul_eq_mul, norm_mul]
    have hU := norm_ons_decMiddleU_le_one
      L decWeight site hallOne d₂ side₁
    calc
      ‖t‖ * ‖lambda‖ *
          ‖ons_decMiddleU L decWeight ons_turnRoot site d₂ side₁‖ ≤
        2 * ‖lambda‖ * 1 := by gcongr
      _ = 2 * ‖lambda‖ := by ring
  · simp only [ons_decMiddleBalanced, Matrix.fromBlocks_apply₂₁,
      Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    have hV := norm_ons_decMiddleV_le_sq
      L decWeight site ‖lambda‖ hlambda0 hlambdaOne hall side₂ d₁
    have hnormPos : 0 < ‖lambda‖ := norm_pos_iff.mpr hlambda
    rw [inv_eq_one_div]
    calc
      (1 / ‖lambda‖) *
          ‖ons_decMiddleV L decWeight ons_turnRoot 1 1 site side₂ d₁‖ ≤
        (1 / ‖lambda‖) * ‖lambda‖ ^ 2 := by gcongr
      _ = ‖lambda‖ := by field_simp
      _ ≤ 2 * ‖lambda‖ := by nlinarith
  · simp [ons_decMiddleBalanced, hlambda0]

theorem norm_ons_spinDartSeamSign
    {L : ℕ} (a b : Fin 2) (d : ons_Dart L) :
    ‖ons_spinDartSeamSign a b d‖ = 1 := by
  unfold ons_spinDartSeamSign
  rw [norm_zpow]
  norm_num

theorem norm_ons_spinSeamDecWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ)
    (a b : Fin 2) (edge : ons_DecEdge L) :
    ‖ons_spinSeamDecWeight decWeight a b edge‖ = ‖decWeight edge‖ := by
  classical
  unfold ons_spinSeamDecWeight
  split
  · rw [norm_mul, norm_ons_spinDartSeamSign, one_mul]
  · rfl

theorem ons_detWalkRoot_KWDecoration_spinGauge
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (omega : ℂ) :
    ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L decWeight omega
          (ons_spinPhase L a) (ons_spinPhase L b)) =
      ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L
          (ons_spinSeamDecWeight decWeight a b) omega 1 1) := by
  apply ons_detWalkRoot_eq_of_loopWeight_eq
  intro n loop
  rw [ons_KWmatDecorationWeightedPhase_spinGauge]
  exact ons_loopWeight_diagonalGaugeMatrix
    (fun d : ons_Dart L ↦ ons_spinVertexGauge L a b d.1)
    (fun d ↦ ons_spinVertexGauge_ne_zero L a b d.1)
    (ons_KWmatDecorationWeightedPhase L
      (ons_spinSeamDecWeight decWeight a b) omega 1 1) loop

theorem ons_detWalkRoot_scaleMiddle_balanced_affine_of_bounds
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (t lambda : ℂ) (hlambda : lambda ≠ 0)
    (site : ZMod L × ZMod L)
    (qCompressed qAugmented : ℝ)
    (hqCompressed : 0 ≤ qCompressed)
    (hqAugmented : 0 ≤ qAugmented)
    (hentryCompressed : ∀ x y,
      ‖ons_KWmatDecorationWeightedPhase L
        (ons_spinSeamDecWeight
          (ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 1) t) a b)
        ons_turnRoot 1 1 x y‖ ≤ qCompressed)
    (hentryAugmented : ∀ x y,
      ‖ons_decMiddleBalanced L
        (ons_spinSeamDecWeight decWeight a b)
        ons_turnRoot t lambda site x y‖ ≤ qAugmented)
    (hsmallCompressed : qCompressed <
      (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
    (hsmallAugmented : qAugmented <
      (2 * (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) ^ 2)⁻¹) :
    ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 1) t)
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) =
      ons_detWalkRoot
          (ons_maskMatrix
            ({Sum.inr 0, Sum.inr 1} :
              Finset (ons_Dart L ⊕ Fin 2))
            (ons_decMiddleBalanced L
              (ons_spinSeamDecWeight decWeight a b)
              ons_turnRoot 1 lambda site)) *
        (1 - t * ∑' s, ons_firstReturnWeight
          (ons_decMiddleBalanced L
            (ons_spinSeamDecWeight decWeight a b)
            ons_turnRoot 1 lambda site)
          (Sum.inr 0) (Sum.inr 1) s) := by
  let scaled := ons_scaleDecEdgeWeight decWeight
    (ons_decChainEdge site 1) t
  let seamWeight := ons_spinSeamDecWeight decWeight a b
  let seamScaled := ons_spinSeamDecWeight scaled a b
  let Mphased := ons_KWmatDecorationWeightedPhase L scaled
    ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)
  let Mcompressed := ons_KWmatDecorationWeightedPhase L seamScaled
    ons_turnRoot 1 1
  let Maugmented := ons_decMiddleBalanced L seamWeight
    ons_turnRoot t lambda site
  have hcardCompressed :
      (Fintype.card (ons_Dart L) : ℝ) * qCompressed < 1 :=
    ons_card_mul_lt_one_of_Sherman_small
      qCompressed hsmallCompressed
  have hcardAugmented :
      (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) * qAugmented < 1 :=
    ons_card_mul_lt_one_of_Sherman_small
      qAugmented hsmallAugmented
  have hgeomCompressed :
      (∑' n : ℕ, ((Fintype.card (ons_Dart L) : ℝ) *
        qCompressed) ^ (n + 1)) < 1 :=
    ons_geom_sum_lt_one_of_Sherman_small
      qCompressed hqCompressed hsmallCompressed
  have hgeomAugmented :
      (∑' n : ℕ, ((Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) *
        qAugmented) ^ (n + 1)) < 1 :=
    ons_geom_sum_lt_one_of_Sherman_small
      qAugmented hqAugmented hsmallAugmented
  have hscaleSeam : seamScaled =
      ons_scaleDecEdgeWeight seamWeight
        (ons_decChainEdge site 1) t := by
    simpa only [scaled, seamWeight, seamScaled] using
      ons_spinSeamDecWeight_scale_chain_one
        L decWeight a b site t
  have hdet : (1 - Mcompressed).det = (1 - Maugmented).det := by
    symm
    rw [show Mcompressed = ons_KWmatDecorationWeightedPhase L
        (ons_scaleDecEdgeWeight seamWeight
          (ons_decChainEdge site 1) t) ons_turnRoot 1 1 by
      simp only [Mcompressed, hscaleSeam]]
    simpa only [Maugmented] using
      ons_decMiddleBalanced_det L seamWeight ons_turnRoot t lambda
        (by simp [ons_turnRoot]) hlambda site
  have hrootCompressedAugmented :
      ons_detWalkRoot Mcompressed = ons_detWalkRoot Maugmented :=
    ons_detWalkRoot_eq_of_det_eq_of_small
      Mcompressed Maugmented qCompressed qAugmented
      hqCompressed hqAugmented hentryCompressed hentryAugmented
      hcardCompressed hcardAugmented
      hgeomCompressed hgeomAugmented hdet
  have hrootGauge : ons_detWalkRoot Mphased =
      ons_detWalkRoot Mcompressed := by
    simpa only [Mphased, Mcompressed, scaled, seamScaled] using
      ons_detWalkRoot_KWDecoration_spinGauge L scaled a b ons_turnRoot
  have haff := ons_detWalkRoot_decMiddleBalanced_affine
    L seamWeight ons_turnRoot t lambda (by simp [ons_turnRoot])
      ons_turnRoot_sq hlambda site qAugmented hqAugmented
      hentryAugmented hsmallAugmented hcardAugmented
  change ons_detWalkRoot Mphased = _
  rw [hrootGauge, hrootCompressedAugmented]
  simpa only [Maugmented, seamWeight] using haff

end StatMech.Onsager
