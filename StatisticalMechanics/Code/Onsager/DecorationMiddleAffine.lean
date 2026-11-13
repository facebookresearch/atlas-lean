/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.StateWeightedDeletion









namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_decMiddleAugmentedCol
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (omega t : ℂ) (site : ZMod L × ZMod L) :
    Matrix (ons_Dart L ⊕ Fin 2) (ons_Dart L ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks
    (ons_KWmatDecorationWeightedPhase L
      (ons_scaleDecEdgeWeight decWeight
        (ons_decChainEdge site 1) 0) omega 1 1)
    (t • ons_decMiddleU L decWeight omega site)
    (ons_decMiddleV L decWeight omega 1 1 site)
    0

noncomputable def ons_decMiddleColRowWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ)
    (site : ZMod L × ZMod L) :
    ons_Dart L ⊕ Fin 2 → ℂ
  | .inl _ => 1
  | .inr _ => decWeight (ons_decChainEdge site 1)

noncomputable def ons_decMiddleColColWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ) (t : ℂ) :
    ons_Dart L ⊕ Fin 2 → ℂ
  | .inl d => decWeight s(d, ons_dartRev L d)
  | .inr _ => t

theorem ons_decMiddleAugmentedCol_factor
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t : ℂ) (site : ZMod L × ZMod L) :
    ons_decMiddleAugmentedCol L decWeight omega t site =
      ons_stateWeightedReversibleTurnMatrix ons_decMiddleAugDir omega
        (ons_decMiddleColRowWeight decWeight site)
        (ons_decMiddleColColWeight decWeight t)
        (ons_decMiddleInternalFactor L decWeight site) := by
  ext x y
  rcases x with d₂ | side₂ <;> rcases y with d₁ | side₁
  · simp only [ons_decMiddleAugmentedCol, Matrix.fromBlocks_apply₁₁,
      ons_stateWeightedReversibleTurnMatrix, ons_decMiddleAugDir,
      ons_decMiddleColRowWeight, ons_decMiddleColColWeight,
      ons_decMiddleInternalFactor, one_mul]
    unfold ons_KWmatDecorationWeightedPhase ons_decTransitionWeight
    by_cases hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1
    · rw [if_pos hstep, if_pos hstep]
      simp only [ons_dirPhase_one_one, one_mul]
      rw [ons_scaleMiddle_external]
    · simp [hstep]
  · simp [ons_decMiddleAugmentedCol,
      ons_stateWeightedReversibleTurnMatrix,
      ons_decMiddleColRowWeight, ons_decMiddleColColWeight,
      ons_decMiddleInternalFactor, ons_decMiddleAugDir,
      ons_decMiddleU]
    ring
  · simp [ons_decMiddleAugmentedCol,
      ons_stateWeightedReversibleTurnMatrix,
      ons_decMiddleColRowWeight, ons_decMiddleColColWeight,
      ons_decMiddleInternalFactor, ons_decMiddleAugDir,
      ons_decMiddleV, ons_dirPhase_one_one]
  · simp [ons_decMiddleAugmentedCol,
      ons_stateWeightedReversibleTurnMatrix,
      ons_decMiddleColRowWeight, ons_decMiddleColColWeight,
      ons_decMiddleInternalFactor]

theorem ons_decMiddleAugmentedCol_det
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t : ℂ) (homega : omega ≠ 0)
    (site : ZMod L × ZMod L) :
    (1 - ons_decMiddleAugmentedCol L decWeight omega t site).det =
      (1 - ons_KWmatDecorationWeightedPhase L
        (ons_scaleDecEdgeWeight decWeight
          (ons_decChainEdge site 1) t) omega 1 1).det := by
  let M₀ := ons_KWmatDecorationWeightedPhase L
    (ons_scaleDecEdgeWeight decWeight
      (ons_decChainEdge site 1) 0) omega 1 1
  let U := ons_decMiddleU L decWeight omega site
  let V := ons_decMiddleV L decWeight omega 1 1 site
  have hblock :
      1 - ons_decMiddleAugmentedCol L decWeight omega t site =
        Matrix.fromBlocks (1 - M₀) (-(t • U)) (-V) 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [ons_decMiddleAugmentedCol, M₀, U, V, Matrix.one_apply]
  have hmul : (-(t • U)) * (-V) = t • (U * V) := by
    ext i j
    simp [Matrix.mul_apply]
    ring
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

theorem ons_loopWeight_decMiddleAugmentedCol_eq_row
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t : ℂ) (site : ZMod L × ZMod L)
    (loop : Fin n → ons_Dart L ⊕ Fin 2) :
    ons_loopWeight
        (ons_decMiddleAugmentedCol L decWeight omega t site) loop =
      ons_loopWeight
        (ons_decMiddleAugmented L decWeight omega 1 1 t site) loop := by
  rw [ons_decMiddleAugmentedCol_factor,
    ons_decMiddleAugmented_factor,
    ons_loopWeight_stateWeightedReversibleTurnMatrix,
    ons_loopWeight_stateWeightedReversibleTurnMatrix]
  congr 2
  apply Finset.prod_congr rfl
  intro k hk
  rcases hstate : loop k with d | side
  · simp [ons_decMiddleColRowWeight, ons_decMiddleColColWeight,
      ons_decMiddleRowWeight, ons_decMiddleColWeight]
  · simp [ons_decMiddleColRowWeight, ons_decMiddleColColWeight,
      ons_decMiddleRowWeight, ons_decMiddleColWeight]
    ring

theorem ons_decMiddleAugmentedCol_scaleColumns
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (omega t : ℂ) (site : ZMod L × ZMod L) :
    ons_decMiddleAugmentedCol L decWeight omega t site =
      ons_scaleColumns
        ({Sum.inr 0, Sum.inr 1} :
          Finset (ons_Dart L ⊕ Fin 2)) t
        (ons_decMiddleAugmentedCol L decWeight omega 1 site) := by
  ext x y
  rcases x with d₂ | side₂ <;> rcases y with d₁ | side₁
  · simp [ons_decMiddleAugmentedCol, ons_scaleColumns]
  · fin_cases side₁ <;>
      simp [ons_decMiddleAugmentedCol, ons_scaleColumns]
  · simp [ons_decMiddleAugmentedCol, ons_scaleColumns]
  · fin_cases side₁ <;>
      simp [ons_decMiddleAugmentedCol, ons_scaleColumns]

theorem ons_decMiddleAugmentedCol_lemma5
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I)
    (site : ZMod L × ZMod L)
    (state : ons_Dart L ⊕ Fin 2) :
    ∑ loop ∈ ons_loopSetBoth (n := n) state
        (ons_decMiddleAugRev L state),
      ons_loopWeight
        (ons_decMiddleAugmentedCol L decWeight omega t site) loop = 0 := by
  calc
    (∑ loop ∈ ons_loopSetBoth (n := n) state
        (ons_decMiddleAugRev L state),
      ons_loopWeight
        (ons_decMiddleAugmentedCol L decWeight omega t site) loop) =
      ∑ loop ∈ ons_loopSetBoth (n := n) state
        (ons_decMiddleAugRev L state),
      ons_loopWeight
        (ons_decMiddleAugmented L decWeight omega 1 1 t site) loop := by
          apply Finset.sum_congr rfl
          intro loop hloop
          exact ons_loopWeight_decMiddleAugmentedCol_eq_row
            L decWeight omega t site loop
    _ = 0 := ons_decMiddleAugmented_lemma5
      L decWeight omega t homega hI site state

theorem ons_loopWeight_decMiddleAugmentedCol_loopRev
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I)
    (site : ZMod L × ZMod L)
    (loop : Fin n → ons_Dart L ⊕ Fin 2) :
    ons_loopWeight
        (ons_decMiddleAugmentedCol L decWeight omega t site)
        (ons_involutiveLoopRev (ons_decMiddleAugRev L) loop) =
      ons_loopWeight
        (ons_decMiddleAugmentedCol L decWeight omega t site) loop := by
  rw [ons_loopWeight_decMiddleAugmentedCol_eq_row,
    ons_loopWeight_decMiddleAugmentedCol_eq_row]
  exact ons_loopWeight_decMiddleAugmented_loopRev
    L decWeight omega t homega hI site loop

theorem ons_detWalkRoot_decMiddleAugmentedCol_affine
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I)
    (site : ZMod L × ZMod L)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ x y,
      ‖ons_decMiddleAugmentedCol L decWeight omega t site x y‖ ≤ q)
    (hsmall : q <
      (2 * (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) * q < 1) :
    ons_detWalkRoot
        (ons_decMiddleAugmentedCol L decWeight omega t site) =
      ons_detWalkRoot
          (ons_maskMatrix
            ({Sum.inr 0, Sum.inr 1} :
              Finset (ons_Dart L ⊕ Fin 2))
            (ons_decMiddleAugmentedCol L decWeight omega 1 site)) *
        (1 - t * ∑' s, ons_firstReturnWeight
          (ons_decMiddleAugmentedCol L decWeight omega 1 site)
          (Sum.inr 0) (Sum.inr 1) s) := by
  let Mt := ons_decMiddleAugmentedCol L decWeight omega t site
  let M := ons_decMiddleAugmentedCol L decWeight omega 1 site
  let e : ons_Dart L ⊕ Fin 2 := Sum.inr 0
  let r : ons_Dart L ⊕ Fin 2 := Sum.inr 1
  have hboth : ∀ n : ℕ,
      (∑ loop ∈ ons_loopSetBoth (n := n + 1) e r,
        ons_loopWeight Mt loop) = 0 := by
    intro n
    simpa only [e, r, Mt, ons_decMiddleAugRev] using
      ons_decMiddleAugmentedCol_lemma5
        (n := n + 1) L decWeight omega t homega hI site e
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
        (ons_loopWeight_decMiddleAugmentedCol_loopRev
          L decWeight omega t homega hI site) e
  have hdel := ons_detWalkRoot_matrix_delete_pair Mt e r
    (by simp [e, r]) q hq hentry hsmall hcard hboth hsymm
  have hscale : Mt =
      ons_scaleColumns ({e, r} : Finset (ons_Dart L ⊕ Fin 2)) t M := by
    simpa only [Mt, M, e, r] using
      ons_decMiddleAugmentedCol_scaleColumns
        L decWeight omega t site
  have hmask :
      ons_maskMatrix ({e, r} : Finset (ons_Dart L ⊕ Fin 2)) Mt =
        ons_maskMatrix ({e, r} : Finset (ons_Dart L ⊕ Fin 2)) M := by
    rw [hscale]
    exact ons_mask_scaleColumns_absorb _ _ _ _ Finset.Subset.rfl
  have hsum :
      (∑' s, ons_firstReturnWeight Mt e r s) =
        t * ∑' s, ons_firstReturnWeight M e r s := by
    rw [hscale]
    exact ons_tsum_firstReturnWeight_scale M e r t
  simpa only [Mt, M, e, r] using hdel.trans (by rw [hmask, hsum])

theorem ons_detWalkRoot_decMiddleAugmented_spinGauge
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (omega t : ℂ) (site : ZMod L × ZMod L) :
    ons_detWalkRoot
        (ons_decMiddleAugmented L decWeight omega
          (ons_spinPhase L a) (ons_spinPhase L b) t site) =
      ons_detWalkRoot
        (ons_decMiddleAugmented L
          (ons_spinSeamDecWeight decWeight a b)
          omega 1 1 t site) := by
  apply ons_detWalkRoot_eq_of_loopWeight_eq
  intro n loop
  rw [ons_decMiddleAugmented_spinGauge]
  exact ons_loopWeight_diagonalGaugeMatrix
    (ons_decMiddleStateGauge L a b site)
    (ons_decMiddleStateGauge_ne_zero L a b site)
    (ons_decMiddleAugmented L
      (ons_spinSeamDecWeight decWeight a b)
      omega 1 1 t site) loop

theorem ons_detWalkRoot_decMiddleAugmented_row_eq_col
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega t : ℂ) (site : ZMod L × ZMod L) :
    ons_detWalkRoot
        (ons_decMiddleAugmented L decWeight omega 1 1 t site) =
      ons_detWalkRoot
        (ons_decMiddleAugmentedCol L decWeight omega t site) := by
  apply ons_detWalkRoot_eq_of_loopWeight_eq
  intro n loop
  exact (ons_loopWeight_decMiddleAugmentedCol_eq_row
    L decWeight omega t site loop).symm



theorem ons_detWalkRoot_scaleMiddle_affine_of_bounds
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (omega t : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I)
    (site : ZMod L × ZMod L)
    (qCompressed qAugmented : ℝ)
    (hqCompressed : 0 ≤ qCompressed)
    (hqAugmented : 0 ≤ qAugmented)
    (hentryCompressed : ∀ x y,
      ‖ons_KWmatDecorationWeightedPhase L
        (ons_scaleDecEdgeWeight decWeight
          (ons_decChainEdge site 1) t)
        omega (ons_spinPhase L a) (ons_spinPhase L b) x y‖ ≤
          qCompressed)
    (hentryAugmentedRow : ∀ x y,
      ‖ons_decMiddleAugmented L decWeight omega
        (ons_spinPhase L a) (ons_spinPhase L b) t site x y‖ ≤
          qAugmented)
    (hentryAugmentedCol : ∀ x y,
      ‖ons_decMiddleAugmentedCol L
        (ons_spinSeamDecWeight decWeight a b)
        omega t site x y‖ ≤ qAugmented)
    (hsmallCompressed : qCompressed <
      (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
    (hsmallAugmented : qAugmented <
      (2 * (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) ^ 2)⁻¹) :
    ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 1) t)
          omega (ons_spinPhase L a) (ons_spinPhase L b)) =
      ons_detWalkRoot
          (ons_maskMatrix
            ({Sum.inr 0, Sum.inr 1} :
              Finset (ons_Dart L ⊕ Fin 2))
            (ons_decMiddleAugmentedCol L
              (ons_spinSeamDecWeight decWeight a b)
              omega 1 site)) *
        (1 - t * ∑' s, ons_firstReturnWeight
          (ons_decMiddleAugmentedCol L
            (ons_spinSeamDecWeight decWeight a b)
            omega 1 site)
          (Sum.inr 0) (Sum.inr 1) s) := by
  let Mcompressed := ons_KWmatDecorationWeightedPhase L
    (ons_scaleDecEdgeWeight decWeight
      (ons_decChainEdge site 1) t)
    omega (ons_spinPhase L a) (ons_spinPhase L b)
  let Mrow := ons_decMiddleAugmented L decWeight omega
    (ons_spinPhase L a) (ons_spinPhase L b) t site
  let seamWeight := ons_spinSeamDecWeight decWeight a b
  let Mcol := ons_decMiddleAugmentedCol L seamWeight omega t site
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
  have hdet : (1 - Mcompressed).det = (1 - Mrow).det := by
    symm
    simpa only [Mcompressed, Mrow] using
      ons_decMiddleAugmented_det L decWeight omega
        (ons_spinPhase L a) (ons_spinPhase L b) t homega site
  have hrootCompressedRow :
      ons_detWalkRoot Mcompressed = ons_detWalkRoot Mrow :=
    ons_detWalkRoot_eq_of_det_eq_of_small
      Mcompressed Mrow qCompressed qAugmented
      hqCompressed hqAugmented hentryCompressed hentryAugmentedRow
      hcardCompressed hcardAugmented
      hgeomCompressed hgeomAugmented hdet
  have hrootRowSeam :
      ons_detWalkRoot Mrow =
        ons_detWalkRoot
          (ons_decMiddleAugmented L seamWeight omega 1 1 t site) := by
    simpa only [Mrow, seamWeight] using
      ons_detWalkRoot_decMiddleAugmented_spinGauge
        L decWeight a b omega t site
  have hrootRowCol :
      ons_detWalkRoot
          (ons_decMiddleAugmented L seamWeight omega 1 1 t site) =
        ons_detWalkRoot Mcol := by
    simpa only [Mcol, seamWeight] using
      ons_detWalkRoot_decMiddleAugmented_row_eq_col
        L seamWeight omega t site
  have haff := ons_detWalkRoot_decMiddleAugmentedCol_affine
    L seamWeight omega t homega hI site qAugmented hqAugmented
      hentryAugmentedCol hsmallAugmented hcardAugmented
  change ons_detWalkRoot Mcompressed = _
  rw [hrootCompressedRow, hrootRowSeam, hrootRowCol]
  simpa only [Mcol, seamWeight] using haff

end StatMech.Onsager
