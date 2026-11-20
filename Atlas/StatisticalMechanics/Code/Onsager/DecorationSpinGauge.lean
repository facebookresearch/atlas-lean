/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationInternalMiddle
import Code.Onsager.TorusLoopHomology










namespace StatMech.Onsager

open BigOperators

@[simp] theorem ons_dirPhase_one_one (mu : Fin 4) :
    ons_dirPhase 1 1 mu = 1 := by
  fin_cases mu <;> simp [ons_dirPhase]

noncomputable def ons_spinVertexGauge
    (L : ℕ) (a b : Fin 2) (site : ZMod L × ZMod L) : ℂ :=
  ons_spinPhase L a ^ (site.1.val : ℤ) *
    ons_spinPhase L b ^ (site.2.val : ℤ)

noncomputable def ons_spinDartSeamSign
    {L : ℕ} (a b : Fin 2) (d : ons_Dart L) : ℂ :=
  (-1 : ℂ) ^ ((a.val : ℤ) * ons_xWrapSign d +
    (b.val : ℤ) * ons_yWrapSign d)

theorem ons_spinVertexGauge_ne_zero
    (L : ℕ) (a b : Fin 2) (site : ZMod L × ZMod L) :
    ons_spinVertexGauge L a b site ≠ 0 := by
  unfold ons_spinVertexGauge
  exact mul_ne_zero
    (zpow_ne_zero _ (ons_spinPhase_ne_zero L a))
    (zpow_ne_zero _ (ons_spinPhase_ne_zero L b))

theorem ons_spinPhase_zpow_x_gauge
    (L : ℕ) [Fact (2 < L)] (a : Fin 2) (d : ons_Dart L) :
    ons_spinPhase L a ^ ons_dirExponentX d.2 *
        ons_spinPhase L a ^ (d.1.1.val : ℤ) =
      (-1 : ℂ) ^ ((a.val : ℤ) * ons_xWrapSign d) *
        ons_spinPhase L a ^
          ((ons_dirStep L d.2 d.1).1.val : ℤ) := by
  let u := ons_spinPhase L a
  have hu : u ≠ 0 := ons_spinPhase_ne_zero L a
  have hpow : u ^ (L : ℤ) = (-1 : ℂ) ^ (a.val : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L a
  have hexp := ons_dirExponentX_eq_val_diff_add_wrap d
  have hadd : ons_dirExponentX d.2 + (d.1.1.val : ℤ) =
      ((ons_dirStep L d.2 d.1).1.val : ℤ) +
        (L : ℤ) * ons_xWrapSign d := by
    omega
  calc
    u ^ ons_dirExponentX d.2 * u ^ (d.1.1.val : ℤ) =
        u ^ (ons_dirExponentX d.2 + (d.1.1.val : ℤ)) :=
      (zpow_add₀ hu _ _).symm
    _ = u ^ (((ons_dirStep L d.2 d.1).1.val : ℤ) +
        (L : ℤ) * ons_xWrapSign d) := by rw [hadd]
    _ = u ^ ((ons_dirStep L d.2 d.1).1.val : ℤ) *
        u ^ ((L : ℤ) * ons_xWrapSign d) :=
      zpow_add₀ hu _ _
    _ = u ^ ((ons_dirStep L d.2 d.1).1.val : ℤ) *
        (u ^ (L : ℤ)) ^ ons_xWrapSign d := by
      rw [_root_.zpow_mul]
    _ = u ^ ((ons_dirStep L d.2 d.1).1.val : ℤ) *
        ((-1 : ℂ) ^ (a.val : ℤ)) ^ ons_xWrapSign d := by
      rw [hpow]
    _ = (-1 : ℂ) ^ ((a.val : ℤ) * ons_xWrapSign d) *
        u ^ ((ons_dirStep L d.2 d.1).1.val : ℤ) := by
      rw [← _root_.zpow_mul]
      ring

theorem ons_spinPhase_zpow_y_gauge
    (L : ℕ) [Fact (2 < L)] (b : Fin 2) (d : ons_Dart L) :
    ons_spinPhase L b ^ ons_dirExponentY d.2 *
        ons_spinPhase L b ^ (d.1.2.val : ℤ) =
      (-1 : ℂ) ^ ((b.val : ℤ) * ons_yWrapSign d) *
        ons_spinPhase L b ^
          ((ons_dirStep L d.2 d.1).2.val : ℤ) := by
  let v := ons_spinPhase L b
  have hv : v ≠ 0 := ons_spinPhase_ne_zero L b
  have hpow : v ^ (L : ℤ) = (-1 : ℂ) ^ (b.val : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L b
  have hexp := ons_dirExponentY_eq_val_diff_add_wrap d
  have hadd : ons_dirExponentY d.2 + (d.1.2.val : ℤ) =
      ((ons_dirStep L d.2 d.1).2.val : ℤ) +
        (L : ℤ) * ons_yWrapSign d := by
    omega
  calc
    v ^ ons_dirExponentY d.2 * v ^ (d.1.2.val : ℤ) =
        v ^ (ons_dirExponentY d.2 + (d.1.2.val : ℤ)) :=
      (zpow_add₀ hv _ _).symm
    _ = v ^ (((ons_dirStep L d.2 d.1).2.val : ℤ) +
        (L : ℤ) * ons_yWrapSign d) := by rw [hadd]
    _ = v ^ ((ons_dirStep L d.2 d.1).2.val : ℤ) *
        v ^ ((L : ℤ) * ons_yWrapSign d) :=
      zpow_add₀ hv _ _
    _ = v ^ ((ons_dirStep L d.2 d.1).2.val : ℤ) *
        (v ^ (L : ℤ)) ^ ons_yWrapSign d := by
      rw [_root_.zpow_mul]
    _ = v ^ ((ons_dirStep L d.2 d.1).2.val : ℤ) *
        ((-1 : ℂ) ^ (b.val : ℤ)) ^ ons_yWrapSign d := by
      rw [hpow]
    _ = (-1 : ℂ) ^ ((b.val : ℤ) * ons_yWrapSign d) *
        v ^ ((ons_dirStep L d.2 d.1).2.val : ℤ) := by
      rw [← _root_.zpow_mul]
      ring



theorem ons_dirPhase_spin_mul_vertexGauge
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) d.2 *
        ons_spinVertexGauge L a b d.1 =
      ons_spinDartSeamSign a b d *
        ons_spinVertexGauge L a b (ons_dirStep L d.2 d.1) := by
  rw [ons_dirPhase_eq_zpow]
  unfold ons_spinVertexGauge ons_spinDartSeamSign
  have hx := ons_spinPhase_zpow_x_gauge L a d
  have hy := ons_spinPhase_zpow_y_gauge L b d
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  calc
    ons_spinPhase L a ^ ons_dirExponentX d.2 *
          ons_spinPhase L b ^ ons_dirExponentY d.2 *
        (ons_spinPhase L a ^ (d.1.1.val : ℤ) *
          ons_spinPhase L b ^ (d.1.2.val : ℤ)) =
        (ons_spinPhase L a ^ ons_dirExponentX d.2 *
          ons_spinPhase L a ^ (d.1.1.val : ℤ)) *
        (ons_spinPhase L b ^ ons_dirExponentY d.2 *
          ons_spinPhase L b ^ (d.1.2.val : ℤ)) := by ring
    _ = ((-1 : ℂ) ^ ((a.val : ℤ) * ons_xWrapSign d) *
          ons_spinPhase L a ^
            ((ons_dirStep L d.2 d.1).1.val : ℤ)) *
        ((-1 : ℂ) ^ ((b.val : ℤ) * ons_yWrapSign d) *
          ons_spinPhase L b ^
            ((ons_dirStep L d.2 d.1).2.val : ℤ)) := by
      rw [hx, hy]
    _ = _ := by ring

theorem ons_neg_one_zpow_sq (m : ℤ) :
    ((-1 : ℂ) ^ m) ^ 2 = 1 := by
  rw [pow_two, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    show m + m = 2 * m by ring, _root_.zpow_mul]
  norm_num


theorem ons_spinDartSeamSign_rev
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    ons_spinDartSeamSign a b (ons_dartRev L d) =
      ons_spinDartSeamSign a b d := by
  let p := ons_spinVertexGauge L a b d.1
  let q := ons_spinVertexGauge L a b (ons_dirStep L d.2 d.1)
  let phase := ons_dirPhase
    (ons_spinPhase L a) (ons_spinPhase L b) d.2
  let sd := ons_spinDartSeamSign a b d
  let sr := ons_spinDartSeamSign a b (ons_dartRev L d)
  have hp : p ≠ 0 := ons_spinVertexGauge_ne_zero L a b d.1
  have hq : q ≠ 0 :=
    ons_spinVertexGauge_ne_zero L a b (ons_dirStep L d.2 d.1)
  have hphase : phase ≠ 0 := by
    rcases d with ⟨site, mu⟩
    fin_cases mu <;>
      simp [phase, ons_dirPhase, ons_spinPhase_ne_zero]
  have hforward : phase * p = sd * q := by
    simpa only [phase, p, q, sd] using
      ons_dirPhase_spin_mul_vertexGauge L a b d
  have hreverse : phase⁻¹ * q = sr * p := by
    have h := ons_dirPhase_spin_mul_vertexGauge
      L a b (ons_dartRev L d)
    simpa only [phase, p, q, sr, ons_dartRev,
      ons_dirPhase_spin_opposite, ons_dirStep_opposite] using h
  have hprod : sd * sr = 1 := by
    apply mul_right_cancel₀ (mul_ne_zero hp hq)
    calc
      sd * sr * (p * q) = (sd * q) * (sr * p) := by ring
      _ = (phase * p) * (phase⁻¹ * q) := by
        rw [hforward, hreverse]
      _ = (phase * phase⁻¹) * (p * q) := by ring
      _ = p * q := by rw [mul_inv_cancel₀ hphase, one_mul]
      _ = 1 * (p * q) := by ring
  have hsq : sd ^ 2 = 1 := by
    exact ons_neg_one_zpow_sq _
  calc
    sr = 1 * sr := by ring
    _ = (sd * sd) * sr := by rw [← pow_two, hsq]
    _ = sd * (sd * sr) := by ring
    _ = sd := by rw [hprod]; ring


noncomputable def ons_spinSeamDecWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ)
    (a b : Fin 2) (edge : ons_DecEdge L) : ℂ := by
  classical
  exact if h : ons_decIsExternal edge then
    ons_spinDartSeamSign a b (Classical.choose h) * decWeight edge
  else decWeight edge

@[simp] theorem ons_spinSeamDecWeight_external
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (d : ons_Dart L) :
    ons_spinSeamDecWeight decWeight a b s(d, ons_dartRev L d) =
      ons_spinDartSeamSign a b d *
        decWeight s(d, ons_dartRev L d) := by
  classical
  unfold ons_spinSeamDecWeight
  split_ifs with h
  · let chosen := Classical.choose h
    have hchosen : s(d, ons_dartRev L d) =
        s(chosen, ons_dartRev L chosen) := Classical.choose_spec h
    have hor : chosen = d ∨ chosen = ons_dartRev L d :=
      (ons_externalDecoratedEdge_eq_iff L d chosen).mp hchosen.symm
    change ons_spinDartSeamSign a b chosen *
      decWeight s(d, ons_dartRev L d) = _
    rcases hor with heq | hrev
    · rw [heq]
    · rw [hrev, ons_spinDartSeamSign_rev]
  · exact (h ⟨d, rfl⟩).elim

@[simp] theorem ons_spinSeamDecWeight_chain
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (site : ZMod L × ZMod L) (i : Fin 3) :
    ons_spinSeamDecWeight decWeight a b (ons_decChainEdge site i) =
      decWeight (ons_decChainEdge site i) := by
  classical
  unfold ons_spinSeamDecWeight
  rw [dif_neg (ons_decChainEdge_not_external L site i)]

noncomputable def ons_diagonalGaugeMatrix
    {E : Type*} (gauge : E → ℂ) (M : Matrix E E ℂ) :
    Matrix E E ℂ :=
  fun i j ↦ gauge i * M i j * (gauge j)⁻¹

theorem ons_loopWeight_diagonalGaugeMatrix
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n] (gauge : E → ℂ)
    (hgauge : ∀ e, gauge e ≠ 0) (M : Matrix E E ℂ)
    (loop : Fin n → E) :
    ons_loopWeight (ons_diagonalGaugeMatrix gauge M) loop =
      ons_loopWeight M loop := by
  unfold ons_loopWeight ons_diagonalGaugeMatrix
  simp_rw [mul_assoc]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hreindex : (∏ k, gauge (loop (k + 1))) =
      ∏ k, gauge (loop k) :=
    Equiv.prod_comp (Equiv.addRight (1 : Fin n))
      (fun k ↦ gauge (loop k))
  rw [Finset.prod_inv_distrib, hreindex]
  have hprod : (∏ k, gauge (loop k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k hk ↦ hgauge _)
  calc
    (∏ x, gauge (loop x)) *
          ((∏ x, M (loop x) (loop (x + 1))) *
            (∏ k, gauge (loop k))⁻¹) =
        (∏ x, M (loop x) (loop (x + 1))) *
          ((∏ k, gauge (loop k)) *
            (∏ k, gauge (loop k))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hprod, mul_one]

theorem ons_decTransitionWeight_spinSeam
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (d₂ d₁ : ons_Dart L) :
    ons_decTransitionWeight L (ons_spinSeamDecWeight decWeight a b) d₂ d₁ =
      ons_spinDartSeamSign a b d₁ *
        ons_decTransitionWeight L decWeight d₂ d₁ := by
  unfold ons_decTransitionWeight
  rw [ons_spinSeamDecWeight_external]
  have hchain :
      (∏ i ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2,
        ons_spinSeamDecWeight decWeight a b
          (ons_decChainEdge d₂.1 i)) =
        ∏ i ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2,
          decWeight (ons_decChainEdge d₂.1 i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [ons_spinSeamDecWeight_chain]
  rw [hchain]
  ring



theorem ons_KWmatDecorationWeightedPhase_spinGauge
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (omega : ℂ) :
    ons_KWmatDecorationWeightedPhase L decWeight omega
        (ons_spinPhase L a) (ons_spinPhase L b) =
      ons_diagonalGaugeMatrix
        (fun d : ons_Dart L ↦ ons_spinVertexGauge L a b d.1)
        (ons_KWmatDecorationWeightedPhase L
          (ons_spinSeamDecWeight decWeight a b) omega 1 1) := by
  ext d₂ d₁
  by_cases hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1
  · have hg := ons_dirPhase_spin_mul_vertexGauge L a b d₁
    have hne := ons_spinVertexGauge_ne_zero L a b d₁.1
    unfold ons_diagonalGaugeMatrix
    simp only
    unfold ons_KWmatDecorationWeightedPhase
    simp only [hstep, if_pos, ons_dirPhase_one_one, one_mul]
    rw [ons_decTransitionWeight_spinSeam]
    field_simp [hne]
    linear_combination hg *
      (ons_decTransitionWeight L decWeight d₂ d₁ *
        ons_turnW omega d₁.2 d₂.2)
  · unfold ons_KWmatDecorationWeightedPhase ons_diagonalGaugeMatrix
    simp [hstep]

theorem ons_decMiddleU_spinSeam
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (omega : ℂ) (site : ZMod L × ZMod L) :
    ons_decMiddleU L (ons_spinSeamDecWeight decWeight a b) omega site =
      ons_decMiddleU L decWeight omega site := by
  ext d side
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [ons_decMiddleU, ons_decMiddleDestFactor]

theorem ons_decMiddleSourceFactor_spinSeam
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (site : ZMod L × ZMod L) (mu : Fin 4) :
    ons_decMiddleSourceFactor (ons_spinSeamDecWeight decWeight a b)
        site mu =
      ons_decMiddleSourceFactor decWeight site mu := by
  fin_cases mu <;>
    simp [ons_decMiddleSourceFactor]

theorem ons_decMiddleV_spinGauge
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (omega : ℂ) (site : ZMod L × ZMod L) :
    ons_decMiddleV L decWeight omega
        (ons_spinPhase L a) (ons_spinPhase L b) site =
      fun side d ↦
        ons_spinVertexGauge L a b site *
          ons_decMiddleV L (ons_spinSeamDecWeight decWeight a b)
            omega 1 1 site side d *
          (ons_spinVertexGauge L a b d.1)⁻¹ := by
  ext side d
  unfold ons_decMiddleV
  by_cases h : site = ons_dirStep L d.2 d.1 ∧
      ons_decMiddleSide d.2 = side
  · rw [if_pos h, if_pos h]
    rw [ons_spinSeamDecWeight_chain,
      ons_spinSeamDecWeight_external,
      ons_decMiddleSourceFactor_spinSeam]
    simp only [ons_dirPhase_one_one, one_mul]
    have hg := ons_dirPhase_spin_mul_vertexGauge L a b d
    rw [← h.1] at hg
    have hne := ons_spinVertexGauge_ne_zero L a b d.1
    field_simp [hne]
    linear_combination hg *
      (decWeight (ons_decChainEdge site 1) *
        decWeight s(d, ons_dartRev L d) *
        ons_decMiddleSourceFactor decWeight site d.2 *
        ons_turnW omega d.2 (ons_decMiddleDir side))
  · rw [if_neg h, if_neg h]
    ring

theorem ons_spinSeamDecWeight_scale_chain_one
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (site : ZMod L × ZMod L) (t : ℂ) :
    ons_spinSeamDecWeight
        (ons_scaleDecEdgeWeight decWeight
          (ons_decChainEdge site 1) t) a b =
      ons_scaleDecEdgeWeight
        (ons_spinSeamDecWeight decWeight a b)
        (ons_decChainEdge site 1) t := by
  funext edge
  classical
  by_cases hext : ons_decIsExternal edge
  · have hne : edge ≠ ons_decChainEdge site 1 := by
      intro heq
      apply ons_decChainEdge_not_external L site 1
      rwa [← heq]
    simp [ons_spinSeamDecWeight, ons_scaleDecEdgeWeight, hext, hne]
  · simp [ons_spinSeamDecWeight, ons_scaleDecEdgeWeight, hext]

noncomputable def ons_decMiddleStateGauge
    (L : ℕ) (a b : Fin 2) (site : ZMod L × ZMod L) :
    ons_Dart L ⊕ Fin 2 → ℂ
  | .inl d => ons_spinVertexGauge L a b d.1
  | .inr _ => ons_spinVertexGauge L a b site

theorem ons_decMiddleStateGauge_ne_zero
    (L : ℕ) (a b : Fin 2) (site : ZMod L × ZMod L) :
    ∀ state, ons_decMiddleStateGauge L a b site state ≠ 0 := by
  rintro (d | side)
  · exact ons_spinVertexGauge_ne_zero L a b d.1
  · exact ons_spinVertexGauge_ne_zero L a b site

theorem ons_decMiddleU_spinGauge
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (omega : ℂ) (site : ZMod L × ZMod L)
    (d : ons_Dart L) (side : Fin 2) :
    ons_decMiddleU L decWeight omega site d side =
      ons_spinVertexGauge L a b d.1 *
        ons_decMiddleU L (ons_spinSeamDecWeight decWeight a b)
          omega site d side *
        (ons_spinVertexGauge L a b site)⁻¹ := by
  rw [ons_decMiddleU_spinSeam]
  unfold ons_decMiddleU
  by_cases h : d.1 = site ∧ ons_decMiddleSide d.2 = side
  · simp only [h, true_and, if_true]
    have hne := ons_spinVertexGauge_ne_zero L a b site
    field_simp [hne]
  · simp [h]



theorem ons_decMiddleAugmented_spinGauge
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (omega t : ℂ) (site : ZMod L × ZMod L) :
    ons_decMiddleAugmented L decWeight omega
        (ons_spinPhase L a) (ons_spinPhase L b) t site =
      ons_diagonalGaugeMatrix
        (ons_decMiddleStateGauge L a b site)
        (ons_decMiddleAugmented L
          (ons_spinSeamDecWeight decWeight a b)
          omega 1 1 t site) := by
  ext i j
  cases i with
  | inl d₂ =>
      cases j with
      | inl d₁ =>
          have hmatrix := congrFun₂
            (ons_KWmatDecorationWeightedPhase_spinGauge
              L (ons_scaleDecEdgeWeight decWeight
                (ons_decChainEdge site 1) 0) a b omega) d₂ d₁
          simpa [ons_decMiddleAugmented, ons_diagonalGaugeMatrix,
            ons_decMiddleStateGauge,
            ons_spinSeamDecWeight_scale_chain_one] using hmatrix
      | inr side =>
          simpa [ons_decMiddleAugmented, ons_diagonalGaugeMatrix,
            ons_decMiddleStateGauge] using
            ons_decMiddleU_spinGauge
              L decWeight a b omega site d₂ side
  | inr side =>
      cases j with
      | inl d₁ =>
          have hV := congrFun₂
            (ons_decMiddleV_spinGauge
              L decWeight a b omega site) side d₁
          simp only [ons_decMiddleAugmented,
            ons_diagonalGaugeMatrix, ons_decMiddleStateGauge,
            Matrix.fromBlocks_apply₂₁, Matrix.smul_apply, smul_eq_mul]
          rw [hV]
          ring
      | inr side' =>
          simp [ons_decMiddleAugmented, ons_diagonalGaugeMatrix,
            ons_decMiddleStateGauge]

end StatMech.Onsager
