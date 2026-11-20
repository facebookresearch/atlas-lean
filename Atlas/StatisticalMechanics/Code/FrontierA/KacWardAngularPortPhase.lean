/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAngularPortEmbedding
import Code.FrontierA.KacWardRationalNormalization





namespace StatMech.FrontierA

open SimpleGraph

theorem kwAngularUnit_chord_of_lt {a b : ℝ} (hab : a < b) :
    kwAngularUnit b - kwAngularUnit a =
      ((2 * Real.sin ((b - a) / 2) : ℝ) : ℂ) *
        kwAngularUnit ((a + b) / 2 + Real.pi / 2) := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, kwAngularUnit_re]
    rw [Real.cos_sub_cos, Real.cos_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, kwAngularUnit_im]
    rw [Real.sin_sub_sin, Real.sin_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring

theorem kwAngularUnit_chord_of_gt {a b : ℝ} (hba : b < a) :
    kwAngularUnit b - kwAngularUnit a =
      ((2 * Real.sin ((a - b) / 2) : ℝ) : ℂ) *
        kwAngularUnit ((a + b) / 2 - Real.pi / 2) := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, kwAngularUnit_re]
    rw [Real.cos_sub_cos, Real.cos_sub, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    rw [show (b - a) / 2 = -((a - b) / 2) by ring, Real.sin_neg]
    ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, kwAngularUnit_im]
    rw [Real.sin_sub_sin, Real.sin_sub, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    rw [show (b - a) / 2 = -((a - b) / 2) by ring, Real.sin_neg]
    ring


noncomputable def KWAngularPortRadiusData.rawDartDirection
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) : ℝ :=
  if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then
    (embedding.dartAngle (kwDartOfPort G d.fst)).toReal
  else if kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
      kwOrderedPortRank (kwAngularPortOrder embedding) d.snd then
    ((embedding.dartAngle (kwDartOfPort G d.fst)).toReal +
      (embedding.dartAngle (kwDartOfPort G d.snd)).toReal) / 2 + Real.pi / 2
  else
    ((embedding.dartAngle (kwDartOfPort G d.fst)).toReal +
      (embedding.dartAngle (kwDartOfPort G d.snd)).toReal) / 2 - Real.pi / 2

theorem KWAngularPortRadiusData.realizedDartVector_pos_raw
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) :
    ∃ c : ℝ, 0 < c ∧
      (data.toStraightLineEmbedding.vertex d.snd -
        data.toStraightLineEmbedding.vertex d.fst) =
        (c : ℂ) * kwAngularUnit (data.rawDartDirection d) := by
  classical
  by_cases hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · obtain ⟨c, hc, hvec⟩ := kwAngularPortVertex_matching_positive
      embedding (r := (data.radius : ℝ)) hd
        (by linarith [data.edge_long (kwDartOfPort G d.fst)])
    refine ⟨c, hc, ?_⟩
    change kwAngularPortVertex embedding (data.radius : ℝ) d.snd -
        kwAngularPortVertex embedding (data.radius : ℝ) d.fst = _
    rw [hvec, embedding.dartUnit_eq_angularUnit]
    simp [KWAngularPortRadiusData.rawDartDirection, hd]
  · have dd := (kwOrderedDartPortSplitGraph_adj G
        (kwAngularPortOrder embedding) d.fst d.snd).mp d.adj |>.resolve_left hd
    let a := (embedding.dartAngle (kwDartOfPort G d.fst)).toReal
    let b := (embedding.dartAngle (kwDartOfPort G d.snd)).toReal
    have howner : d.fst.1 = d.snd.1 := dd.1
    have hvec :
        data.toStraightLineEmbedding.vertex d.snd -
            data.toStraightLineEmbedding.vertex d.fst =
          (data.radius : ℂ) *
            (kwAngularUnit b - kwAngularUnit a) := by
      change kwAngularPortVertex embedding (data.radius : ℝ) d.snd -
          kwAngularPortVertex embedding (data.radius : ℝ) d.fst = _
      unfold kwAngularPortVertex
      rw [← howner, embedding.dartUnit_eq_angularUnit,
        embedding.dartUnit_eq_angularUnit]
      dsimp only [a, b]
      ring
    by_cases hinc : kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
        kwOrderedPortRank (kwAngularPortOrder embedding) d.snd
    · have hab : a < b :=
        (kwAngularPortOrder_rank_lt_iff_angle_lt embedding howner).mp hinc
      have hsin : 0 < Real.sin ((b - a) / 2) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · linarith
        · nlinarith [Real.Angle.neg_pi_lt_toReal
              (embedding.dartAngle (kwDartOfPort G d.fst)),
            Real.Angle.toReal_le_pi
              (embedding.dartAngle (kwDartOfPort G d.snd)), Real.pi_pos]
      refine ⟨2 * (data.radius : ℝ) * Real.sin ((b - a) / 2),
        mul_pos (mul_pos (by norm_num) (by exact_mod_cast data.radius_pos)) hsin, ?_⟩
      rw [hvec, kwAngularUnit_chord_of_lt hab]
      simp [KWAngularPortRadiusData.rawDartDirection, hd, hinc, a, b]
      push_cast
      ring
    · have hdec : kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by
        rcases dd.2 with h | h <;> omega
      have hba : b < a :=
        (kwAngularPortOrder_rank_lt_iff_angle_lt embedding howner.symm).mp hdec
      have hsin : 0 < Real.sin ((a - b) / 2) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · linarith
        · nlinarith [Real.Angle.neg_pi_lt_toReal
              (embedding.dartAngle (kwDartOfPort G d.snd)),
            Real.Angle.toReal_le_pi
              (embedding.dartAngle (kwDartOfPort G d.fst)), Real.pi_pos]
      refine ⟨2 * (data.radius : ℝ) * Real.sin ((a - b) / 2),
        mul_pos (mul_pos (by norm_num) (by exact_mod_cast data.radius_pos)) hsin, ?_⟩
      rw [hvec, kwAngularUnit_chord_of_gt hba]
      simp [KWAngularPortRadiusData.rawDartDirection, hd, hinc, a, b]
      push_cast
      ring

theorem kwAngularUnit_ne_zero (a : ℝ) : kwAngularUnit a ≠ 0 := by
  unfold kwAngularUnit
  exact Complex.exp_ne_zero _



theorem KWAngularPortRadiusData.realizedTurnPhase_eq_raw
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d e : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) :
    data.toStraightLineEmbedding.turnPhase d e =
      kwAngleTurnPhase (data.rawDartDirection d : Real.Angle)
        (data.rawDartDirection e : Real.Angle) := by
  obtain ⟨c, hc, hd⟩ := data.realizedDartVector_pos_raw d
  obtain ⟨f, hf, he⟩ := data.realizedDartVector_pos_raw e
  rw [← data.toStraightLineEmbedding.vectorTurnPhase_eq_turnPhase d e,
    hd, he, kwVectorTurnPhase_pos_scales c f hc hf
      (kwAngularUnit (data.rawDartDirection d))
      (kwAngularUnit (data.rawDartDirection e))
      (kwAngularUnit_ne_zero _) (kwAngularUnit_ne_zero _)]
  unfold kwVectorTurnPhase kwAngularUnit
  congr 1
  · simp only [Complex.arg_exp_mul_I, Real.Angle.coe_toIocMod]
  · simp only [Complex.arg_exp_mul_I, Real.Angle.coe_toIocMod]


noncomputable def kwRawDirectionRoot (a : ℝ) : ℂ :=
  Complex.exp (((a : ℂ) * Complex.I) / 2)

theorem kwRawDirectionRoot_ne_zero (a : ℝ) : kwRawDirectionRoot a ≠ 0 :=
  Complex.exp_ne_zero _

theorem kwAngleTurnPhase_coe_eq_rootRatio
    (a b : ℝ) (hlower : -Real.pi < b - a)
    (hupper : b - a ≤ Real.pi) :
    kwAngleTurnPhase (a : Real.Angle) (b : Real.Angle) =
      (kwRawDirectionRoot a)⁻¹ * kwRawDirectionRoot b := by
  unfold kwAngleTurnPhase kwRawDirectionRoot
  have hreal : (((b : ℝ) : Real.Angle) - (a : Real.Angle)).toReal = b - a := by
    rw [← Real.Angle.coe_sub]
    exact Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hlower, hupper⟩
  rw [hreal, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem kwRawDirectionRoot_add_pi_inv (a : ℝ) :
    (kwRawDirectionRoot (a + Real.pi))⁻¹ =
      -Complex.I * (kwRawDirectionRoot a)⁻¹ := by
  unfold kwRawDirectionRoot
  rw [← Complex.exp_neg, ← Complex.exp_neg,
    show -((((a + Real.pi : ℝ) : ℂ) * Complex.I) / 2) =
      (-(Real.pi : ℂ) / 2 * Complex.I) +
        -(((a : ℂ) * Complex.I) / 2) by push_cast; ring,
    Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I]

theorem kwRawDirectionRoot_sub_pi_inv (a : ℝ) :
    (kwRawDirectionRoot (a - Real.pi))⁻¹ =
      Complex.I * (kwRawDirectionRoot a)⁻¹ := by
  unfold kwRawDirectionRoot
  rw [← Complex.exp_neg, ← Complex.exp_neg,
    show -((((a - Real.pi : ℝ) : ℂ) * Complex.I) / 2) =
      ((Real.pi : ℂ) / 2 * Complex.I) +
        -(((a : ℂ) * Complex.I) / 2) by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_div_two_mul_I]

theorem kwPortAngleRoot_eq_rawDirectionRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (p : KWDartPort G) :
    kwPortAngleRoot embedding p = kwRawDirectionRoot
      (embedding.dartAngle (kwDartOfPort G p)).toReal := by
  rfl




noncomputable def KWAngularPortRadiusData.phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) : ℂ :=
  if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then 1
  else kwRawDirectionRoot (data.rawDartDirection d)

theorem KWAngularPortRadiusData.phaseGauge_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) :
    data.phaseGauge d ≠ 0 := by
  unfold KWAngularPortRadiusData.phaseGauge
  split
  · norm_num
  · exact kwRawDirectionRoot_ne_zero _

private theorem portAngle_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (p : KWDartPort G) :
    -Real.pi < (embedding.dartAngle (kwDartOfPort G p)).toReal ∧
      (embedding.dartAngle (kwDartOfPort G p)).toReal ≤ Real.pi :=
  ⟨Real.Angle.neg_pi_lt_toReal _, Real.Angle.toReal_le_pi _⟩

private theorem external_raw_angle_eq_at_snd
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm) :
    (data.rawDartDirection d : Real.Angle) =
      (embedding.dartAngle (kwDartOfPort G d.snd) +
        (Real.pi : Real.Angle)) := by
  simp only [KWAngularPortRadiusData.rawDartDirection, hd, if_pos]
  rw [embedding.dartAngle_symm]
  simp only [Real.Angle.coe_toReal]
  rw [add_assoc, ← Real.Angle.coe_add]
  simp

private theorem external_raw_angle_eq_at_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm) :
    (data.rawDartDirection d : Real.Angle) =
      embedding.dartAngle (kwDartOfPort G d.fst) := by
  simp [KWAngularPortRadiusData.rawDartDirection, hd]



theorem KWAngularPortRadiusData.realizedTurnPhase_eq_phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d e : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (hconnect : d.snd = e.fst) (hne : d.edge ≠ e.edge) :
    data.toStraightLineEmbedding.turnPhase d e =
      kwPhaseGauge data.phaseGauge (kwAngularSplitPhase embedding) d e := by
  rw [data.realizedTurnPhase_eq_raw]
  unfold kwPhaseGauge
  by_cases hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · by_cases he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm
    · exfalso
      apply hne
      have hsnd : e.snd = d.fst := by
        apply kwDartOfPort_injective G
        rw [he, ← hconnect, hd]
        simp
      have hedart : e = d.symm := by
        apply SimpleGraph.Dart.ext
        exact Prod.ext hconnect.symm hsnd
      rw [hedart]
      exact d.edge_symm.symm
    · have edata := (kwOrderedDartPortSplitGraph_adj G
          (kwAngularPortOrder embedding) e.fst e.snd).mp e.adj |>.resolve_left he
      let a := (embedding.dartAngle (kwDartOfPort G e.fst)).toReal
      let b := (embedding.dartAngle (kwDartOfPort G e.snd)).toReal
      have habBounds := portAngle_bounds embedding e.fst
      have hbbounds := portAngle_bounds embedding e.snd
      have hdRawPlus : (data.rawDartDirection d : Real.Angle) =
          ((a + Real.pi : ℝ) : Real.Angle) := by
        calc
          _ = embedding.dartAngle (kwDartOfPort G d.snd) +
              (Real.pi : Real.Angle) := external_raw_angle_eq_at_snd data d hd
          _ = embedding.dartAngle (kwDartOfPort G e.fst) +
              (Real.pi : Real.Angle) := by rw [hconnect]
          _ = ((a + Real.pi : ℝ) : Real.Angle) := by
            simp only [a, Real.Angle.coe_add, Real.Angle.coe_toReal]
      have hdRawMinus : (data.rawDartDirection d : Real.Angle) =
          ((a - Real.pi : ℝ) : Real.Angle) := by
        rw [hdRawPlus]
        change (a : Real.Angle) + (Real.pi : Real.Angle) =
          (a : Real.Angle) - (Real.pi : Real.Angle)
        rw [sub_eq_add_neg, Real.Angle.neg_coe_pi]
      by_cases hinc : kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) e.snd
      · have hab : a < b :=
          (kwAngularPortOrder_rank_lt_iff_angle_lt embedding edata.1).mp hinc
        have heRaw : data.rawDartDirection e =
            (a + b) / 2 + Real.pi / 2 := by
          simp [KWAngularPortRadiusData.rawDartDirection, he, hinc, a, b]
        rw [hdRawPlus, heRaw,
          kwAngleTurnPhase_coe_eq_rootRatio]
        · simp [KWAngularPortRadiusData.phaseGauge,
            KWAngularPortRadiusData.rawDartDirection,
            kwAngularSplitPhase, hd, he, hinc]
          rw [kwPortAngleRoot_eq_rawDirectionRoot,
            kwRawDirectionRoot_add_pi_inv]
          simp only [a, b]
          ring
        · nlinarith [habBounds.1, hbbounds.2, Real.pi_pos]
        · nlinarith [habBounds.1, hbbounds.2, Real.pi_pos]
      · have hdec : kwOrderedPortRank (kwAngularPortOrder embedding) e.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.fst := by
          rcases edata.2 with h | h <;> omega
        have hba : b < a :=
          (kwAngularPortOrder_rank_lt_iff_angle_lt embedding edata.1.symm).mp hdec
        have heRaw : data.rawDartDirection e =
            (a + b) / 2 - Real.pi / 2 := by
          simp [KWAngularPortRadiusData.rawDartDirection, he, hinc, a, b]
        rw [hdRawMinus, heRaw,
          kwAngleTurnPhase_coe_eq_rootRatio]
        · simp [KWAngularPortRadiusData.phaseGauge,
            KWAngularPortRadiusData.rawDartDirection,
            kwAngularSplitPhase, hd, he, hinc]
          rw [kwPortAngleRoot_eq_rawDirectionRoot,
            kwRawDirectionRoot_sub_pi_inv]
        · nlinarith [hbbounds.1, habBounds.2, Real.pi_pos]
        · nlinarith [hbbounds.1, habBounds.2, Real.pi_pos]
  · by_cases he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm
    · have ddata := (kwOrderedDartPortSplitGraph_adj G
          (kwAngularPortOrder embedding) d.fst d.snd).mp d.adj |>.resolve_left hd
      let a := (embedding.dartAngle (kwDartOfPort G d.fst)).toReal
      let b := (embedding.dartAngle (kwDartOfPort G d.snd)).toReal
      have habBounds := portAngle_bounds embedding d.fst
      have hbbounds := portAngle_bounds embedding d.snd
      have heRaw : (data.rawDartDirection e : Real.Angle) =
          (b : Real.Angle) := by
        calc
          _ = embedding.dartAngle (kwDartOfPort G e.fst) :=
            external_raw_angle_eq_at_fst data e he
          _ = embedding.dartAngle (kwDartOfPort G d.snd) := by rw [← hconnect]
          _ = (b : Real.Angle) := by simp only [b, Real.Angle.coe_toReal]
      by_cases hinc : kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.snd
      · have hab : a < b :=
          (kwAngularPortOrder_rank_lt_iff_angle_lt embedding ddata.1).mp hinc
        have hdRaw : data.rawDartDirection d =
            (a + b) / 2 + Real.pi / 2 := by
          simp [KWAngularPortRadiusData.rawDartDirection, hd, hinc, a, b]
        rw [hdRaw, heRaw, kwAngleTurnPhase_coe_eq_rootRatio]
        · simp [KWAngularPortRadiusData.phaseGauge,
            KWAngularPortRadiusData.rawDartDirection,
            kwAngularSplitPhase, hd, he, hinc]
          rw [kwPortAngleRoot_eq_rawDirectionRoot]
          simp only [← hconnect, b]
          simp only [a]
        · nlinarith [habBounds.1, hbbounds.2, Real.pi_pos]
        · nlinarith [habBounds.1, hbbounds.2, Real.pi_pos]
      · have hdec : kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by
          rcases ddata.2 with h | h <;> omega
        have hba : b < a :=
          (kwAngularPortOrder_rank_lt_iff_angle_lt embedding ddata.1.symm).mp hdec
        have hdRaw : data.rawDartDirection d =
            (a + b) / 2 - Real.pi / 2 := by
          simp [KWAngularPortRadiusData.rawDartDirection, hd, hinc, a, b]
        rw [hdRaw, heRaw, kwAngleTurnPhase_coe_eq_rootRatio]
        · simp [KWAngularPortRadiusData.phaseGauge,
            KWAngularPortRadiusData.rawDartDirection,
            kwAngularSplitPhase, hd, he, hinc]
          rw [kwPortAngleRoot_eq_rawDirectionRoot]
          simp only [← hconnect, b]
          simp only [a]
        · nlinarith [hbbounds.1, habBounds.2, Real.pi_pos]
        · nlinarith [hbbounds.1, habBounds.2, Real.pi_pos]
    · let di : KWOrderedInternalSplitDart G
          (kwAngularPortOrder embedding) := ⟨d, hd⟩
      let ei : KWOrderedInternalSplitDart G
          (kwAngularPortOrder embedding) := ⟨e, he⟩
      have hstep : KWOrderedInternalDartStep G
          (kwAngularPortOrder embedding) di ei := ⟨hconnect, hne⟩
      have ddata' := kwOrderedInternalSplitDart_adj_data G
        (kwAngularPortOrder embedding) di
      have edata' := kwOrderedInternalSplitDart_adj_data G
        (kwAngularPortOrder embedding) ei
      have ddata : d.fst.1 = d.snd.1 ∧
          (kwOrderedPortRank (kwAngularPortOrder embedding) d.fst + 1 =
              kwOrderedPortRank (kwAngularPortOrder embedding) d.snd ∨
            kwOrderedPortRank (kwAngularPortOrder embedding) d.snd + 1 =
              kwOrderedPortRank (kwAngularPortOrder embedding) d.fst) := by
        simpa only [di] using ddata'
      have edata : e.fst.1 = e.snd.1 ∧
          (kwOrderedPortRank (kwAngularPortOrder embedding) e.fst + 1 =
              kwOrderedPortRank (kwAngularPortOrder embedding) e.snd ∨
            kwOrderedPortRank (kwAngularPortOrder embedding) e.snd + 1 =
              kwOrderedPortRank (kwAngularPortOrder embedding) e.fst) := by
        simpa only [ei] using edata'
      let a := (embedding.dartAngle (kwDartOfPort G d.fst)).toReal
      let b := (embedding.dartAngle (kwDartOfPort G d.snd)).toReal
      let c := (embedding.dartAngle (kwDartOfPort G e.snd)).toReal
      have habBounds := portAngle_bounds embedding d.fst
      have hcbounds := portAngle_bounds embedding e.snd
      by_cases hinc : kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.snd
      · have heinc : kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.snd := by
          simpa only [di, ei] using
            kwOrderedInternalDartStep_rank_lt G
              (kwAngularPortOrder embedding) hstep hinc
        have hac : a < c := by
          have had : kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
              kwOrderedPortRank (kwAngularPortOrder embedding) e.snd := by
            calc
              _ < kwOrderedPortRank (kwAngularPortOrder embedding) d.snd := hinc
              _ = kwOrderedPortRank (kwAngularPortOrder embedding) e.fst :=
                congrArg (kwOrderedPortRank (kwAngularPortOrder embedding)) hconnect
              _ < _ := heinc
          exact (kwAngularPortOrder_rank_lt_iff_angle_lt embedding
            (ddata.1.trans (hconnect ▸ edata.1))).mp had
        have hdRaw : data.rawDartDirection d =
            (a + b) / 2 + Real.pi / 2 := by
          simp [KWAngularPortRadiusData.rawDartDirection, hd, hinc, a, b]
        have heRaw : data.rawDartDirection e =
            (b + c) / 2 + Real.pi / 2 := by
          simp only [KWAngularPortRadiusData.rawDartDirection, he, if_neg,
            heinc, if_pos]
          dsimp only [b, c]
          rw [← hconnect]
          simp
        rw [hdRaw, heRaw, kwAngleTurnPhase_coe_eq_rootRatio]
        · simp [KWAngularPortRadiusData.phaseGauge,
            KWAngularPortRadiusData.rawDartDirection,
            kwAngularSplitPhase, hd, he, hinc, heinc]
          rw [← hconnect]
        · nlinarith [habBounds.1, hcbounds.2, Real.pi_pos]
        · nlinarith [habBounds.1, hcbounds.2, Real.pi_pos]
      · have hddec : kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by
          rcases ddata.2 with h | h <;> omega
        have hedec : kwOrderedPortRank (kwAngularPortOrder embedding) e.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.fst := by
          simpa only [di, ei] using
            kwOrderedInternalDartStep_rank_gt G
              (kwAngularPortOrder embedding) hstep hddec
        have hca : c < a := by
          have had : kwOrderedPortRank (kwAngularPortOrder embedding) e.snd <
              kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by
            calc
              _ < kwOrderedPortRank (kwAngularPortOrder embedding) e.fst := hedec
              _ = kwOrderedPortRank (kwAngularPortOrder embedding) d.snd :=
                congrArg (kwOrderedPortRank (kwAngularPortOrder embedding)) hconnect.symm
              _ < _ := hddec
          exact (kwAngularPortOrder_rank_lt_iff_angle_lt embedding
            ((hconnect ▸ edata.1).symm.trans ddata.1.symm)).mp had
        have hdRaw : data.rawDartDirection d =
            (a + b) / 2 - Real.pi / 2 := by
          simp [KWAngularPortRadiusData.rawDartDirection, hd, hinc, a, b]
        have heRaw : data.rawDartDirection e =
            (b + c) / 2 - Real.pi / 2 := by
          have heinc : ¬ kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
              kwOrderedPortRank (kwAngularPortOrder embedding) e.snd := by omega
          simp only [KWAngularPortRadiusData.rawDartDirection, he, if_neg,
            heinc]
          dsimp only [b, c]
          rw [← hconnect]
          simp
        rw [hdRaw, heRaw, kwAngleTurnPhase_coe_eq_rootRatio]
        · have heinc : ¬ kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
              kwOrderedPortRank (kwAngularPortOrder embedding) e.snd := by omega
          simp [KWAngularPortRadiusData.phaseGauge,
            KWAngularPortRadiusData.rawDartDirection,
            kwAngularSplitPhase, hd, he, hinc, heinc]
          rw [← hconnect]
        · nlinarith [hcbounds.1, habBounds.2, Real.pi_pos]
        · nlinarith [hcbounds.1, habBounds.2, Real.pi_pos]

end StatMech.FrontierA
