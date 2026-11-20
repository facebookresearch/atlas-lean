/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAngularPortGeometry
import Code.FrontierA.KacWardHalfPlaneSegment
import Code.FrontierA.KacWardFinitePolygonEar









namespace StatMech.FrontierA

open SimpleGraph


noncomputable def kwAngularUnit (a : ℝ) : ℂ :=
  Complex.exp ((a : ℂ) * Complex.I)

@[simp] theorem kwAngularUnit_re (a : ℝ) :
    (kwAngularUnit a).re = Real.cos a := by
  simp [kwAngularUnit, Complex.exp_mul_I, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re]

@[simp] theorem kwAngularUnit_im (a : ℝ) :
    (kwAngularUnit a).im = Real.sin a := by
  simp [kwAngularUnit, Complex.exp_mul_I, Complex.sin_ofReal_re]


theorem KWStraightLineEmbedding.dartUnit_eq_angularUnit
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    embedding.dartUnit d =
      kwAngularUnit (embedding.dartAngle d).toReal := by
  let z := embedding.vertex d.snd - embedding.vertex d.fst
  have hz : z ≠ 0 := by
    simpa only [z] using embedding.dartVector_ne_zero d
  have hnorm : (‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hz
  apply mul_left_cancel₀ hnorm
  rw [← embedding.dartVector_eq_norm_mul_dartUnit d]
  unfold kwAngularUnit KWStraightLineEmbedding.dartAngle
  rw [Complex.arg_coe_angle_toReal_eq_arg]
  simpa only [z] using (Complex.norm_mul_exp_arg_mul_I z).symm


theorem kw_sin_add_sub_sin_add (x y : ℝ) :
    Real.sin x + Real.sin y - Real.sin (x + y) =
      4 * Real.sin (x / 2) * Real.sin (y / 2) *
        Real.sin ((x + y) / 2) := by
  have hsum :
      Real.sin x + Real.sin y =
        2 * Real.sin ((x + y) / 2) * Real.cos ((x - y) / 2) := by
    rw [show x = (x + y) / 2 + (x - y) / 2 by ring,
      show y = (x + y) / 2 - (x - y) / 2 by ring,
      Real.sin_add, Real.sin_sub]
    ring
  have hprod := Real.two_mul_sin_mul_sin (x / 2) (y / 2)
  rw [show x / 2 - y / 2 = (x - y) / 2 by ring,
    show x / 2 + y / 2 = (x + y) / 2 by ring] at hprod
  have hdouble := Real.sin_two_mul ((x + y) / 2)
  rw [show 2 * ((x + y) / 2) = x + y by ring] at hdouble
  rw [hsum, hdouble]
  calc
    _ = 2 * Real.sin ((x + y) / 2) *
        (Real.cos ((x - y) / 2) - Real.cos ((x + y) / 2)) := by ring
    _ = 2 * Real.sin ((x + y) / 2) *
        (2 * Real.sin (x / 2) * Real.sin (y / 2)) := by rw [hprod]
    _ = _ := by ring


theorem kwComplexCross_angularUnit_chord (a b c : ℝ) :
    kwComplexCross (kwAngularUnit b - kwAngularUnit a)
        (kwAngularUnit c - kwAngularUnit a) =
      4 * Real.sin ((b - a) / 2) * Real.sin ((c - b) / 2) *
        Real.sin ((c - a) / 2) := by
  calc
    _ = Real.sin (c - b) + Real.sin (b - a) - Real.sin (c - a) := by
      simp only [kwComplexCross, Complex.sub_re, Complex.sub_im,
        kwAngularUnit_re, kwAngularUnit_im]
      rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]
      ring
    _ = 4 * Real.sin ((b - a) / 2) * Real.sin ((c - b) / 2) *
        Real.sin (((b - a) + (c - b)) / 2) := by
      rw [add_comm (Real.sin (c - b)),
        show c - a = (b - a) + (c - b) by ring,
        kw_sin_add_sub_sin_add (b - a) (c - b)]
    _ = _ := by ring



theorem kwComplexCross_angularUnit_chord_pos
    {a b c : ℝ}
    (ha : -Real.pi < a) (hb : b ≤ Real.pi)
    (hcLower : -Real.pi < c) (hcUpper : c ≤ Real.pi)
    (hab : a < b) (hc : c < a ∨ b < c) :
    0 < kwComplexCross (kwAngularUnit b - kwAngularUnit a)
      (kwAngularUnit c - kwAngularUnit a) := by
  rw [kwComplexCross_angularUnit_chord]
  have hx0 : 0 < (b - a) / 2 := by linarith
  have hxpi : (b - a) / 2 < Real.pi := by linarith
  have hsx : 0 < Real.sin ((b - a) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  rcases hc with hc | hc
  · have hy0 : (c - b) / 2 < 0 := by linarith
    have hypi : -Real.pi < (c - b) / 2 := by linarith
    have hz0 : (c - a) / 2 < 0 := by linarith
    have hzpi : -Real.pi < (c - a) / 2 := by linarith
    have hsy : Real.sin ((c - b) / 2) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt hy0 hypi
    have hsz : Real.sin ((c - a) / 2) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt hz0 hzpi
    have hyz : 0 < Real.sin ((c - b) / 2) *
        Real.sin ((c - a) / 2) := mul_pos_of_neg_of_neg hsy hsz
    calc
      0 < (4 * Real.sin ((b - a) / 2)) *
          (Real.sin ((c - b) / 2) * Real.sin ((c - a) / 2)) := by
        exact mul_pos (mul_pos (by norm_num) hsx) hyz
      _ = 4 * Real.sin ((b - a) / 2) * Real.sin ((c - b) / 2) *
          Real.sin ((c - a) / 2) := by ring
  · have hy0 : 0 < (c - b) / 2 := by linarith
    have hypi : (c - b) / 2 < Real.pi := by linarith
    have hz0 : 0 < (c - a) / 2 := by linarith
    have hzpi : (c - a) / 2 < Real.pi := by linarith
    have hsy : 0 < Real.sin ((c - b) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi hy0 hypi
    have hsz : 0 < Real.sin ((c - a) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi hz0 hzpi
    positivity


theorem kwOrderedPortRank_eq_iff_of_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) {p q : KWDartPort G} (howner : p.1 = q.1) :
    kwOrderedPortRank order p = kwOrderedPortRank order q ↔ p = q := by
  constructor
  · intro hrank
    rcases p with ⟨v, i⟩
    rcases q with ⟨w, j⟩
    dsimp only at howner hrank ⊢
    subst w
    congr
    apply (order v).injective
    exact Fin.ext hrank
  · rintro rfl
    rfl


theorem KWStraightLineEmbedding.angularPort_supporting_cross_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {p q s : KWDartPort G}
    (hpqOwner : p.1 = q.1) (hpsOwner : p.1 = s.1)
    (hpq : kwOrderedPortRank (kwAngularPortOrder embedding) p + 1 =
      kwOrderedPortRank (kwAngularPortOrder embedding) q)
    (hsp : s ≠ p) (hsq : s ≠ q) :
    0 < kwComplexCross
      (embedding.dartUnit (kwDartOfPort G q) -
        embedding.dartUnit (kwDartOfPort G p))
      (embedding.dartUnit (kwDartOfPort G s) -
        embedding.dartUnit (kwDartOfPort G p)) := by
  let a := (embedding.dartAngle (kwDartOfPort G p)).toReal
  let b := (embedding.dartAngle (kwDartOfPort G q)).toReal
  let c := (embedding.dartAngle (kwDartOfPort G s)).toReal
  have hab : a < b := by
    apply (kwAngularPortOrder_rank_lt_iff_angle_lt embedding hpqOwner).1
    omega
  have hranksp : kwOrderedPortRank (kwAngularPortOrder embedding) s ≠
      kwOrderedPortRank (kwAngularPortOrder embedding) p := by
    intro h
    exact hsp ((kwOrderedPortRank_eq_iff_of_owner
      (kwAngularPortOrder embedding) hpsOwner.symm).mp h)
  have hranksq : kwOrderedPortRank (kwAngularPortOrder embedding) s ≠
      kwOrderedPortRank (kwAngularPortOrder embedding) q := by
    intro h
    exact hsq ((kwOrderedPortRank_eq_iff_of_owner
      (kwAngularPortOrder embedding)
      (hpsOwner.symm.trans hpqOwner)).mp h)
  have hc : c < a ∨ b < c := by
    have hsRank : kwOrderedPortRank (kwAngularPortOrder embedding) s <
          kwOrderedPortRank (kwAngularPortOrder embedding) p ∨
        kwOrderedPortRank (kwAngularPortOrder embedding) q <
          kwOrderedPortRank (kwAngularPortOrder embedding) s := by
      omega
    rcases hsRank with hsRank | hsRank
    · left
      exact (kwAngularPortOrder_rank_lt_iff_angle_lt embedding
        hpsOwner.symm).1 hsRank
    · right
      exact (kwAngularPortOrder_rank_lt_iff_angle_lt embedding
        (hpqOwner.symm.trans hpsOwner)).1 hsRank
  rw [embedding.dartUnit_eq_angularUnit,
    embedding.dartUnit_eq_angularUnit,
    embedding.dartUnit_eq_angularUnit]
  exact kwComplexCross_angularUnit_chord_pos
    (Real.Angle.neg_pi_lt_toReal _)
    (Real.Angle.toReal_le_pi _)
    (Real.Angle.neg_pi_lt_toReal _)
    (Real.Angle.toReal_le_pi _) hab hc

theorem kwComplexCross_ofReal_mul (r : ℝ) (x y : ℂ) :
    kwComplexCross ((r : ℂ) * x) ((r : ℂ) * y) =
      r ^ 2 * kwComplexCross x y := by
  unfold kwComplexCross
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring



theorem KWAngularPortRadiusData.portVertex_supporting_cross_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {p q s : KWDartPort G}
    (hpqOwner : p.1 = q.1) (hpsOwner : p.1 = s.1)
    (hpq : kwOrderedPortRank (kwAngularPortOrder embedding) p + 1 =
      kwOrderedPortRank (kwAngularPortOrder embedding) q)
    (hsp : s ≠ p) (hsq : s ≠ q) :
    0 < kwComplexCross
      (kwAngularPortVertex embedding (data.radius : ℝ) q -
        kwAngularPortVertex embedding (data.radius : ℝ) p)
      (kwAngularPortVertex embedding (data.radius : ℝ) s -
        kwAngularPortVertex embedding (data.radius : ℝ) p) := by
  have hunit := embedding.angularPort_supporting_cross_pos
    hpqOwner hpsOwner hpq hsp hsq
  have hqsub :
      kwAngularPortVertex embedding (data.radius : ℝ) q -
          kwAngularPortVertex embedding (data.radius : ℝ) p =
        ((data.radius : ℝ) : ℂ) *
          (embedding.dartUnit (kwDartOfPort G q) -
            embedding.dartUnit (kwDartOfPort G p)) := by
    unfold kwAngularPortVertex
    rw [← hpqOwner]
    push_cast
    ring
  have hssub :
      kwAngularPortVertex embedding (data.radius : ℝ) s -
          kwAngularPortVertex embedding (data.radius : ℝ) p =
        ((data.radius : ℝ) : ℂ) *
          (embedding.dartUnit (kwDartOfPort G s) -
            embedding.dartUnit (kwDartOfPort G p)) := by
    unfold kwAngularPortVertex
    rw [← hpsOwner]
    push_cast
    ring
  rw [hqsub, hssub, kwComplexCross_ofReal_mul]
  exact mul_pos (sq_pos_of_pos (by exact_mod_cast data.radius_pos)) hunit



theorem KWAngularPortRadiusData.internalChords_disjoint_of_same_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {p q p' q' : KWDartPort G}
    (hpqOwner : p.1 = q.1) (hppOwner : p.1 = p'.1)
    (hpq'Owner : p.1 = q'.1)
    (hpq : kwOrderedPortRank (kwAngularPortOrder embedding) p + 1 =
      kwOrderedPortRank (kwAngularPortOrder embedding) q)
    (hpq' : kwOrderedPortRank (kwAngularPortOrder embedding) p' + 1 =
      kwOrderedPortRank (kwAngularPortOrder embedding) q')
    (hedge : s(p, q) ≠ s(p', q')) :
    Disjoint
      {z : ℂ | Sbtw ℝ
        (kwAngularPortVertex embedding (data.radius : ℝ) p) z
        (kwAngularPortVertex embedding (data.radius : ℝ) q)}
      {z : ℂ | Sbtw ℝ
        (kwAngularPortVertex embedding (data.radius : ℝ) p') z
        (kwAngularPortVertex embedding (data.radius : ℝ) q')} := by
  let vp := kwAngularPortVertex embedding (data.radius : ℝ) p
  let vq := kwAngularPortVertex embedding (data.radius : ℝ) q
  let vp' := kwAngularPortVertex embedding (data.radius : ℝ) p'
  let vq' := kwAngularPortVertex embedding (data.radius : ℝ) q'
  have hpp : p ≠ p' ∨ q ≠ q' := by
    by_contra h
    push Not at h
    exact hedge (by rw [h.1, h.2])
  by_cases hp'p : p' = p
  · subst p'
    have hqq' : q = q' := by
      apply (kwOrderedPortRank_eq_iff_of_owner
        (kwAngularPortOrder embedding)
        (hpqOwner.symm.trans hpq'Owner)).mp
      omega
    subst q'
    exact (hedge rfl).elim
  by_cases hq'p : q' = p
  · subst q'
    have hp'q : p' ≠ q := by
      intro h
      subst p'
      omega
    have hcross := data.portVertex_supporting_cross_pos
      hpqOwner hppOwner hpq hp'p hp'q
    apply (kw_openSegments_disjoint_of_common_left_cross_ne
      (A := vp) (B := vq) (C := vp') hcross.ne').mono_right
    intro z hz
    exact (sbtw_comm.mp hz)
  by_cases hp'q : p' = q
  · subst p'
    have hq'p : q' ≠ p := by
      intro h
      subst q'
      omega
    have hcross := data.portVertex_supporting_cross_pos
      hpqOwner hpq'Owner hpq hq'p (by
        intro h
        subst q'
        omega)
    rw [disjoint_comm]
    apply (kw_openSegments_disjoint_of_common_left_cross_ne
      (A := vq) (B := vq') (C := vp) ?_).mono_right
    · intro z hz
      exact sbtw_comm.mp hz
    · have heq : kwComplexCross (vq' - vq) (vp - vq) =
          kwComplexCross (vq - vp) (vq' - vp) := by
        simp only [kwComplexCross, Complex.sub_re, Complex.sub_im]
        ring
      rw [heq]
      exact hcross.ne'
  by_cases hq'q : q' = q
  · subst q'
    have hpp' : p = p' := by
      apply (kwOrderedPortRank_eq_iff_of_owner
        (kwAngularPortOrder embedding) hppOwner).mp
      omega
    exact (hp'p hpp'.symm).elim
  have hpCross := data.portVertex_supporting_cross_pos
    hpqOwner hppOwner hpq hp'p hp'q
  have hqCross := data.portVertex_supporting_cross_pos
    hpqOwner hpq'Owner hpq hq'p hq'q
  exact kw_openSegments_disjoint_of_cross_same_sign
    (Or.inl ⟨hpCross, hqCross⟩)

end StatMech.FrontierA
