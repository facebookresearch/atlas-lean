/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAngularPortCircle










namespace StatMech.FrontierA

open Set SimpleGraph


noncomputable def KWAngularPortRadiusData.trimParameter
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding) (d : G.Dart) : ℝ :=
  (data.radius : ℝ) /
    ‖embedding.vertex d.snd - embedding.vertex d.fst‖

theorem KWAngularPortRadiusData.trimParameter_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding) (d : G.Dart) :
    0 < data.trimParameter d := by
  unfold KWAngularPortRadiusData.trimParameter
  exact div_pos (by exact_mod_cast data.radius_pos)
    (norm_pos_iff.mpr (embedding.dartVector_ne_zero d))

theorem KWAngularPortRadiusData.trimParameter_lt_quarter
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding) (d : G.Dart) :
    data.trimParameter d < 1 / 4 := by
  unfold KWAngularPortRadiusData.trimParameter
  have hlen : 0 < ‖embedding.vertex d.snd - embedding.vertex d.fst‖ :=
    norm_pos_iff.mpr (embedding.dartVector_ne_zero d)
  apply (div_lt_iff₀ hlen).2
  have := data.edge_long d
  linarith

theorem KWAngularPortRadiusData.trimParameter_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding) (d : G.Dart) :
    data.trimParameter d.symm = data.trimParameter d := by
  unfold KWAngularPortRadiusData.trimParameter
  have hvec : embedding.vertex d.fst - embedding.vertex d.snd =
      -(embedding.vertex d.snd - embedding.vertex d.fst) := by ring
  change (data.radius : ℝ) /
      ‖embedding.vertex d.fst - embedding.vertex d.snd‖ =
    (data.radius : ℝ) /
      ‖embedding.vertex d.snd - embedding.vertex d.fst‖
  rw [hvec, norm_neg]


theorem KWAngularPortRadiusData.portVertex_eq_lineMap
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding) (p : KWDartPort G) :
    kwAngularPortVertex embedding (data.radius : ℝ) p =
      AffineMap.lineMap
        (embedding.vertex (kwDartOfPort G p).fst)
        (embedding.vertex (kwDartOfPort G p).snd)
        (data.trimParameter (kwDartOfPort G p)) := by
  let d := kwDartOfPort G p
  have hlen : (‖embedding.vertex d.snd - embedding.vertex d.fst‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (embedding.dartVector_ne_zero d)
  unfold kwAngularPortVertex KWStraightLineEmbedding.dartUnit
    KWAngularPortRadiusData.trimParameter
  rw [kwDartOfPort_fst]
  rw [AffineMap.lineMap_apply_module]
  simp only [Complex.real_smul]
  push_cast
  field_simp
  ring

theorem kw_lineMap_reverse (a b : ℂ) (t : ℝ) :
    AffineMap.lineMap b a t = AffineMap.lineMap a b (1 - t) := by
  rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
  simp only [Complex.real_smul]
  push_cast
  ring


theorem KWAngularPortRadiusData.matchingPortVertex_eq_lineMap
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {p q : KWDartPort G}
    (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm) :
    kwAngularPortVertex embedding (data.radius : ℝ) q =
      AffineMap.lineMap
        (embedding.vertex (kwDartOfPort G p).fst)
        (embedding.vertex (kwDartOfPort G p).snd)
        (1 - data.trimParameter (kwDartOfPort G p)) := by
  rw [data.portVertex_eq_lineMap q, hmatching,
    data.trimParameter_symm]
  change AffineMap.lineMap
      (embedding.vertex (kwDartOfPort G p).snd)
      (embedding.vertex (kwDartOfPort G p).fst)
      (data.trimParameter (kwDartOfPort G p)) = _
  exact kw_lineMap_reverse _ _ _

theorem kw_lineMap_lineMap (a b : ℂ) (t u : ℝ) :
    AffineMap.lineMap (AffineMap.lineMap a b t)
        (AffineMap.lineMap a b (1 - t)) u =
      AffineMap.lineMap a b (t + u * (1 - 2 * t)) := by
  simp only [AffineMap.lineMap_apply_module, Complex.real_smul]
  push_cast
  ring



theorem KWAngularPortRadiusData.matching_sbtw_original
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {p q : KWDartPort G}
    (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm)
    {z : ℂ}
    (hz : Sbtw ℝ
      (kwAngularPortVertex embedding (data.radius : ℝ) p) z
      (kwAngularPortVertex embedding (data.radius : ℝ) q)) :
    Sbtw ℝ
      (embedding.vertex (kwDartOfPort G p).fst) z
      (embedding.vertex (kwDartOfPort G p).snd) := by
  let d := kwDartOfPort G p
  let t := data.trimParameter d
  obtain ⟨u, hu, rfl⟩ := hz.mem_image_Ioo
  rw [data.portVertex_eq_lineMap p,
    data.matchingPortVertex_eq_lineMap hmatching,
    kw_lineMap_lineMap]
  apply sbtw_lineMap_iff.mpr
  refine ⟨embedding.vertex_injective.ne d.fst_ne_snd, ?_, ?_⟩
  · have ht0 := data.trimParameter_pos d
    have htq := data.trimParameter_lt_quarter d
    nlinarith [hu.1, hu.2]
  · have ht0 := data.trimParameter_pos d
    have htq := data.trimParameter_lt_quarter d
    nlinarith [hu.1, hu.2]



theorem KWAngularPortRadiusData.radius_lt_dist_fst_of_matching_sbtw
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {p q : KWDartPort G}
    (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm)
    {z : ℂ}
    (hz : Sbtw ℝ
      (kwAngularPortVertex embedding (data.radius : ℝ) p) z
      (kwAngularPortVertex embedding (data.radius : ℝ) q)) :
    (data.radius : ℝ) <
      dist (embedding.vertex (kwDartOfPort G p).fst) z := by
  let d := kwDartOfPort G p
  let t := data.trimParameter d
  obtain ⟨u, hu, hzu⟩ := hz.mem_image_Ioo
  rw [data.portVertex_eq_lineMap p,
    data.matchingPortVertex_eq_lineMap hmatching,
    kw_lineMap_lineMap] at hzu
  rw [← hzu, dist_eq_norm]
  have hv : 0 < t + u * (1 - 2 * t) := by
    have ht0 := data.trimParameter_pos d
    have htq := data.trimParameter_lt_quarter d
    nlinarith [hu.1, hu.2]
  have hvt : t < t + u * (1 - 2 * t) := by
    have htq := data.trimParameter_lt_quarter d
    nlinarith [hu.1]
  have hnorm : ‖((t + u * (1 - 2 * t) : ℝ) : ℂ) *
        (embedding.vertex d.snd - embedding.vertex d.fst)‖ =
      (t + u * (1 - 2 * t)) *
        ‖embedding.vertex d.snd - embedding.vertex d.fst‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
  have hline : embedding.vertex d.fst -
      AffineMap.lineMap (embedding.vertex d.fst) (embedding.vertex d.snd)
          (t + u * (1 - 2 * t)) =
        -(((t + u * (1 - 2 * t) : ℝ) : ℂ) *
          (embedding.vertex d.snd - embedding.vertex d.fst)) := by
    rw [AffineMap.lineMap_apply_module]
    simp only [Complex.real_smul]
    push_cast
    ring
  change (data.radius : ℝ) <
    ‖embedding.vertex d.fst -
      AffineMap.lineMap (embedding.vertex d.fst) (embedding.vertex d.snd)
        (t + u * (1 - 2 * t))‖
  rw [hline, norm_neg, hnorm]
  unfold KWAngularPortRadiusData.trimParameter at hvt
  have hlen : 0 < ‖embedding.vertex d.snd - embedding.vertex d.fst‖ :=
    norm_pos_iff.mpr (embedding.dartVector_ne_zero d)
  exact (div_lt_iff₀ hlen).mp hvt


theorem KWAngularPortRadiusData.radius_lt_dist_snd_of_matching_sbtw
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {p q : KWDartPort G}
    (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm)
    {z : ℂ}
    (hz : Sbtw ℝ
      (kwAngularPortVertex embedding (data.radius : ℝ) p) z
      (kwAngularPortVertex embedding (data.radius : ℝ) q)) :
    (data.radius : ℝ) <
      dist (embedding.vertex (kwDartOfPort G p).snd) z := by
  have hreverse : kwDartOfPort G p = (kwDartOfPort G q).symm := by
    rw [hmatching]
    simp
  have h := data.radius_lt_dist_fst_of_matching_sbtw hreverse
    ((sbtw_comm).mpr hz)
  simpa only [hmatching] using h

end StatMech.FrontierA
