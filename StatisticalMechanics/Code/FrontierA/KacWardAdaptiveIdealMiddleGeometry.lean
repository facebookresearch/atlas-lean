/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveConnectorClosedSeparation





namespace StatMech.FrontierA

open scoped Convex
open Set

def KWAdaptivePatchedData.idealMiddleClosedEdge
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) : Set ℂ :=
  if even then
    kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc)
  else
    kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc)

theorem KWAdaptivePatchedData.idealMiddleCorner_eq_lineMap
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.idealMiddleCorner i q =
      AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1))
        ((patch.data.parameter i q.succ.castSucc.castSucc +
          patch.data.parameter i q.succ.castSucc.succ) / 2) := by
  unfold KWAdaptivePatchedData.idealMiddleCorner KWStairParameterData.base
  rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply,
    AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  push_cast
  ring

private theorem mem_segment_lineMap_parameter
    {A B z : ℂ} {lo hi p q : ℝ}
    (hp : p ∈ Icc lo hi) (hq : q ∈ Icc lo hi)
    (hz : z ∈ segment ℝ (AffineMap.lineMap A B p)
      (AffineMap.lineMap A B q)) :
    ∃ u ∈ Icc lo hi, z = AffineMap.lineMap A B u := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  let u := (1 - t) * p + t * q
  refine ⟨u, ?_, ?_⟩
  · constructor <;> dsimp only [u] <;>
      nlinarith [hp.1, hp.2, hq.1, hq.2, ht.1, ht.2]
  · simp only [AffineMap.lineMap_apply_module, Complex.real_smul]
    dsimp only [u]
    push_cast
    ring



theorem KWAdaptivePatchedData.idealMiddleClosedEdge_point_parameter
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) {z : ℂ}
    (hz : z ∈ patch.idealMiddleClosedEdge i q even) :
    ∃ u ∈ Icc
        (patch.data.parameter i q.succ.castSucc.castSucc)
        (patch.data.parameter i q.succ.castSucc.succ),
      z = AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) u := by
  let lo := patch.data.parameter i q.succ.castSucc.castSucc
  let hi := patch.data.parameter i q.succ.castSucc.succ
  let mid := (lo + hi) / 2
  have hlohi : lo ≤ hi := (patch.data.parameter_strict i q.succ.castSucc).le
  have hmid : mid ∈ Icc lo hi := by
    dsimp only [mid]
    constructor <;> linarith
  have hbase : patch.data.base i q.succ.castSucc.castSucc =
      AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) lo := rfl
  have hnext : patch.data.base i q.succ.castSucc.succ =
      AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) hi := rfl
  have hcorner : patch.idealMiddleCorner i q =
      AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) mid := by
    simpa only [lo, hi, mid] using patch.idealMiddleCorner_eq_lineMap i q
  cases even with
  | true =>
      simp only [KWAdaptivePatchedData.idealMiddleClosedEdge,
        if_pos rfl, kwRawClosedEdge, kwStairEvenIndex_add_one,
        patch.idealVertex_even, patch.idealVertex_odd,
        patch.pathBase_castSucc, patch.idealPathCorner_castSucc,
        hbase, hcorner] at hz
      exact mem_segment_lineMap_parameter ⟨le_rfl, hlohi⟩ hmid hz
  | false =>
      simp only [KWAdaptivePatchedData.idealMiddleClosedEdge,
        Bool.false_eq_true, if_false, kwRawClosedEdge,
        kwStairOddIndex_castSucc_add_one, patch.idealVertex_even,
        patch.idealVertex_odd, patch.idealPathCorner_castSucc] at hz
      have hpath : patch.pathBase i q.succ =
          patch.data.base i q.succ.castSucc.succ := by
        by_cases hq : q = patch.lastMiddleIndex
        · subst q
          have hlast : patch.lastMiddleIndex.succ = Fin.last M := by
            apply Fin.ext
            simp [KWAdaptivePatchedData.lastMiddleIndex]
            have := patch.hM
            omega
          rw [hlast, patch.pathBase_last]
          unfold KWAdaptivePatchedData.incomingPort
          congr 2
        · have hsucc_ne : q.succ ≠ Fin.last M := by
            intro h
            apply hq
            apply Fin.ext
            have hval := congrArg Fin.val h
            simp only [Fin.val_succ, Fin.val_last] at hval
            simp [KWAdaptivePatchedData.lastMiddleIndex]
            omega
          obtain ⟨r, hr⟩ := Fin.eq_castSucc_of_ne_last hsucc_ne
          rw [← hr, patch.pathBase_castSucc]
          congr 2
      rw [hpath, hnext, hcorner] at hz
      exact mem_segment_lineMap_parameter hmid ⟨hlohi, le_rfl⟩ hz


theorem KWAdaptivePatchedData.idealMiddleClosedEdge_point_halfParameter
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) {z : ℂ}
    (hz : z ∈ patch.idealMiddleClosedEdge i q even) :
    ∃ u ∈ if even then
        Icc (patch.data.parameter i q.succ.castSucc.castSucc)
          ((patch.data.parameter i q.succ.castSucc.castSucc +
            patch.data.parameter i q.succ.castSucc.succ) / 2)
      else
        Icc ((patch.data.parameter i q.succ.castSucc.castSucc +
            patch.data.parameter i q.succ.castSucc.succ) / 2)
          (patch.data.parameter i q.succ.castSucc.succ),
      z = AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) u := by
  let lo := patch.data.parameter i q.succ.castSucc.castSucc
  let hi := patch.data.parameter i q.succ.castSucc.succ
  let mid := (lo + hi) / 2
  have hlohi : lo ≤ hi := (patch.data.parameter_strict i q.succ.castSucc).le
  have hmid : mid ∈ Icc lo hi := by
    dsimp only [mid]
    constructor <;> linarith
  have hbase : patch.data.base i q.succ.castSucc.castSucc =
      AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) lo := rfl
  have hnext : patch.data.base i q.succ.castSucc.succ =
      AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) hi := rfl
  have hcorner : patch.idealMiddleCorner i q =
      AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) mid := by
    simpa only [lo, hi, mid] using patch.idealMiddleCorner_eq_lineMap i q
  cases even with
  | true =>
      simp only [if_pos rfl]
      simp only [KWAdaptivePatchedData.idealMiddleClosedEdge,
        if_pos rfl, kwRawClosedEdge, kwStairEvenIndex_add_one,
        patch.idealVertex_even, patch.idealVertex_odd,
        patch.pathBase_castSucc, patch.idealPathCorner_castSucc,
        hbase, hcorner] at hz
      exact mem_segment_lineMap_parameter ⟨le_rfl, hmid.1⟩
        ⟨hmid.1, le_rfl⟩ hz
  | false =>
      simp only [Bool.false_eq_true, if_false]
      simp only [KWAdaptivePatchedData.idealMiddleClosedEdge,
        Bool.false_eq_true, if_false, kwRawClosedEdge,
        kwStairOddIndex_castSucc_add_one, patch.idealVertex_even,
        patch.idealVertex_odd, patch.idealPathCorner_castSucc] at hz
      have hpath : patch.pathBase i q.succ =
          patch.data.base i q.succ.castSucc.succ := by
        by_cases hq : q = patch.lastMiddleIndex
        · subst q
          have hlast : patch.lastMiddleIndex.succ = Fin.last M := by
            apply Fin.ext
            simp [KWAdaptivePatchedData.lastMiddleIndex]
            have := patch.hM
            omega
          rw [hlast, patch.pathBase_last]
          unfold KWAdaptivePatchedData.incomingPort
          congr 2
        · have hsucc_ne : q.succ ≠ Fin.last M := by
            intro h
            apply hq
            apply Fin.ext
            have hval := congrArg Fin.val h
            simp only [Fin.val_succ, Fin.val_last] at hval
            simp [KWAdaptivePatchedData.lastMiddleIndex]
            omega
          obtain ⟨r, hr⟩ := Fin.eq_castSucc_of_ne_last hsucc_ne
          rw [← hr, patch.pathBase_castSucc]
          congr 2
      rw [hpath, hnext, hcorner] at hz
      exact mem_segment_lineMap_parameter ⟨le_rfl, hmid.2⟩
        ⟨hmid.2, le_rfl⟩ hz

theorem KWAdaptivePatchedData.idealMiddleClosedEdge_subset_outgoingPortRay
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) :
    patch.idealMiddleClosedEdge i q even ⊆
      (fun w : ℂ ↦ polygon.vertex i + w) ''
        ({patch.beta * polygon.edgeVector i} ∪
          kwOpenRayTail (patch.beta * polygon.edgeVector i)) := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ :=
    patch.idealMiddleClosedEdge_point_parameter i q even hz
  have hfirstIndex : (0 : Fin (M + 2)).succ ≤
      q.succ.castSucc.castSucc := by
    apply Fin.mk_le_mk.mpr
    change 1 ≤ q.val + 1
    omega
  have hubeta : patch.beta ≤ u := by
    calc
      patch.beta = patch.data.parameter i (0 : Fin (M + 2)).succ :=
        (patch.parameter_one i).symm
      _ ≤ patch.data.parameter i q.succ.castSucc.castSucc :=
        (patch.data.parameter_strictMono i).monotone hfirstIndex
      _ ≤ u := hu.1
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  by_cases huBeta : u = patch.beta
  · refine ⟨patch.beta * polygon.edgeVector i, Or.inl rfl, ?_⟩
    rw [huBeta]
    unfold KWFiniteSimplePolygon.edgeVector
    ring
  · let t := u / patch.beta
    have huBetaLt : patch.beta < u :=
      lt_of_le_of_ne hubeta (Ne.symm huBeta)
    have ht : 1 < t := by
      apply (lt_div_iff₀ patch.hbeta).mpr
      simpa only [one_mul] using huBetaLt
    refine ⟨u * polygon.edgeVector i, Or.inr ⟨t, ht, ?_⟩, ?_⟩
    · dsimp only [t]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr patch.hbeta.ne']
    · unfold KWFiniteSimplePolygon.edgeVector
      ring

theorem KWAdaptivePatchedData.idealMiddleClosedEdge_subset_incomingPortRay
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) :
    patch.idealMiddleClosedEdge i q even ⊆
      (fun w : ℂ ↦ polygon.vertex (i + 1) + w) ''
        ({patch.alpha (i + 1) * (-polygon.edgeVector i)} ∪
          kwOpenRayTail (patch.alpha (i + 1) * (-polygon.edgeVector i))) := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ :=
    patch.idealMiddleClosedEdge_point_parameter i q even hz
  have hlastIndex : q.succ.castSucc.succ ≤
      (Fin.last (M + 1)).castSucc := by
    apply Fin.mk_le_mk.mpr
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
    have hq := q.isLt
    omega
  have hualpha : patch.alpha (i + 1) ≤ 1 - u := by
    calc
      patch.alpha (i + 1) = 1 -
          patch.data.parameter i (Fin.last (M + 1)).castSucc := by
        rw [patch.parameter_penultimate i]
        ring
      _ ≤ 1 - patch.data.parameter i q.succ.castSucc.succ := by
        exact sub_le_sub_left
          ((patch.data.parameter_strictMono i).monotone hlastIndex) 1
      _ ≤ 1 - u := sub_le_sub_left hu.2 1
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  have hvertex : polygon.vertex i + u * polygon.edgeVector i =
      polygon.vertex (i + 1) + (1 - u) * (-polygon.edgeVector i) := by
    unfold KWFiniteSimplePolygon.edgeVector
    push_cast
    ring
  rw [show u * (polygon.vertex (i + 1) - polygon.vertex i) +
      polygon.vertex i = polygon.vertex i + u * polygon.edgeVector i by
    unfold KWFiniteSimplePolygon.edgeVector
    ring, hvertex]
  by_cases huAlpha : (1 - u) = patch.alpha (i + 1)
  · refine ⟨patch.alpha (i + 1) * (-polygon.edgeVector i), Or.inl rfl, ?_⟩
    have hc := congrArg (fun x : ℝ ↦ (x : ℂ)) huAlpha
    push_cast at hc
    rw [hc]
  · let t := (1 - u) / patch.alpha (i + 1)
    have huAlphaLt : patch.alpha (i + 1) < 1 - u :=
      lt_of_le_of_ne hualpha (Ne.symm huAlpha)
    have ht : 1 < t := by
      apply (lt_div_iff₀ (patch.halpha (i + 1))).mpr
      simpa only [one_mul] using huAlphaLt
    refine ⟨(1 - u) * (-polygon.edgeVector i),
      Or.inr ⟨t, ht, ?_⟩, rfl⟩
    dsimp only [t]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (patch.halpha (i + 1)).ne']



theorem KWAdaptivePatchedData.idealMiddleClosedEdge_subset_outgoingRay
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool)
    (hnotFirst : q ≠ 0 ∨ even = false) :
    patch.idealMiddleClosedEdge i q even ⊆
      (fun w : ℂ ↦ polygon.vertex i + w) ''
        kwOpenRayTail (patch.beta * polygon.edgeVector i) := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ :=
    patch.idealMiddleClosedEdge_point_halfParameter i q even hz
  have hbetaLo : patch.beta ≤
      patch.data.parameter i q.succ.castSucc.castSucc := by
    calc
      patch.beta = patch.data.parameter i (0 : Fin (M + 2)).succ :=
        (patch.parameter_one i).symm
      _ ≤ patch.data.parameter i q.succ.castSucc.castSucc := by
        apply (patch.data.parameter_strictMono i).monotone
        apply Fin.mk_le_mk.mpr
        simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Nat.zero_mod]
        omega
  have hbetaU : patch.beta < u := by
    cases even with
    | false =>
        simp only [Bool.false_eq_true, if_false] at hu
        have hdelta := patch.data.parameter_strict i q.succ.castSucc
        linarith [hu.1]
    | true =>
        simp only [if_pos rfl] at hu
        have hq0 : q ≠ 0 := by simpa using hnotFirst
        have hindex : (0 : Fin (M + 2)).succ <
            q.succ.castSucc.castSucc := by
          apply Fin.mk_lt_mk.mpr
          have hqval : q.val ≠ 0 := fun h ↦ hq0 (Fin.ext h)
          simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Nat.zero_mod]
          omega
        have hlo := patch.data.parameter_strictMono i hindex
        rw [patch.parameter_one i] at hlo
        exact hlo.trans_le hu.1
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  let t := u / patch.beta
  have ht : 1 < t := by
    apply (lt_div_iff₀ patch.hbeta).mpr
    simpa only [one_mul] using hbetaU
  refine ⟨u * polygon.edgeVector i, ⟨t, ht, ?_⟩, ?_⟩
  · dsimp only [t]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr patch.hbeta.ne']
  · unfold KWFiniteSimplePolygon.edgeVector
    ring



theorem KWAdaptivePatchedData.idealMiddleClosedEdge_subset_incomingRay
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool)
    (hnotLast : q ≠ patch.lastMiddleIndex ∨ even = true) :
    patch.idealMiddleClosedEdge i q even ⊆
      (fun w : ℂ ↦ polygon.vertex (i + 1) + w) ''
        kwOpenRayTail (patch.alpha (i + 1) * (-polygon.edgeVector i)) := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ :=
    patch.idealMiddleClosedEdge_point_halfParameter i q even hz
  have hHiAlpha : patch.data.parameter i q.succ.castSucc.succ ≤
      1 - patch.alpha (i + 1) := by
    calc
      patch.data.parameter i q.succ.castSucc.succ ≤
          patch.data.parameter i (Fin.last (M + 1)).castSucc := by
        apply (patch.data.parameter_strictMono i).monotone
        apply Fin.mk_le_mk.mpr
        simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
        have hq := q.isLt
        omega
      _ = 1 - patch.alpha (i + 1) := patch.parameter_penultimate i
  have hAlphaU : patch.alpha (i + 1) < 1 - u := by
    cases even with
    | true =>
        simp only [if_pos rfl] at hu
        have hdelta := patch.data.parameter_strict i q.succ.castSucc
        linarith [hu.2, hHiAlpha]
    | false =>
        simp only [Bool.false_eq_true, if_false] at hu
        have hqLast : q ≠ patch.lastMiddleIndex := by simpa using hnotLast
        have hindex : q.succ.castSucc.succ <
            (Fin.last (M + 1)).castSucc := by
          apply Fin.mk_lt_mk.mpr
          have hqval : q.val ≠ M - 1 := by
            intro h
            apply hqLast
            apply Fin.ext
            simpa [KWAdaptivePatchedData.lastMiddleIndex] using h
          simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
          have hq := q.isLt
          omega
        have hhi := patch.data.parameter_strictMono i hindex
        rw [patch.parameter_penultimate i] at hhi
        linarith [hu.2]
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  rw [show u * (polygon.vertex (i + 1) - polygon.vertex i) +
      polygon.vertex i = polygon.vertex (i + 1) +
        (1 - u) * (-polygon.edgeVector i) by
    unfold KWFiniteSimplePolygon.edgeVector
    push_cast
    ring]
  let t := (1 - u) / patch.alpha (i + 1)
  have ht : 1 < t := by
    apply (lt_div_iff₀ (patch.halpha (i + 1))).mpr
    simpa only [one_mul] using hAlphaU
  refine ⟨(1 - u) * (-polygon.edgeVector i), ⟨t, ht, ?_⟩, rfl⟩
  dsimp only [t]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (patch.halpha (i + 1)).ne']

end StatMech.FrontierA
