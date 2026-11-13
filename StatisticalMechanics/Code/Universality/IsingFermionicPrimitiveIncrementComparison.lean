/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicCenteredTVRegularity










open Filter Set Topology

namespace StatMech.Universality

noncomputable section





theorem norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le
    (f : Complex -> Complex) (hf : Continuous f)
    (a v : Complex) (B epsilon : Real)
    (hepsilon : 0 <= epsilon)
    (hbound : forall t : Real, t ∈ Icc 0 1 ->
      norm (f (a + (t : Complex) * v)) <= B)
    (hosc : forall t : Real, t ∈ Icc 0 1 ->
      norm (f (a + (t : Complex) * v) - f a) <= epsilon) :
    norm (complexDisplacementIntegral (fun z => f z ^ 2) a v -
        f a ^ 2 * v) <=
      (2 * B * epsilon) * norm v := by
  have hboundStart : norm (f a) <= B := by
    simpa using hbound 0 (by simp)
  apply norm_complexDisplacementIntegral_sub_const_mul_le
    (fun z => f z ^ 2) (hf.pow 2) a v (f a ^ 2) (2 * B * epsilon)
  intro t ht
  rw [show f (a + (t : Complex) * v) ^ 2 - f a ^ 2 =
      (f (a + (t : Complex) * v) - f a) *
        (f (a + (t : Complex) * v) + f a) by ring,
    norm_mul]
  calc
    norm (f (a + (t : Complex) * v) - f a) *
        norm (f (a + (t : Complex) * v) + f a) <=
      epsilon * (2 * B) := by
        apply mul_le_mul (hosc t ht)
        · calc
            norm (f (a + (t : Complex) * v) + f a) <=
                norm (f (a + (t : Complex) * v)) + norm (f a) :=
              norm_add_le _ _
            _ <= B + B := add_le_add (hbound t ht) hboundStart
            _ = 2 * B := by ring
        · exact norm_nonneg _
        · exact hepsilon
    _ = 2 * B * epsilon := by ring




theorem norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le_of_lipschitz
    (f : Complex -> Complex) (hf : Continuous f)
    (a v : Complex) (B L : NNReal)
    (hbound : forall t : Real, t ∈ Icc 0 1 ->
      norm (f (a + (t : Complex) * v)) <= B)
    (hlip : forall t : Real, t ∈ Icc 0 1 ->
      norm (f (a + (t : Complex) * v) - f a) <=
        (L : Real) * norm ((t : Complex) * v)) :
    norm (complexDisplacementIntegral (fun z => f z ^ 2) a v -
        f a ^ 2 * v) <=
      (2 * (B : Real) * (L : Real) * norm v) * norm v := by
  have hosc : forall t : Real, t ∈ Icc 0 1 ->
      norm (f (a + (t : Complex) * v) - f a) <=
        (L : Real) * norm v := by
    intro t ht
    refine (hlip t ht).trans ?_
    rw [norm_mul]
    have htNorm : norm (t : Complex) <= 1 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    simpa using mul_le_mul_of_nonneg_right htNorm (norm_nonneg v)
  have h := norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le
    f hf a v B ((L : Real) * norm v)
    (mul_nonneg L.coe_nonneg (norm_nonneg v)) hbound hosc
  convert h using 1
  ring






theorem
    norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le_of_closedBall_anchor
    (f : Complex -> Complex) (hf : Continuous f)
    (a v : Complex) (A R : Real) (L : NNReal)
    (hR : 0 <= R)
    (hanchor : norm (f 0) <= A)
    (hlip : LipschitzOnWith L f (Metric.closedBall (0 : Complex) R))
    (ha : a ∈ Metric.closedBall (0 : Complex) R)
    (hsegment : forall t : Real, t ∈ Icc 0 1 ->
      a + (t : Complex) * v ∈ Metric.closedBall (0 : Complex) R) :
    norm (complexDisplacementIntegral (fun z => f z ^ 2) a v -
        f a ^ 2 * v) <=
      (2 * (A + (L : Real) * R) * ((L : Real) * norm v)) * norm v := by
  have hzero : (0 : Complex) ∈ Metric.closedBall (0 : Complex) R := by
    simpa [Metric.mem_closedBall] using hR
  have hbound : forall t : Real, t ∈ Icc 0 1 ->
      norm (f (a + (t : Complex) * v)) <= A + (L : Real) * R := by
    intro t ht
    have hz := hsegment t ht
    have hdist : dist (a + (t : Complex) * v) 0 <= R := by
      simpa [Metric.mem_closedBall] using hz
    calc
      norm (f (a + (t : Complex) * v)) <=
          norm (f 0) + norm (f (a + (t : Complex) * v) - f 0) :=
        norm_le_norm_add_norm_sub' _ _
      _ <= A + (L : Real) * dist (a + (t : Complex) * v) 0 :=
        add_le_add hanchor (by
          simpa [dist_eq_norm] using
            hlip.dist_le_mul (a + (t : Complex) * v) hz 0 hzero)
      _ <= A + (L : Real) * R := by
        gcongr
  have hosc : forall t : Real, t ∈ Icc 0 1 ->
      norm (f (a + (t : Complex) * v) - f a) <=
        (L : Real) * norm v := by
    intro t ht
    have hz := hsegment t ht
    have hlocal := hlip.dist_le_mul (a + (t : Complex) * v) hz a ha
    rw [dist_eq_norm, dist_eq_norm] at hlocal
    refine hlocal.trans ?_
    rw [show a + (t : Complex) * v - a = (t : Complex) * v by ring,
      norm_mul]
    have htNorm : norm (t : Complex) <= 1 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    simpa using mul_le_mul_of_nonneg_right htNorm (norm_nonneg v)
  exact norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le
    f hf a v (A + (L : Real) * R) ((L : Real) * norm v)
    (mul_nonneg L.coe_nonneg (norm_nonneg v)) hbound hosc





theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_segmentSquareIntegral_sub_start_le
    (k : Nat) (R : Real) (hR : 0 <= R) (hk : 2 <= k)
    (hwide : 2 * R +
        ((((k / 2) * (k + 1) : Nat) : Real) + 6) *
          fkIsingExpandingSquareScale k <=
      fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k)
    (A : Real)
    (hanchor : norm
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k 0) <= A)
    (a v : Complex)
    (ha : a ∈ Metric.closedBall (0 : Complex) R)
    (hsegment : forall t : Real, t ∈ Icc 0 1 ->
      a + (t : Complex) * v ∈ Metric.closedBall (0 : Complex) R) :
    norm (complexDisplacementIntegral
        (fun z =>
          fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k z ^ 2)
        a v -
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k a ^ 2 * v) <=
      (2 * (A + 9728 * R) * (9728 * norm v)) * norm v := by
  have h :=
    norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le_of_closedBall_anchor
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k)
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_continuous k)
      a v A R (4 * (2432 : NNReal)) hR hanchor
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_fullCarrierTV
        k R hR hk hwide)
      ha hsegment
  norm_num at h
  exact h






theorem
    exists_centeredReflectedInterpolant_segmentSquareIntegral_error_of_root_tendsto
    (rootLimit : Complex)
    (hroot : Tendsto
      (fun k =>
        fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k 0)
      atTop (nhds rootLimit))
    (R : Real) (hR : 0 <= R)
    (a v : Nat -> Complex)
    (hv : Tendsto (fun k => norm (v k)) atTop (nhds 0))
    (hwide : ∀ᶠ k in atTop,
      2 * R + ((((k / 2) * (k + 1) : Nat) : Real) + 6) *
          fkIsingExpandingSquareScale k <=
        fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k)
    (ha : ∀ᶠ k in atTop,
      a k ∈ Metric.closedBall (0 : Complex) R)
    (hsegment : ∀ᶠ k in atTop,
      forall t : Real, t ∈ Icc 0 1 ->
        a k + (t : Complex) * v k ∈ Metric.closedBall (0 : Complex) R) :
    exists error : Nat -> Real,
      (forall k, 0 <= error k) /\
      Tendsto error atTop (nhds 0) /\
      (∀ᶠ k in atTop,
        norm (complexDisplacementIntegral
            (fun z =>
              fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k z ^ 2)
            (a k) (v k) -
          fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k (a k) ^ 2 *
            v k) <=
          error k * norm (v k)) := by
  let u : Nat -> Complex := fun k =>
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k 0
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto u (by
    simpa [u] using hroot)).subset_closedBall 0
  let A : Real := max B 0
  have hanchor : forall k, norm
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k 0) <= A := by
    intro k
    have hk := hB (show u k ∈ Set.range u from ⟨k, rfl⟩)
    rw [Metric.mem_closedBall] at hk
    have hk' : norm
        (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k 0) <= B := by
      simpa [u, dist_eq_norm] using hk
    exact hk'.trans (le_max_left _ _)
  let error : Nat -> Real := fun k =>
    (2 * (A + 9728 * R) * 9728) * norm (v k)
  have hconstant : 0 <= 2 * (A + 9728 * R) * 9728 := by
    have hA : 0 <= A := le_max_right _ _
    positivity
  refine ⟨error, ?_, ?_, ?_⟩
  · intro k
    exact mul_nonneg hconstant (norm_nonneg (v k))
  · simpa [error] using hv.const_mul (2 * (A + 9728 * R) * 9728)
  · filter_upwards [eventually_ge_atTop 2, hwide, ha, hsegment]
      with k hk hkWide hka hkSegment
    have hlocal :=
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_segmentSquareIntegral_sub_start_le
        k R hR hk hkWide A (hanchor k) (a k) (v k) hka hkSegment
    change _ <= (2 * (A + 9728 * R) * 9728 * norm (v k)) * norm (v k)
    convert hlocal using 1
    ring



theorem norm_complexDisplacementIntegral_sq_sub_realIncrement_le
    (f : Complex -> Complex) (hf : Continuous f)
    (a v : Complex) (B epsilon increment : Real)
    (hepsilon : 0 <= epsilon)
    (hbound : forall t : Real, t ∈ Icc 0 1 ->
      norm (f (a + (t : Complex) * v)) <= B)
    (hosc : forall t : Real, t ∈ Icc 0 1 ->
      norm (f (a + (t : Complex) * v) - f a) <= epsilon)
    (hexact : f a ^ 2 * v = (increment : Complex)) :
    norm (complexDisplacementIntegral (fun z => f z ^ 2) a v -
        (increment : Complex)) <=
      (2 * B * epsilon) * norm v := by
  rw [<- hexact]
  exact norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le
    f hf a v B epsilon hepsilon hbound hosc





theorem abs_complexDisplacementIntegral_sq_im_sub_realIncrement_le
    (f : Complex -> Complex) (hf : Continuous f)
    (a v : Complex) (B epsilon increment : Real)
    (hepsilon : 0 <= epsilon)
    (hbound : forall t : Real, t ∈ Icc 0 1 ->
      norm (f (a + (t : Complex) * v)) <= B)
    (hosc : forall t : Real, t ∈ Icc 0 1 ->
      norm (f (a + (t : Complex) * v) - f a) <= epsilon)
    (hexact : (f a ^ 2 * v).im = increment) :
    abs ((complexDisplacementIntegral (fun z => f z ^ 2) a v).im -
        increment) <=
      (2 * B * epsilon) * norm v := by
  have h := norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le
    f hf a v B epsilon hepsilon hbound hosc
  have him :
      (complexDisplacementIntegral (fun z => f z ^ 2) a v -
        f a ^ 2 * v).im =
        (complexDisplacementIntegral (fun z => f z ^ 2) a v).im -
          increment := by
    simp only [Complex.sub_im, hexact]
  rw [<- him]
  exact (Complex.abs_im_le_norm _).trans h



theorem normSq_isingProj_one_sub_negOne_eq_sq_re (z : Complex) :
    Complex.normSq (isingProj 1 z) -
        Complex.normSq (isingProj (-1) z) = (z ^ 2).re := by
  simp only [isingProj, map_one, map_neg, Complex.normSq_div,
    Complex.normSq_add, Complex.normSq_sub, Complex.normSq_conj,
    Complex.normSq_neg, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, pow_two]
  norm_num [Complex.normSq_apply]
  ring

theorem normSq_isingProj_negI_sub_I_eq_sq_im (z : Complex) :
    Complex.normSq (isingProj (-Complex.I) z) -
        Complex.normSq (isingProj Complex.I z) = (z ^ 2).im := by
  simp only [isingProj, map_mul, map_neg, Complex.conj_I,
    Complex.normSq_div, Complex.normSq_add, Complex.normSq_sub,
    Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_neg,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, pow_two]
  norm_num [Complex.normSq_apply]
  ring



theorem normSq_isingProj_one_sub_negI_eq_sq_mul_northwest_im (z : Complex) :
    Complex.normSq (isingProj 1 z) -
        Complex.normSq (isingProj (-Complex.I) z) =
      (z ^ 2 * ((-1 + Complex.I) / 2)).im := by
  simp only [isingProj, map_one, map_neg, map_mul, Complex.conj_I,
    Complex.normSq_div, Complex.normSq_add, Complex.normSq_sub,
    Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_neg,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, pow_two]
  norm_num [Complex.normSq_apply]
  ring


theorem normSq_isingProj_one_sub_I_eq_sq_mul_northeast_im (z : Complex) :
    Complex.normSq (isingProj 1 z) -
        Complex.normSq (isingProj Complex.I z) =
      (z ^ 2 * ((1 + Complex.I) / 2)).im := by
  simp only [isingProj, map_one, map_mul, Complex.conj_I,
    Complex.normSq_div, Complex.normSq_add, Complex.normSq_sub,
    Complex.normSq_mul, Complex.normSq_conj, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.div_re, Complex.div_im, Complex.conj_re,
    Complex.conj_im, Complex.one_re, Complex.one_im, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, pow_two]
  norm_num [Complex.normSq_apply]
  ring

theorem normSq_isingProj_negI_sub_negOne_eq_sq_mul_northeast_im
    (z : Complex) :
    Complex.normSq (isingProj (-Complex.I) z) -
        Complex.normSq (isingProj (-1) z) =
      (z ^ 2 * ((1 + Complex.I) / 2)).im := by
  simp only [isingProj, map_one, map_neg, map_mul, Complex.conj_I,
    Complex.normSq_div, Complex.normSq_add, Complex.normSq_sub,
    Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_neg,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, pow_two]
  norm_num [Complex.normSq_apply]
  ring

end

end StatMech.Universality
