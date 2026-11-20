/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge
import Code.Universality.IsingFermionicReflectedTensorTent
import Code.Universality.IsingFermionicPhysicalCenteredRadialPatch












namespace StatMech.Universality

open Filter Set Topology
open scoped BigOperators

noncomputable section



theorem complex_wedgeIntegral_tendsto_of_locallyUniform
    {F : Nat -> Complex -> Complex} {f : Complex -> Complex}
    (hF : forall n, Continuous (F n))
    (hlimit : TendstoLocallyUniformlyOn F f atTop Set.univ)
    (z w : Complex) :
    Tendsto (fun n => Complex.wedgeIntegral z w (F n)) atTop
      (nhds (Complex.wedgeIntegral z w f)) := by
  have hhorizontal : TendstoUniformlyOn
      (fun n (x : Real) => F n (x + z.im * Complex.I))
      (fun x : Real => f (x + z.im * Complex.I)) atTop
      (Set.uIcc z.re w.re) := by
    have hcomp : TendstoLocallyUniformlyOn
        (fun n (x : Real) => F n (x + z.im * Complex.I))
        (fun x : Real => f (x + z.im * Complex.I)) atTop
        (Set.uIcc z.re w.re) :=
      hlimit.comp (t := Set.uIcc z.re w.re)
        (fun x : Real => x + z.im * Complex.I)
        (fun _ _ => Set.mem_univ _) (by fun_prop)
    exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      isCompact_uIcc).mp hcomp
  have hvertical : TendstoUniformlyOn
      (fun n (y : Real) => F n (w.re + y * Complex.I))
      (fun y : Real => f (w.re + y * Complex.I)) atTop
      (Set.uIcc z.im w.im) := by
    have hcomp : TendstoLocallyUniformlyOn
        (fun n (y : Real) => F n (w.re + y * Complex.I))
        (fun y : Real => f (w.re + y * Complex.I)) atTop
        (Set.uIcc z.im w.im) :=
      hlimit.comp (t := Set.uIcc z.im w.im)
        (fun y : Real => w.re + y * Complex.I)
        (fun _ _ => Set.mem_univ _) (by fun_prop)
    exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      isCompact_uIcc).mp hcomp
  have hhorizontalContinuous : forall n,
      ContinuousOn (fun x : Real => F n (x + z.im * Complex.I))
        (Set.uIcc z.re w.re) := fun n => by
    exact ((hF n).comp (by fun_prop)).continuousOn
  have hverticalContinuous : forall n,
      ContinuousOn (fun y : Real => F n (w.re + y * Complex.I))
        (Set.uIcc z.im w.im) := fun n => by
    exact ((hF n).comp (by fun_prop)).continuousOn
  have hhorizontalIntegral :=
    TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (μ := MeasureTheory.volume)
      (Filter.Eventually.of_forall hhorizontalContinuous) hhorizontal
  have hverticalIntegral :=
    TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (μ := MeasureTheory.volume)
      (Filter.Eventually.of_forall hverticalContinuous) hvertical
  simpa [Complex.wedgeIntegral] using hhorizontalIntegral.add
    (hverticalIntegral.const_smul Complex.I)



theorem continuous_wedgeContour (f : Complex -> Complex) (hf : Continuous f) :
    Continuous (fun p : Complex × Complex =>
      Complex.wedgeIntegral p.1 p.2 f +
        Complex.wedgeIntegral p.2 p.1 f) := by
  let H : Real × Real -> Complex := fun p =>
    ∫ x : Real in 0..p.2, f (x + p.1 * Complex.I)
  let V : Real × Real -> Complex := fun p =>
    ∫ y : Real in 0..p.2, f (p.1 + y * Complex.I)
  have hH : Continuous H := by
    dsimp only [H]
    exact intervalIntegral.continuous_parametric_primitive_of_continuous
      (f := fun y x : Real => f (x + y * Complex.I)) (by fun_prop)
  have hV : Continuous V := by
    dsimp only [V]
    exact intervalIntegral.continuous_parametric_primitive_of_continuous
      (f := fun x y : Real => f (x + y * Complex.I)) (by fun_prop)
  have hHorizontal (y a b : Real) :
      (∫ x : Real in a..b, f (x + y * Complex.I)) =
        H (y, b) - H (y, a) := by
    have h0a : IntervalIntegrable (fun x : Real =>
        f (x + y * Complex.I)) MeasureTheory.volume 0 a :=
      (hf.comp (by fun_prop)).intervalIntegrable _ _
    have hab : IntervalIntegrable (fun x : Real =>
        f (x + y * Complex.I)) MeasureTheory.volume a b :=
      (hf.comp (by fun_prop)).intervalIntegrable _ _
    have hadd := intervalIntegral.integral_add_adjacent_intervals h0a hab
    dsimp only [H]
    linear_combination hadd
  have hVertical (x a b : Real) :
      (∫ y : Real in a..b, f (x + y * Complex.I)) =
        V (x, b) - V (x, a) := by
    have h0a : IntervalIntegrable (fun y : Real =>
        f (x + y * Complex.I)) MeasureTheory.volume 0 a :=
      (hf.comp (by fun_prop)).intervalIntegrable _ _
    have hab : IntervalIntegrable (fun y : Real =>
        f (x + y * Complex.I)) MeasureTheory.volume a b :=
      (hf.comp (by fun_prop)).intervalIntegrable _ _
    have hadd := intervalIntegral.integral_add_adjacent_intervals h0a hab
    dsimp only [V]
    linear_combination hadd
  simp_rw [Complex.wedgeIntegral, hHorizontal, hVertical]
  fun_prop




structure VanishingRectangleContourError
    (F : Nat -> Complex -> Complex) where
  error : Complex -> Complex -> Nat -> Real
  error_tendsto_zero : forall z w,
    Tendsto (error z w) atTop (nhds 0)
  contour_norm_le : forall z w n,
    norm (Complex.wedgeIntegral z w (F n) +
      Complex.wedgeIntegral w z (F n)) <= error z w n

theorem VanishingRectangleContourError.contour_tendsto_zero
    {F : Nat -> Complex -> Complex}
    (H : VanishingRectangleContourError F) (z w : Complex) :
    Tendsto (fun n => Complex.wedgeIntegral z w (F n) +
      Complex.wedgeIntegral w z (F n)) atTop (nhds 0) := by
  apply squeeze_zero_norm (fun n => H.contour_norm_le z w n)
  exact H.error_tendsto_zero z w


theorem VanishingRectangleContourError.contour_tendsto_zero_comp
    {F : Nat -> Complex -> Complex}
    (H : VanishingRectangleContourError F) {sigma : Nat -> Nat}
    (hsigma : Tendsto sigma atTop atTop) (z w : Complex) :
    Tendsto (fun n => Complex.wedgeIntegral z w (F (sigma n)) +
      Complex.wedgeIntegral w z (F (sigma n))) atTop (nhds 0) :=
  (H.contour_tendsto_zero z w).comp hsigma




theorem norm_wedgeContour_le_of_uniformNorm
    (F : Complex -> Complex) (epsilon : Real)
    (hF : forall z, norm (F z) <= epsilon) (z w : Complex) :
    norm (Complex.wedgeIntegral z w F + Complex.wedgeIntegral w z F) <=
      2 * epsilon * (|w.re - z.re| + |w.im - z.im|) := by
  let A : Complex := ∫ x : Real in z.re..w.re, F (x + z.im * Complex.I)
  let B : Complex := ∫ x : Real in z.re..w.re, F (x + w.im * Complex.I)
  let C : Complex := ∫ y : Real in z.im..w.im, F (w.re + y * Complex.I)
  let D : Complex := ∫ y : Real in z.im..w.im, F (z.re + y * Complex.I)
  have hA : norm A <= epsilon * |w.re - z.re| := by
    dsimp only [A]
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x _hx => hF (x + z.im * Complex.I))
  have hB : norm B <= epsilon * |w.re - z.re| := by
    dsimp only [B]
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x _hx => hF (x + w.im * Complex.I))
  have hC : norm C <= epsilon * |w.im - z.im| := by
    dsimp only [C]
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun y _hy => hF (w.re + y * Complex.I))
  have hD : norm D <= epsilon * |w.im - z.im| := by
    dsimp only [D]
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun y _hy => hF (z.re + y * Complex.I))
  rw [Complex.wedgeIntegral_add_wedgeIntegral_eq]
  change norm (A - B + Complex.I * C - Complex.I * D) <= _
  calc
    norm (A - B + Complex.I * C - Complex.I * D) <=
        norm (A - B + Complex.I * C) + norm (Complex.I * D) :=
      norm_sub_le _ _
    _ <= (norm (A - B) + norm (Complex.I * C)) + norm (Complex.I * D) :=
      by gcongr; exact norm_add_le _ _
    _ <= ((norm A + norm B) + norm (Complex.I * C)) + norm (Complex.I * D) :=
      by gcongr; exact norm_sub_le _ _
    _ <= 2 * epsilon * (|w.re - z.re| + |w.im - z.im|) := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
      nlinarith



noncomputable def complexDisplacementIntegral
    (f : Complex -> Complex) (a v : Complex) : Complex :=
  ∫ t : Real in 0..1, f (a + (t : Complex) * v) * v


theorem complexDisplacementIntegral_reverse
    (f : Complex -> Complex) (a v : Complex) :
    complexDisplacementIntegral f (a + v) (-v) =
      -complexDisplacementIntegral f a v := by
  unfold complexDisplacementIntegral
  have hpoint (t : Real) :
      f (a + v + (t : Complex) * -v) * -v =
        -(f (a + ((1 - t : Real) : Complex) * v) * v) := by
    have harg : a + v + (t : Complex) * -v =
        a + ((1 - t : Real) : Complex) * v := by
      push_cast
      ring
    rw [harg]
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_sub_left
      (fun t : Real => f (a + (t : Complex) * v) * v) 1]
  norm_num


theorem complexDisplacementIntegral_ofReal
    (f : Complex -> Complex) (x y d : Real) :
    complexDisplacementIntegral f (x + y * Complex.I) d =
      ∫ s : Real in x..x + d, f (s + y * Complex.I) := by
  unfold complexDisplacementIntegral
  have hpoint (t : Real) :
      f ((x : Complex) + y * Complex.I + (t : Complex) * (d : Complex)) *
          (d : Complex) =
        (d : Complex) * f ((x + d * t : Real) + y * Complex.I) := by
    have harg : (x : Complex) + y * Complex.I +
        (t : Complex) * (d : Complex) =
      ((x + d * t : Real) : Complex) + y * Complex.I := by
      push_cast
      ring
    rw [harg]
    ring
  simp_rw [hpoint, ← smul_eq_mul]
  simpa [add_comm] using
    (intervalIntegral.smul_integral_comp_add_mul
      (f := fun s : Real => f (s + y * Complex.I))
      (a := (0 : Real)) (b := 1) d x)



theorem complexDisplacementIntegral_mul_I
    (f : Complex -> Complex) (x y d : Real) :
    complexDisplacementIntegral f (x + y * Complex.I)
        ((d : Complex) * Complex.I) =
      Complex.I * ∫ s : Real in y..y + d, f (x + s * Complex.I) := by
  unfold complexDisplacementIntegral
  have hpoint (t : Real) :
      f ((x : Complex) + y * Complex.I +
          (t : Complex) * ((d : Complex) * Complex.I)) *
          ((d : Complex) * Complex.I) =
        Complex.I * ((d : Complex) *
          f ((x : Complex) + (y + d * t : Real) * Complex.I)) := by
    have harg : (x : Complex) + y * Complex.I +
        (t : Complex) * ((d : Complex) * Complex.I) =
      (x : Complex) + (y + d * t : Real) * Complex.I := by
      push_cast
      ring
    rw [harg]
    ring
  simp_rw [hpoint, intervalIntegral.integral_const_mul]
  congr 1
  simpa [smul_eq_mul, add_comm] using
    (intervalIntegral.smul_integral_comp_add_mul
      (f := fun s : Real => f ((x : Complex) + s * Complex.I))
      (a := (0 : Real)) (b := 1) d y)



theorem axisRectangleDisplacementContour_eq_wedgeContour
    (f : Complex -> Complex) (x y width height : Real) :
    complexDisplacementIntegral f (x + y * Complex.I) width +
        complexDisplacementIntegral f
          ((x + width : Real) + y * Complex.I)
          ((height : Complex) * Complex.I) +
        complexDisplacementIntegral f
          ((x + width : Real) + (y + height : Real) * Complex.I)
          ((-width : Real) : Complex) +
        complexDisplacementIntegral f
          (x + (y + height : Real) * Complex.I)
          ((-height : Real) * Complex.I) =
      Complex.wedgeIntegral (x + y * Complex.I)
          ((x + width : Real) + (y + height : Real) * Complex.I) f +
        Complex.wedgeIntegral
          ((x + width : Real) + (y + height : Real) * Complex.I)
          (x + y * Complex.I) f := by
  rw [complexDisplacementIntegral_ofReal,
    complexDisplacementIntegral_mul_I,
    complexDisplacementIntegral_ofReal,
    complexDisplacementIntegral_mul_I]
  unfold Complex.wedgeIntegral
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero,
    sub_zero, add_zero, Complex.add_im, mul_one, zero_add, smul_eq_mul]
  simp only [mul_comm Complex.I]
  have hcomm :
      (∫ s : Real in x..x + width, f ((s : Complex) + y * Complex.I)) =
        ∫ s : Real in x..x + width, f (y * Complex.I + (s : Complex)) := by
    apply intervalIntegral.integral_congr
    intro s _hs
    exact congrArg f (add_comm (s : Complex) (y * Complex.I))
  rw [hcomm]
  ring



theorem sum_horizontalComplexDisplacementIntegral
    (f : Complex -> Complex) (hf : Continuous f)
    (x y mesh : Real) (N : Nat) :
    (∑ k ∈ Finset.range N,
      complexDisplacementIntegral f
        ((x + (k : Real) * mesh : Real) + y * Complex.I) mesh) =
      complexDisplacementIntegral f (x + y * Complex.I)
        ((((N : Real) * mesh) : Real) : Complex) := by
  let a : Nat -> Real := fun k => x + (k : Real) * mesh
  let g : Real -> Complex := fun s => f (s + y * Complex.I)
  have hg : Continuous g := hf.comp (by fun_prop)
  have hint : ∀ k < N,
      IntervalIntegrable g MeasureTheory.volume (a k) (a (k + 1)) :=
    fun k _hk => hg.intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  simp_rw [complexDisplacementIntegral_ofReal]
  simpa [a, g, Nat.cast_add, add_mul, add_assoc] using hsum



theorem sum_verticalComplexDisplacementIntegral
    (f : Complex -> Complex) (hf : Continuous f)
    (x y mesh : Real) (N : Nat) :
    (∑ k ∈ Finset.range N,
      complexDisplacementIntegral f
        (x + (y + (k : Real) * mesh : Real) * Complex.I)
        ((mesh : Complex) * Complex.I)) =
      complexDisplacementIntegral f (x + y * Complex.I)
        (((N : Real) * mesh : Real) * Complex.I) := by
  let a : Nat -> Real := fun k => y + (k : Real) * mesh
  let g : Real -> Complex := fun s => f (x + s * Complex.I)
  have hg : Continuous g := hf.comp (by fun_prop)
  have hint : ∀ k < N,
      IntervalIntegrable g MeasureTheory.volume (a k) (a (k + 1)) :=
    fun k _hk => hg.intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  simp_rw [complexDisplacementIntegral_mul_I]
  rw [← Finset.mul_sum]
  congr 1
  simpa [a, g, Nat.cast_add, add_mul, add_assoc] using hsum


noncomputable def axisMacroDirectContour
    (f : Complex -> Complex) (x y mesh : Real)
    (width height : Nat) : Complex :=
  (∑ k ∈ Finset.range width,
      complexDisplacementIntegral f
        ((x + (k : Real) * mesh : Real) + y * Complex.I) mesh) +
    (∑ k ∈ Finset.range height,
      complexDisplacementIntegral f
        ((x + (width : Real) * mesh : Real) +
          (y + (k : Real) * mesh : Real) * Complex.I)
        ((mesh : Complex) * Complex.I)) +
    (∑ k ∈ Finset.range width,
      complexDisplacementIntegral f
        ((x + (width : Real) * mesh + (k : Real) * (-mesh) : Real) +
          (y + (height : Real) * mesh : Real) * Complex.I)
        ((-mesh : Real) : Complex)) +
    ∑ k ∈ Finset.range height,
      complexDisplacementIntegral f
        (x + (y + (height : Real) * mesh +
          (k : Real) * (-mesh) : Real) * Complex.I)
        (((-mesh : Real) : Complex) * Complex.I)



noncomputable def axisTwoEdgeStaircasePathIntegral
    (f : Complex -> Complex) (x y mesh : Real)
    (width height : Nat) : Complex :=
  let u : Complex := (mesh : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (mesh : Complex) / 2 * (1 + Complex.I)
  (∑ k ∈ Finset.range width,
      let a : Complex :=
        (x + (k : Real) * mesh : Real) + y * Complex.I
      complexDisplacementIntegral f a u +
        complexDisplacementIntegral f (a + u) v) +
    (∑ k ∈ Finset.range height,
      let a : Complex :=
        (x + (width : Real) * mesh : Real) +
          (y + (k : Real) * mesh : Real) * Complex.I
      complexDisplacementIntegral f a v +
        complexDisplacementIntegral f (a + v) (-u)) +
    (∑ k ∈ Finset.range width,
      let a : Complex :=
        (x + (width : Real) * mesh - (k : Real) * mesh : Real) +
          (y + (height : Real) * mesh : Real) * Complex.I
      complexDisplacementIntegral f a (-u) +
        complexDisplacementIntegral f (a - u) (-v)) +
    ∑ k ∈ Finset.range height,
      let a : Complex :=
        x + (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
          Complex.I
      complexDisplacementIntegral f a (-v) +
        complexDisplacementIntegral f (a - v) u



theorem axisTwoEdgeStaircase_base_norm_le
    (x y mesh : Real) (width height : Nat) (hmesh : 0 ≤ mesh) :
    let p : Complex := x + y * Complex.I
    (∀ k < width,
      norm (((x + (k : Real) * mesh : Real) + y * Complex.I) - p) ≤
        (width : Real) * mesh + (height : Real) * mesh) ∧
    (∀ k < height,
      norm (((x + (width : Real) * mesh : Real) +
        (y + (k : Real) * mesh : Real) * Complex.I) - p) ≤
        (width : Real) * mesh + (height : Real) * mesh) ∧
    (∀ k < width,
      norm (((x + (width : Real) * mesh - (k : Real) * mesh : Real) +
        (y + (height : Real) * mesh : Real) * Complex.I) - p) ≤
        (width : Real) * mesh + (height : Real) * mesh) ∧
    (∀ k < height,
      norm ((x + (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
        Complex.I) - p) ≤
        (width : Real) * mesh + (height : Real) * mesh) := by
  dsimp only
  have hwidth : 0 ≤ (width : Real) * mesh := mul_nonneg (by positivity) hmesh
  have hheight : 0 ≤ (height : Real) * mesh := mul_nonneg (by positivity) hmesh
  constructor
  · intro k hk
    calc
      norm (((x + (k : Real) * mesh : Real) + y * Complex.I) -
          (x + y * Complex.I)) ≤
        |(((x + (k : Real) * mesh : Real) + y * Complex.I) -
          (x + y * Complex.I)).re| +
        |(((x + (k : Real) * mesh : Real) + y * Complex.I) -
          (x + y * Complex.I)).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = (k : Real) * mesh := by
        have hkmesh : 0 ≤ mesh * (k : Real) :=
          mul_nonneg hmesh (by positivity)
        rw [show (((x + (k : Real) * mesh : Real) + y * Complex.I) -
            (x + y * Complex.I)).re = mesh * k by simp; ring,
          show (((x + (k : Real) * mesh : Real) + y * Complex.I) -
            (x + y * Complex.I)).im = 0 by simp]
        rw [abs_of_nonneg hkmesh, abs_zero, add_zero]
        ring
      _ ≤ (width : Real) * mesh + (height : Real) * mesh := by
        have hkR : (k : Real) ≤ width := by exact_mod_cast (Nat.le_of_lt hk)
        nlinarith
  · constructor
    · intro k hk
      calc
        norm (((x + (width : Real) * mesh : Real) +
            (y + (k : Real) * mesh : Real) * Complex.I) -
            (x + y * Complex.I)) ≤
          |(((x + (width : Real) * mesh : Real) +
            (y + (k : Real) * mesh : Real) * Complex.I) -
            (x + y * Complex.I)).re| +
          |(((x + (width : Real) * mesh : Real) +
            (y + (k : Real) * mesh : Real) * Complex.I) -
            (x + y * Complex.I)).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = (width : Real) * mesh + (k : Real) * mesh := by
          have hkmesh : 0 ≤ mesh * (k : Real) :=
            mul_nonneg hmesh (by positivity)
          rw [show (((x + (width : Real) * mesh : Real) +
              (y + (k : Real) * mesh : Real) * Complex.I) -
              (x + y * Complex.I)).re = width * mesh by simp,
            show (((x + (width : Real) * mesh : Real) +
              (y + (k : Real) * mesh : Real) * Complex.I) -
              (x + y * Complex.I)).im = mesh * k by simp; ring]
          rw [abs_of_nonneg hwidth, abs_of_nonneg hkmesh]
          ring
        _ ≤ (width : Real) * mesh + (height : Real) * mesh := by
          have hkR : (k : Real) ≤ height := by exact_mod_cast (Nat.le_of_lt hk)
          nlinarith
    · constructor
      · intro k hk
        calc
          norm (((x + (width : Real) * mesh - (k : Real) * mesh : Real) +
              (y + (height : Real) * mesh : Real) * Complex.I) -
              (x + y * Complex.I)) ≤
            |(((x + (width : Real) * mesh - (k : Real) * mesh : Real) +
              (y + (height : Real) * mesh : Real) * Complex.I) -
              (x + y * Complex.I)).re| +
            |(((x + (width : Real) * mesh - (k : Real) * mesh : Real) +
              (y + (height : Real) * mesh : Real) * Complex.I) -
              (x + y * Complex.I)).im| := Complex.norm_le_abs_re_add_abs_im _
          _ = ((width : Real) - k) * mesh + (height : Real) * mesh := by
            have hkR : (k : Real) ≤ width := by exact_mod_cast (Nat.le_of_lt hk)
            have hdiff : 0 ≤ (width : Real) * mesh - mesh * k := by
              nlinarith [mul_nonneg (sub_nonneg.mpr hkR) hmesh]
            rw [show (((x + (width : Real) * mesh - (k : Real) * mesh : Real) +
                (y + (height : Real) * mesh : Real) * Complex.I) -
                (x + y * Complex.I)).re = width * mesh - mesh * k by
                  simp; ring,
              show (((x + (width : Real) * mesh - (k : Real) * mesh : Real) +
                (y + (height : Real) * mesh : Real) * Complex.I) -
                (x + y * Complex.I)).im = height * mesh by simp]
            rw [abs_of_nonneg hdiff, abs_of_nonneg hheight]
            ring
          _ ≤ (width : Real) * mesh + (height : Real) * mesh := by
            have hkR : (0 : Real) ≤ k := by positivity
            nlinarith
      · intro k hk
        calc
          norm ((x +
              (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
                Complex.I) - (x + y * Complex.I)) ≤
            |((x +
              (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
                Complex.I) - (x + y * Complex.I)).re| +
            |((x +
              (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
                Complex.I) - (x + y * Complex.I)).im| :=
              Complex.norm_le_abs_re_add_abs_im _
          _ = ((height : Real) - k) * mesh := by
            have hkR : (k : Real) ≤ height := by exact_mod_cast (Nat.le_of_lt hk)
            have hdiff : 0 ≤ (height : Real) * mesh - mesh * k := by
              nlinarith [mul_nonneg (sub_nonneg.mpr hkR) hmesh]
            rw [show ((x +
                (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
                  Complex.I) - (x + y * Complex.I)).re = 0 by simp,
              show ((x +
                (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
                  Complex.I) - (x + y * Complex.I)).im =
                  height * mesh - mesh * k by simp; ring]
            rw [abs_zero, zero_add, abs_of_nonneg hdiff]
            ring
          _ ≤ (width : Real) * mesh + (height : Real) * mesh := by
            have hkR : (0 : Real) ≤ k := by positivity
            nlinarith



theorem axisMacroDirectContour_eq_wedgeContour
    (f : Complex -> Complex) (hf : Continuous f)
    (x y mesh : Real) (width height : Nat) :
    axisMacroDirectContour f x y mesh width height =
      Complex.wedgeIntegral (x + y * Complex.I)
          ((x + (width : Real) * mesh : Real) +
            (y + (height : Real) * mesh : Real) * Complex.I) f +
        Complex.wedgeIntegral
          ((x + (width : Real) * mesh : Real) +
            (y + (height : Real) * mesh : Real) * Complex.I)
          (x + y * Complex.I) f := by
  unfold axisMacroDirectContour
  rw [sum_horizontalComplexDisplacementIntegral f hf x y mesh width]
  rw [sum_verticalComplexDisplacementIntegral f hf
    (x + (width : Real) * mesh) y mesh height]
  rw [sum_horizontalComplexDisplacementIntegral f hf
    (x + (width : Real) * mesh) (y + (height : Real) * mesh)
    (-mesh) width]
  rw [sum_verticalComplexDisplacementIntegral f hf
    x (y + (height : Real) * mesh) (-mesh) height]
  convert axisRectangleDisplacementContour_eq_wedgeContour
    f x y ((width : Real) * mesh) ((height : Real) * mesh) using 1 <;>
    push_cast <;> ring



theorem norm_complexDisplacementIntegral_sub_const_mul_le
    (f : Complex -> Complex) (hf : Continuous f)
    (a v c : Complex) (epsilon : Real)
    (hosc : ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (f (a + (t : Complex) * v) - c) <= epsilon) :
    norm (complexDisplacementIntegral f a v - c * v) <=
      epsilon * norm v := by
  have hpath : Continuous (fun t : Real =>
      f (a + (t : Complex) * v) * v) := by
    fun_prop
  have hconst : Continuous (fun _t : Real => c * v) := continuous_const
  have heq : complexDisplacementIntegral f a v - c * v =
      ∫ t : Real in 0..1,
        (f (a + (t : Complex) * v) - c) * v := by
    unfold complexDisplacementIntegral
    rw [show c * v = ∫ _t : Real in 0..1, c * v by simp,
      ← intervalIntegral.integral_sub (hpath.intervalIntegrable 0 1)
        (hconst.intervalIntegrable 0 1)]
    apply intervalIntegral.integral_congr
    intro t _ht
    ring
  rw [heq]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : Real)) (b := 1) (C := epsilon * norm v)
    (f := fun t : Real => (f (a + (t : Complex) * v) - c) * v)
    (fun t ht => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hosc t (Set.Ioc_subset_Icc_self ht)) (norm_nonneg v))
  simpa using hbound



theorem norm_complexDisplacementIntegral_sub_le_of_uniformNorm
    (F G : Complex -> Complex) (hF : Continuous F) (hG : Continuous G)
    (a v : Complex) (epsilon : Real)
    (herror : ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (F (a + (t : Complex) * v) -
        G (a + (t : Complex) * v)) ≤ epsilon) :
    norm (complexDisplacementIntegral F a v -
      complexDisplacementIntegral G a v) ≤ epsilon * norm v := by
  have hpath : Continuous (fun t : Real => a + (t : Complex) * v) := by
    fun_prop
  have hFI : Continuous (fun t : Real =>
      F (a + (t : Complex) * v) * v) := (hF.comp hpath).mul continuous_const
  have hGI : Continuous (fun t : Real =>
      G (a + (t : Complex) * v) * v) := (hG.comp hpath).mul continuous_const
  have heq : complexDisplacementIntegral F a v -
      complexDisplacementIntegral G a v =
        complexDisplacementIntegral (fun z => F z - G z) a v := by
    unfold complexDisplacementIntegral
    rw [← intervalIntegral.integral_sub
      (hFI.intervalIntegrable 0 1) (hGI.intervalIntegrable 0 1)]
    apply intervalIntegral.integral_congr
    intro t _ht
    ring
  rw [heq]
  simpa using norm_complexDisplacementIntegral_sub_const_mul_le
    (fun z => F z - G z) (hF.sub hG) a v 0 epsilon (by
      intro t ht
      simpa using herror t ht)



theorem norm_twoStepDisplacementIntegral_sub_direct_le
    (f : Complex -> Complex) (hf : Continuous f)
    (a u v c : Complex) (epsilon : Real)
    (hu : ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (f (a + (t : Complex) * u) - c) <= epsilon)
    (hv : ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (f (a + u + (t : Complex) * v) - c) <= epsilon)
    (hdirect : ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (f (a + (t : Complex) * (u + v)) - c) <= epsilon) :
    norm (complexDisplacementIntegral f a u +
        complexDisplacementIntegral f (a + u) v -
        complexDisplacementIntegral f a (u + v)) <=
      epsilon * (norm u + norm v + norm (u + v)) := by
  have hU := norm_complexDisplacementIntegral_sub_const_mul_le
    f hf a u c epsilon hu
  have hV := norm_complexDisplacementIntegral_sub_const_mul_le
    f hf (a + u) v c epsilon hv
  have hD := norm_complexDisplacementIntegral_sub_const_mul_le
    f hf a (u + v) c epsilon hdirect
  calc
    norm (complexDisplacementIntegral f a u +
        complexDisplacementIntegral f (a + u) v -
        complexDisplacementIntegral f a (u + v)) =
      norm ((complexDisplacementIntegral f a u - c * u) +
        (complexDisplacementIntegral f (a + u) v - c * v) -
        (complexDisplacementIntegral f a (u + v) - c * (u + v))) := by
          congr 1
          ring
    _ <= norm (complexDisplacementIntegral f a u - c * u) +
        norm (complexDisplacementIntegral f (a + u) v - c * v) +
        norm (complexDisplacementIntegral f a (u + v) - c * (u + v)) := by
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_add_le _ _) (le_refl _))
    _ <= epsilon * norm u + epsilon * norm v + epsilon * norm (u + v) :=
      add_le_add (add_le_add hU hV) hD
    _ = epsilon * (norm u + norm v + norm (u + v)) := by ring



theorem norm_twoStepDisplacementIntegral_sub_direct_le_of_ball
    (f : Complex -> Complex) (hf : Continuous f)
    (a u v : Complex) (epsilon radius : Real)
    (huNorm : norm u ≤ radius) (hvNorm : norm v ≤ radius)
    (hosc : ∀ q, norm (q - a) ≤ 2 * radius ->
      norm (f q - f a) ≤ epsilon) :
    norm (complexDisplacementIntegral f a u +
        complexDisplacementIntegral f (a + u) v -
        complexDisplacementIntegral f a (u + v)) ≤
      epsilon * (norm u + norm v + norm (u + v)) := by
  apply norm_twoStepDisplacementIntegral_sub_direct_le
    f hf a u v (f a) epsilon
  · intro t ht
    apply hosc
    rw [show a + (t : Complex) * u - a = (t : Complex) * u by ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have htNorm : |t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    calc
      |t| * norm u ≤ 1 * radius :=
        mul_le_mul htNorm huNorm (norm_nonneg u) (by
          nlinarith [norm_nonneg u])
      _ ≤ 2 * radius := by nlinarith [norm_nonneg u]
  · intro t ht
    apply hosc
    rw [show a + u + (t : Complex) * v - a = u + (t : Complex) * v by ring]
    calc
      norm (u + (t : Complex) * v) ≤ norm u + norm ((t : Complex) * v) :=
        norm_add_le _ _
      _ = norm u + |t| * norm v := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 * radius := by
        have htNorm : |t| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [ht.1, ht.2]
        have hmul : |t| * norm v ≤ radius := by
          calc
            |t| * norm v ≤ 1 * radius :=
              mul_le_mul htNorm hvNorm (norm_nonneg v) (by
                nlinarith [norm_nonneg v])
            _ = radius := one_mul radius
        linarith
  · intro t ht
    apply hosc
    rw [show a + (t : Complex) * (u + v) - a =
      (t : Complex) * (u + v) by ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have htNorm : |t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have huv := norm_add_le u v
    have hsum : norm (u + v) ≤ 2 * radius := by linarith
    calc
      |t| * norm (u + v) ≤ 1 * (2 * radius) :=
        mul_le_mul htNorm hsum (norm_nonneg (u + v)) (by
          nlinarith [norm_nonneg u])
      _ = 2 * radius := one_mul _




theorem norm_sum_twoStepDisplacementIntegral_sub_direct_le
    (f : Complex -> Complex) (hf : Continuous f)
    (N : Nat) (a u v c : Nat -> Complex) (epsilon : Nat -> Real)
    (hu : ∀ k < N, ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (f (a k + (t : Complex) * u k) - c k) <= epsilon k)
    (hv : ∀ k < N, ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (f (a k + u k + (t : Complex) * v k) - c k) <= epsilon k)
    (hdirect : ∀ k < N, ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (f (a k + (t : Complex) * (u k + v k)) - c k) <=
        epsilon k) :
    norm (∑ k ∈ Finset.range N,
      (complexDisplacementIntegral f (a k) (u k) +
        complexDisplacementIntegral f (a k + u k) (v k) -
        complexDisplacementIntegral f (a k) (u k + v k))) <=
      ∑ k ∈ Finset.range N,
        epsilon k * (norm (u k) + norm (v k) + norm (u k + v k)) := by
  calc
    norm (∑ k ∈ Finset.range N,
        (complexDisplacementIntegral f (a k) (u k) +
          complexDisplacementIntegral f (a k + u k) (v k) -
          complexDisplacementIntegral f (a k) (u k + v k))) <=
        ∑ k ∈ Finset.range N,
          norm (complexDisplacementIntegral f (a k) (u k) +
            complexDisplacementIntegral f (a k + u k) (v k) -
            complexDisplacementIntegral f (a k) (u k + v k)) :=
      norm_sum_le _ _
    _ <= ∑ k ∈ Finset.range N,
        epsilon k * (norm (u k) + norm (v k) + norm (u k + v k)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact norm_twoStepDisplacementIntegral_sub_direct_le
        f hf (a k) (u k) (v k) (c k) (epsilon k)
        (hu k (Finset.mem_range.mp hk))
        (hv k (Finset.mem_range.mp hk))
        (hdirect k (Finset.mem_range.mp hk))



theorem norm_sum_twoEdgePath_sub_direct_le_of_ball
    (f : Complex -> Complex) (hf : Continuous f)
    (N : Nat) (a : Nat -> Complex) (u v : Complex)
    (epsilon radius : Real)
    (huNorm : norm u ≤ radius) (hvNorm : norm v ≤ radius)
    (hosc : ∀ k < N, ∀ q, norm (q - a k) ≤ 2 * radius ->
      norm (f q - f (a k)) ≤ epsilon) :
    norm ((∑ k ∈ Finset.range N,
        (complexDisplacementIntegral f (a k) u +
          complexDisplacementIntegral f (a k + u) v)) -
      ∑ k ∈ Finset.range N,
        complexDisplacementIntegral f (a k) (u + v)) ≤
      ∑ k ∈ Finset.range N,
        epsilon * (norm u + norm v + norm (u + v)) := by
  rw [← Finset.sum_sub_distrib]
  calc
    norm (∑ k ∈ Finset.range N,
        ((complexDisplacementIntegral f (a k) u +
          complexDisplacementIntegral f (a k + u) v) -
        complexDisplacementIntegral f (a k) (u + v))) ≤
      ∑ k ∈ Finset.range N,
        norm ((complexDisplacementIntegral f (a k) u +
          complexDisplacementIntegral f (a k + u) v) -
        complexDisplacementIntegral f (a k) (u + v)) := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N,
        epsilon * (norm u + norm v + norm (u + v)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply norm_twoStepDisplacementIntegral_sub_direct_le_of_ball
        f hf (a k) u v epsilon radius huNorm hvNorm
      exact hosc k (Finset.mem_range.mp hk)


theorem norm_sum_twoEdgePath_sub_le_of_uniformNorm
    (F G : Complex -> Complex) (hF : Continuous F) (hG : Continuous G)
    (N : Nat) (a : Nat -> Complex) (u v : Complex) (epsilon : Real)
    (herror : ∀ k < N, ∀ q,
      (∃ t ∈ Set.Icc (0 : Real) 1, q = a k + (t : Complex) * u) ∨
      (∃ t ∈ Set.Icc (0 : Real) 1,
        q = a k + u + (t : Complex) * v) ->
      norm (F q - G q) ≤ epsilon) :
    norm ((∑ k ∈ Finset.range N,
        (complexDisplacementIntegral F (a k) u +
          complexDisplacementIntegral F (a k + u) v)) -
      ∑ k ∈ Finset.range N,
        (complexDisplacementIntegral G (a k) u +
          complexDisplacementIntegral G (a k + u) v)) ≤
      ∑ k ∈ Finset.range N, epsilon * (norm u + norm v) := by
  rw [← Finset.sum_sub_distrib]
  calc
    norm (∑ k ∈ Finset.range N,
        ((complexDisplacementIntegral F (a k) u +
          complexDisplacementIntegral F (a k + u) v) -
        (complexDisplacementIntegral G (a k) u +
          complexDisplacementIntegral G (a k + u) v))) ≤
      ∑ k ∈ Finset.range N,
        norm ((complexDisplacementIntegral F (a k) u +
          complexDisplacementIntegral F (a k + u) v) -
        (complexDisplacementIntegral G (a k) u +
          complexDisplacementIntegral G (a k + u) v)) := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, epsilon * (norm u + norm v) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hu := norm_complexDisplacementIntegral_sub_le_of_uniformNorm
        F G hF hG (a k) u epsilon (by
          intro t ht
          exact herror k hk' _ (Or.inl ⟨t, ht, rfl⟩))
      have hv := norm_complexDisplacementIntegral_sub_le_of_uniformNorm
        F G hF hG (a k + u) v epsilon (by
          intro t ht
          exact herror k hk' _ (Or.inr ⟨t, ht, rfl⟩))
      calc
        norm ((complexDisplacementIntegral F (a k) u +
            complexDisplacementIntegral F (a k + u) v) -
          (complexDisplacementIntegral G (a k) u +
            complexDisplacementIntegral G (a k + u) v)) =
          norm ((complexDisplacementIntegral F (a k) u -
              complexDisplacementIntegral G (a k) u) +
            (complexDisplacementIntegral F (a k + u) v -
              complexDisplacementIntegral G (a k + u) v)) := by
                congr 1
                ring
        _ ≤ norm (complexDisplacementIntegral F (a k) u -
              complexDisplacementIntegral G (a k) u) +
            norm (complexDisplacementIntegral F (a k + u) v -
              complexDisplacementIntegral G (a k + u) v) := norm_add_le _ _
        _ ≤ epsilon * norm u + epsilon * norm v := add_le_add hu hv
        _ = epsilon * (norm u + norm v) := by ring



theorem norm_axisTwoEdgeStaircasePathIntegral_sub_le_of_uniformNorm
    (F G : Complex -> Complex) (hF : Continuous F) (hG : Continuous G)
    (x y mesh : Real) (width height : Nat) (epsilon : Real)
    (hmesh : 0 < mesh) (herror : ∀ q, norm (F q - G q) ≤ epsilon) :
    norm (axisTwoEdgeStaircasePathIntegral F x y mesh width height -
      axisTwoEdgeStaircasePathIntegral G x y mesh width height) ≤
        4 * epsilon * mesh * (width + height) := by
  let u : Complex := (mesh : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (mesh : Complex) / 2 * (1 + Complex.I)
  let ab : Nat -> Complex := fun k =>
    (x + (k : Real) * mesh : Real) + y * Complex.I
  let ar : Nat -> Complex := fun k =>
    (x + (width : Real) * mesh : Real) +
      (y + (k : Real) * mesh : Real) * Complex.I
  let atop : Nat -> Complex := fun k =>
    (x + (width : Real) * mesh - (k : Real) * mesh : Real) +
      (y + (height : Real) * mesh : Real) * Complex.I
  let al : Nat -> Complex := fun k =>
    x + (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
      Complex.I
  have hepsilon : 0 ≤ epsilon := (norm_nonneg (F 0 - G 0)).trans (herror 0)
  have huNorm : norm u ≤ mesh := by
    dsimp only [u]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hmesh]
    norm_num
    have h := norm_sub_le (1 : Complex) Complex.I
    rw [norm_one, Complex.norm_I] at h
    nlinarith
  have hvNorm : norm v ≤ mesh := by
    dsimp only [v]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hmesh]
    norm_num
    have h := norm_add_le (1 : Complex) Complex.I
    rw [norm_one, Complex.norm_I] at h
    nlinarith
  have sideBound (N : Nat) (a : Nat -> Complex) (du dv : Complex)
      (hdu : norm du ≤ mesh) (hdv : norm dv ≤ mesh) :
      norm ((∑ k ∈ Finset.range N,
          (complexDisplacementIntegral F (a k) du +
            complexDisplacementIntegral F (a k + du) dv)) -
        ∑ k ∈ Finset.range N,
          (complexDisplacementIntegral G (a k) du +
            complexDisplacementIntegral G (a k + du) dv)) ≤
        2 * epsilon * mesh * N := by
    calc
      _ ≤ ∑ k ∈ Finset.range N,
          epsilon * (norm du + norm dv) :=
        norm_sum_twoEdgePath_sub_le_of_uniformNorm
          F G hF hG N a du dv epsilon (by
            intro k hk q _hq
            exact herror q)
      _ ≤ ∑ _k ∈ Finset.range N, 2 * epsilon * mesh := by
        apply Finset.sum_le_sum
        intro k hk
        nlinarith
      _ = 2 * epsilon * mesh * N := by
        simp
        ring
  have hb := sideBound width ab u v huNorm hvNorm
  have hr := sideBound height ar v (-u) hvNorm (by simpa using huNorm)
  have ht := sideBound width atop (-u) (-v)
    (by simpa using huNorm) (by simpa using hvNorm)
  have hl := sideBound height al (-v) u (by simpa using hvNorm) huNorm
  have ht' :
      norm ((∑ k ∈ Finset.range width,
          (complexDisplacementIntegral F (atop k) (-u) +
            complexDisplacementIntegral F (atop k - u) (-v))) -
        ∑ k ∈ Finset.range width,
          (complexDisplacementIntegral G (atop k) (-u) +
            complexDisplacementIntegral G (atop k - u) (-v))) ≤
        2 * epsilon * mesh * width := by
    simpa [sub_eq_add_neg] using ht
  have hl' :
      norm ((∑ k ∈ Finset.range height,
          (complexDisplacementIntegral F (al k) (-v) +
            complexDisplacementIntegral F (al k - v) u)) -
        ∑ k ∈ Finset.range height,
          (complexDisplacementIntegral G (al k) (-v) +
            complexDisplacementIntegral G (al k - v) u)) ≤
        2 * epsilon * mesh * height := by
    simpa [sub_eq_add_neg] using hl
  have hdecomp :
      axisTwoEdgeStaircasePathIntegral F x y mesh width height -
          axisTwoEdgeStaircasePathIntegral G x y mesh width height =
        ((∑ k ∈ Finset.range width,
            (complexDisplacementIntegral F (ab k) u +
              complexDisplacementIntegral F (ab k + u) v)) -
          ∑ k ∈ Finset.range width,
            (complexDisplacementIntegral G (ab k) u +
              complexDisplacementIntegral G (ab k + u) v)) +
        ((∑ k ∈ Finset.range height,
            (complexDisplacementIntegral F (ar k) v +
              complexDisplacementIntegral F (ar k + v) (-u))) -
          ∑ k ∈ Finset.range height,
            (complexDisplacementIntegral G (ar k) v +
              complexDisplacementIntegral G (ar k + v) (-u))) +
        ((∑ k ∈ Finset.range width,
            (complexDisplacementIntegral F (atop k) (-u) +
              complexDisplacementIntegral F (atop k - u) (-v))) -
          ∑ k ∈ Finset.range width,
            (complexDisplacementIntegral G (atop k) (-u) +
              complexDisplacementIntegral G (atop k - u) (-v))) +
        ((∑ k ∈ Finset.range height,
            (complexDisplacementIntegral F (al k) (-v) +
              complexDisplacementIntegral F (al k - v) u)) -
          ∑ k ∈ Finset.range height,
            (complexDisplacementIntegral G (al k) (-v) +
              complexDisplacementIntegral G (al k - v) u)) := by
    unfold axisTwoEdgeStaircasePathIntegral
    dsimp only [u, v, ab, ar, atop, al]
    ring
  rw [hdecomp]
  calc
    norm (_ + _ + _ + _) ≤ norm (_ + _ + _) + norm _ := norm_add_le _ _
    _ ≤ (norm (_ + _) + norm _) + norm _ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((norm _ + norm _) + norm _) + norm _ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (2 * epsilon * mesh * width +
          2 * epsilon * mesh * height) +
        2 * epsilon * mesh * width +
          2 * epsilon * mesh * height := by
      exact add_le_add (add_le_add (add_le_add hb hr) ht') hl'
    _ = 4 * epsilon * mesh * (width + height) := by
      push_cast
      ring



theorem VanishingRectangleContourError.isConservativeOn_subsequentialLimit
    {F : Nat -> Complex -> Complex}
    (H : VanishingRectangleContourError F)
    (hF : forall n, Continuous (F n))
    {sigma : Nat -> Nat} (hsigma : Tendsto sigma atTop atTop)
    {f : Complex -> Complex}
    (hlimit : TendstoLocallyUniformlyOn (fun n => F (sigma n)) f atTop
      Set.univ) :
    Complex.IsConservativeOn f Set.univ := by
  have hf : Continuous f := continuousOn_univ.mp
    (hlimit.continuousOn (Filter.Frequently.of_forall
      (fun n => (hF (sigma n)).continuousOn)))
  intro z w _hrect
  have hcontourLimit : Tendsto
      (fun n => Complex.wedgeIntegral z w (F (sigma n)) +
        Complex.wedgeIntegral w z (F (sigma n))) atTop
      (nhds (Complex.wedgeIntegral z w f +
        Complex.wedgeIntegral w z f)) :=
    (complex_wedgeIntegral_tendsto_of_locallyUniform
      (fun n => hF (sigma n)) hlimit z w).add
      (complex_wedgeIntegral_tendsto_of_locallyUniform
        (fun n => hF (sigma n)) hlimit w z)
  have hzero := H.contour_tendsto_zero_comp hsigma z w
  have heq : Complex.wedgeIntegral z w f +
      Complex.wedgeIntegral w z f = 0 :=
    tendsto_nhds_unique hcontourLimit hzero
  exact eq_neg_of_add_eq_zero_left heq




theorem isingCellCRAt_conj_radialGridPosition
    (mesh : Real) (i j : Nat) :
    IsingCellCRAt
      (fun a b => (starRingEnd Complex) (isingRadialGridPosition mesh a b))
      i j := by
  unfold IsingCellCRAt isingRadialGridPosition
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;>
    ring



theorem isingCellCRAt_radialGridPosition_iff
    (mesh : Real) (i j : Nat) :
    IsingCellCRAt (fun a b => isingRadialGridPosition mesh a b) i j <->
      mesh = 0 := by
  constructor
  · intro h
    unfold IsingCellCRAt isingRadialGridPosition at h
    have him := congrArg Complex.im h
    simp [Complex.mul_re, Complex.mul_im] at him
    linarith
  · rintro rfl
    simp [IsingCellCRAt, isingRadialGridPosition]




def reflectedRadialBilinearCellContour
    (mesh : Real) (a00 a10 a01 a11 : Complex) : Complex :=
  let u : Complex := (mesh : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (mesh : Complex) / 2 * (1 + Complex.I)
  (u * (a00 + a10) + v * (a10 + a11) -
    u * (a01 + a11) - v * (a00 + a01)) / 2

theorem reflectedRadialBilinearCellContour_eq
    (mesh : Real) (a00 a10 a01 a11 : Complex) :
    reflectedRadialBilinearCellContour mesh a00 a10 a01 a11 =
      (mesh : Complex) / 2 *
        ((a10 - a01) + Complex.I * (a11 - a00)) := by
  unfold reflectedRadialBilinearCellContour
  ring

theorem intervalIntegral_complexAffine_unit (a b : Complex) :
    (∫ x : Real in 0..1,
      ((1 - x : Real) : Complex) * a + (x : Complex) * b) =
      (a + b) / 2 := by
  let P : Real -> Complex := fun x =>
    ((x : Complex) - (x : Complex) ^ 2 / 2) * a +
      ((x : Complex) ^ 2 / 2) * b
  have hP : forall x : Real, HasDerivAt P
      (((1 - x : Real) : Complex) * a + (x : Complex) * b) x := by
    intro x
    have hx : HasDerivAt (fun y : Real => (y : Complex)) 1 x :=
      (hasDerivAt_id (x : Complex)).comp_ofReal
    dsimp only [P]
    convert ((hx.sub ((hx.pow 2).div_const 2)).mul_const a).add
      (((hx.pow 2).div_const 2).mul_const b) using 1
    all_goals
      push_cast
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx => hP x)]
  · dsimp only [P]
    norm_num
    ring
  · exact (by fun_prop : Continuous (fun x : Real =>
      ((1 - x : Real) : Complex) * a + (x : Complex) * b)).intervalIntegrable 0 1



theorem complexDisplacementIntegral_eq_average_mul
    (f : Complex -> Complex) (a v A B : Complex)
    (haffine : ∀ t ∈ Set.Icc (0 : Real) 1,
      f (a + (t : Complex) * v) =
        ((1 - t : Real) : Complex) * A + (t : Complex) * B) :
    complexDisplacementIntegral f a v = (A + B) / 2 * v := by
  unfold complexDisplacementIntegral
  rw [intervalIntegral.integral_mul_const]
  congr 1
  rw [← intervalIntegral_complexAffine_unit A B]
  apply intervalIntegral.integral_congr
  intro t ht
  exact haffine t (by simpa [Set.uIcc_of_le zero_le_one] using ht)



noncomputable def reflectedRadialBilinearCellPathIntegral
    (mesh : Real) (a00 a10 a01 a11 : Complex) : Complex :=
  let u : Complex := (mesh : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (mesh : Complex) / 2 * (1 + Complex.I)
  (∫ x : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 x 0 * u) +
    (∫ y : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 1 y * v) -
    (∫ x : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 x 1 * u) -
    (∫ y : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 0 y * v)

theorem reflectedRadialBilinearCellPathIntegral_eq_contour
    (mesh : Real) (a00 a10 a01 a11 : Complex) :
    reflectedRadialBilinearCellPathIntegral mesh a00 a10 a01 a11 =
      reflectedRadialBilinearCellContour mesh a00 a10 a01 a11 := by
  have hbottom : (∫ x : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 x 0) = (a00 + a10) / 2 := by
    simpa [complexBilinearCell] using
      intervalIntegral_complexAffine_unit a00 a10
  have hright : (∫ y : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 1 y) = (a10 + a11) / 2 := by
    simpa [complexBilinearCell] using
      intervalIntegral_complexAffine_unit a10 a11
  have htop : (∫ x : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 x 1) = (a01 + a11) / 2 := by
    simpa [complexBilinearCell] using
      intervalIntegral_complexAffine_unit a01 a11
  have hleft : (∫ y : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 0 y) = (a00 + a01) / 2 := by
    simpa [complexBilinearCell] using
      intervalIntegral_complexAffine_unit a00 a01
  unfold reflectedRadialBilinearCellPathIntegral
    reflectedRadialBilinearCellContour
  simp_rw [intervalIntegral.integral_mul_const]
  rw [hbottom, hright, htop, hleft]
  ring



theorem reflectedRadialBilinearCellContour_eq_zero_of_cellCR
    (mesh : Real) (a00 a10 a01 a11 : Complex)
    (hCR : a01 - a10 = Complex.I * (a11 - a00)) :
    reflectedRadialBilinearCellContour mesh a00 a10 a01 a11 = 0 := by
  rw [reflectedRadialBilinearCellContour_eq]
  have h : a10 - a01 = -Complex.I * (a11 - a00) := by
    linear_combination -hCR
  rw [h]
  ring

theorem reflectedRadialBilinearCellPathIntegral_eq_zero_of_cellCR
    (mesh : Real) (a00 a10 a01 a11 : Complex)
    (hCR : a01 - a10 = Complex.I * (a11 - a00)) :
    reflectedRadialBilinearCellPathIntegral mesh a00 a10 a01 a11 = 0 := by
  rw [reflectedRadialBilinearCellPathIntegral_eq_contour]
  exact reflectedRadialBilinearCellContour_eq_zero_of_cellCR
    mesh a00 a10 a01 a11 hCR


theorem IsingCellCRAt.div_const
    {F : Nat -> Nat -> Complex} {i j : Nat}
    (hCR : IsingCellCRAt F i j) (c : Complex) :
    IsingCellCRAt (fun a b => F a b / c) i j := by
  unfold IsingCellCRAt at hCR ⊢
  rw [← sub_div, ← sub_div, hCR]
  ring



def reflectedRadialHorizontalEdgeIntegral
    (mesh : Real) (F : Nat -> Nat -> Complex) (i j : Nat) : Complex :=
  ((mesh : Complex) / 2 * (1 - Complex.I)) * (F i j + F (i + 1) j) / 2



def reflectedRadialVerticalEdgeIntegral
    (mesh : Real) (F : Nat -> Nat -> Complex) (i j : Nat) : Complex :=
  ((mesh : Complex) / 2 * (1 + Complex.I)) * (F i j + F i (j + 1)) / 2

theorem reflectedRadialBilinearCellContour_eq_edgeCoboundary
    (mesh : Real) (F : Nat -> Nat -> Complex) (i j : Nat) :
    reflectedRadialBilinearCellContour mesh
        (F i j) (F (i + 1) j) (F i (j + 1)) (F (i + 1) (j + 1)) =
      reflectedRadialHorizontalEdgeIntegral mesh F i j +
        reflectedRadialVerticalEdgeIntegral mesh F (i + 1) j -
        reflectedRadialHorizontalEdgeIntegral mesh F i (j + 1) -
        reflectedRadialVerticalEdgeIntegral mesh F i j := by
  unfold reflectedRadialBilinearCellContour
    reflectedRadialHorizontalEdgeIntegral reflectedRadialVerticalEdgeIntegral
  ring

theorem sum_range_add_one_sub (f : Nat -> Complex) (base n : Nat) :
    (∑ k ∈ Finset.range n, (f (base + k + 1) - f (base + k))) =
      f (base + n) - f base := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.add_succ]
      ring

theorem sum_range_sub_add_one (f : Nat -> Complex) (base n : Nat) :
    (∑ k ∈ Finset.range n, (f (base + k) - f (base + k + 1))) =
      f base - f (base + n) := by
  rw [show (∑ k ∈ Finset.range n,
      (f (base + k) - f (base + k + 1))) =
      -(∑ k ∈ Finset.range n,
        (f (base + k + 1) - f (base + k))) by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    ring]
  rw [sum_range_add_one_sub]
  ring




def reflectedRadialDiscretePrimitive
    (H V : Nat -> Nat -> Complex) (i0 j0 a b : Nat) : Complex :=
  (∑ x ∈ Finset.range a, H (i0 + x) j0) +
    ∑ y ∈ Finset.range b, V (i0 + a) (j0 + y)


theorem reflectedRadialDiscretePrimitive_succ_j
    (H V : Nat -> Nat -> Complex) (i0 j0 a b : Nat) :
    reflectedRadialDiscretePrimitive H V i0 j0 a (b + 1) -
        reflectedRadialDiscretePrimitive H V i0 j0 a b =
      V (i0 + a) (j0 + b) := by
  unfold reflectedRadialDiscretePrimitive
  rw [Finset.sum_range_succ]
  ring



theorem reflectedRadialDiscretePrimitive_succ_i
    (H V : Nat -> Nat -> Complex) (i0 j0 a b : Nat)
    (hcurl : ∀ y < b,
      H (i0 + a) (j0 + y) + V (i0 + a + 1) (j0 + y) -
        H (i0 + a) (j0 + y + 1) - V (i0 + a) (j0 + y) = 0) :
    reflectedRadialDiscretePrimitive H V i0 j0 (a + 1) b -
        reflectedRadialDiscretePrimitive H V i0 j0 a b =
      H (i0 + a) (j0 + b) := by
  have hVdiff :
      (∑ y ∈ Finset.range b, V (i0 + a + 1) (j0 + y)) -
          (∑ y ∈ Finset.range b, V (i0 + a) (j0 + y)) =
        H (i0 + a) (j0 + b) - H (i0 + a) j0 := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ y ∈ Finset.range b,
          (V (i0 + a + 1) (j0 + y) - V (i0 + a) (j0 + y))) =
          ∑ y ∈ Finset.range b,
            (H (i0 + a) (j0 + y + 1) - H (i0 + a) (j0 + y)) := by
        apply Finset.sum_congr rfl
        intro y hy
        have hc := hcurl y (Finset.mem_range.mp hy)
        linear_combination hc
      _ = H (i0 + a) (j0 + b) - H (i0 + a) j0 := by
        exact sum_range_add_one_sub (fun j => H (i0 + a) j) j0 b
  unfold reflectedRadialDiscretePrimitive
  rw [Finset.sum_range_succ]
  have hi : i0 + (a + 1) = i0 + a + 1 := by omega
  rw [hi]
  linear_combination hVdiff



theorem reflectedRadialDiscretePrimitive_succ_i_of_cellCR
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (i0 j0 a b : Nat)
    (hCR : ∀ y < b, IsingCellCRAt F (i0 + a) (j0 + y)) :
    reflectedRadialDiscretePrimitive
          (reflectedRadialHorizontalEdgeIntegral mesh F)
          (reflectedRadialVerticalEdgeIntegral mesh F)
          i0 j0 (a + 1) b -
        reflectedRadialDiscretePrimitive
          (reflectedRadialHorizontalEdgeIntegral mesh F)
          (reflectedRadialVerticalEdgeIntegral mesh F)
          i0 j0 a b =
      reflectedRadialHorizontalEdgeIntegral mesh F
        (i0 + a) (j0 + b) := by
  apply reflectedRadialDiscretePrimitive_succ_i
  intro y hy
  rw [← reflectedRadialBilinearCellContour_eq_edgeCoboundary]
  exact reflectedRadialBilinearCellContour_eq_zero_of_cellCR mesh _ _ _ _
    (hCR y hy)





def reflectedRadialAxisStaircaseBoundaryIntegral
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (i0 j0 width height : Nat) : Complex :=
  (∑ k ∈ Finset.range width,
      (reflectedRadialHorizontalEdgeIntegral mesh F
          (i0 + height + k) (j0 + k) +
        reflectedRadialVerticalEdgeIntegral mesh F
          (i0 + height + k + 1) (j0 + k))) +
    (∑ k ∈ Finset.range height,
      (reflectedRadialVerticalEdgeIntegral mesh F
          (i0 + width + (height - 1 - k) + 1) (j0 + width + k) -
        reflectedRadialHorizontalEdgeIntegral mesh F
          (i0 + width + (height - 1 - k)) (j0 + width + k + 1))) +
    (∑ k ∈ Finset.range width,
      (-reflectedRadialHorizontalEdgeIntegral mesh F
          (i0 + (width - 1 - k))
          (j0 + height + (width - 1 - k) + 1) -
        reflectedRadialVerticalEdgeIntegral mesh F
          (i0 + (width - 1 - k))
          (j0 + height + (width - 1 - k)))) +
    ∑ k ∈ Finset.range height,
      (-reflectedRadialVerticalEdgeIntegral mesh F
          (i0 + k) (j0 + (height - 1 - k)) +
        reflectedRadialHorizontalEdgeIntegral mesh F
          (i0 + k) (j0 + (height - 1 - k)))



noncomputable def reflectedRadialAxisStaircasePathIntegral
    (f : Complex -> Complex) (mesh : Real) (n i0 j0 width height : Nat) :
    Complex :=
  let u : Complex := (mesh : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (mesh : Complex) / 2 * (1 + Complex.I)
  (∑ k ∈ Finset.range width,
      (complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition
            mesh n (i0 + height + k) (j0 + k)) u +
        complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition
            mesh n (i0 + height + k + 1) (j0 + k)) v)) +
    (∑ k ∈ Finset.range height,
      (complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition mesh n
            (i0 + width + (height - 1 - k) + 1) (j0 + width + k)) v +
        complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition mesh n
            (i0 + width + (height - 1 - k) + 1)
            (j0 + width + k + 1)) (-u))) +
    (∑ k ∈ Finset.range width,
      (complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition mesh n
            (i0 + (width - 1 - k) + 1)
            (j0 + height + (width - 1 - k) + 1)) (-u) +
        complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition mesh n
            (i0 + (width - 1 - k))
            (j0 + height + (width - 1 - k) + 1)) (-v))) +
    ∑ k ∈ Finset.range height,
      (complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition mesh n
            (i0 + k) (j0 + (height - 1 - k) + 1)) (-v) +
        complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition mesh n
            (i0 + k) (j0 + (height - 1 - k))) u)



theorem reflectedRadialAxisStaircasePathIntegral_eq_axisTwoEdge
    (f : Complex -> Complex) (mesh : Real)
    (n i0 j0 width height : Nat) :
    let p := isingReflectedCenteredRadialGridPosition
      mesh n (i0 + height) j0
    reflectedRadialAxisStaircasePathIntegral
        f mesh n i0 j0 width height =
      axisTwoEdgeStaircasePathIntegral
        f p.re p.im mesh width height := by
  let p := isingReflectedCenteredRadialGridPosition
    mesh n (i0 + height) j0
  let u : Complex := (mesh : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (mesh : Complex) / 2 * (1 + Complex.I)
  have hbottomBase (k : Nat) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + height + k) (j0 + k) =
        (p.re + (k : Real) * mesh : Real) + p.im * Complex.I := by
    calc
      _ = p + (k : Real) * mesh := by
        simpa [p, Nat.add_assoc] using
          isingReflectedCenteredRadialGridPosition_diagonal_add
            mesh n (i0 + height) j0 k
      _ = _ := by apply Complex.ext <;> simp <;> ring
  have hbottomTurn (k : Nat) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + height + k + 1) (j0 + k) =
        ((p.re + (k : Real) * mesh : Real) + p.im * Complex.I) + u := by
    rw [show i0 + height + k + 1 = (i0 + height + k) + 1 by omega,
      isingReflectedCenteredRadialGridPosition_succ_i,
      hbottomBase]
  have hrightBase (k : Nat) (hk : k < height) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + width + (height - 1 - k) + 1) (j0 + width + k) =
        (p.re + (width : Real) * mesh : Real) +
          (p.im + (k : Real) * mesh : Real) * Complex.I := by
    have hk' : k ≤ height := by omega
    have hsub : height - 1 - k + 1 = height - k := by omega
    have hindex : i0 + width + (height - 1 - k) + 1 =
        (i0 + width) + (height - k) := by
      rw [Nat.add_assoc, hsub]
    calc
      _ = isingReflectedCenteredRadialGridPosition mesh n
          ((i0 + width) + (height - k)) ((j0 + width) + k) := by
        rw [hindex]
      _ = isingReflectedCenteredRadialGridPosition mesh n
          ((i0 + width) + height) (j0 + width) +
            ((k : Real) * mesh) * Complex.I :=
        isingReflectedCenteredRadialGridPosition_antidiagonal_add
          mesh n (i0 + width) (j0 + width) height k hk'
      _ = p + (width : Real) * mesh +
            ((k : Real) * mesh) * Complex.I := by
        rw [show i0 + width + height = i0 + height + width by omega]
        rw [show j0 + width = j0 + width by rfl]
        rw [show isingReflectedCenteredRadialGridPosition mesh n
            (i0 + height + width) (j0 + width) =
              p + (width : Real) * mesh by
          simpa [p, Nat.add_assoc] using
            isingReflectedCenteredRadialGridPosition_diagonal_add
              mesh n (i0 + height) j0 width]
      _ = _ := by apply Complex.ext <;> simp <;> ring
  have hrightTurn (k : Nat) (hk : k < height) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + width + (height - 1 - k) + 1)
          (j0 + width + k + 1) =
        ((p.re + (width : Real) * mesh : Real) +
          (p.im + (k : Real) * mesh : Real) * Complex.I) + v := by
    rw [show j0 + width + k + 1 = (j0 + width + k) + 1 by omega,
      isingReflectedCenteredRadialGridPosition_succ_j,
      hrightBase k hk]
  have htopBase (k : Nat) (hk : k < width) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + (width - 1 - k) + 1)
          (j0 + height + (width - 1 - k) + 1) =
        (p.re + (width : Real) * mesh - (k : Real) * mesh : Real) +
          (p.im + (height : Real) * mesh : Real) * Complex.I := by
    have hk' : k ≤ width := by omega
    have hsub : width - 1 - k + 1 = width - k := by omega
    have hi : i0 + (width - 1 - k) + 1 = i0 + (width - k) := by
      rw [Nat.add_assoc, hsub]
    have hj : j0 + height + (width - 1 - k) + 1 =
        (j0 + height) + (width - k) := by
      rw [Nat.add_assoc, hsub]
    calc
      _ = isingReflectedCenteredRadialGridPosition mesh n
          (i0 + (width - k)) ((j0 + height) + (width - k)) := by
        rw [hi, hj]
      _ = isingReflectedCenteredRadialGridPosition mesh n
          (i0 + width) ((j0 + height) + width) -
            (k : Real) * mesh :=
        isingReflectedCenteredRadialGridPosition_diagonal_sub
          mesh n i0 (j0 + height) width width k hk' hk'
      _ = isingReflectedCenteredRadialGridPosition mesh n
          i0 (j0 + height) + (width : Real) * mesh -
            (k : Real) * mesh := by
        rw [isingReflectedCenteredRadialGridPosition_diagonal_add]
      _ = p + ((height : Real) * mesh) * Complex.I +
            (width : Real) * mesh - (k : Real) * mesh := by
        rw [show isingReflectedCenteredRadialGridPosition mesh n
            i0 (j0 + height) =
              p + ((height : Real) * mesh) * Complex.I by
          simpa [p] using
            isingReflectedCenteredRadialGridPosition_antidiagonal_add
              mesh n i0 j0 height height (le_refl height)]
      _ = _ := by apply Complex.ext <;> simp <;> ring
  have htopTurn (k : Nat) (hk : k < width) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + (width - 1 - k))
          (j0 + height + (width - 1 - k) + 1) =
        ((p.re + (width : Real) * mesh - (k : Real) * mesh : Real) +
          (p.im + (height : Real) * mesh : Real) * Complex.I) - u := by
    have hs := isingReflectedCenteredRadialGridPosition_succ_i
      mesh n (i0 + (width - 1 - k))
        (j0 + height + (width - 1 - k) + 1)
    have hs' :
        isingReflectedCenteredRadialGridPosition mesh n
            (i0 + (width - 1 - k) + 1)
            (j0 + height + (width - 1 - k) + 1) =
          isingReflectedCenteredRadialGridPosition mesh n
              (i0 + (width - 1 - k))
              (j0 + height + (width - 1 - k) + 1) + u := by
      simpa [u] using hs
    rw [htopBase k hk] at hs'
    linear_combination -hs'
  have hleftBase (k : Nat) (hk : k < height) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + k) (j0 + (height - 1 - k) + 1) =
        p.re +
          (p.im + (height : Real) * mesh - (k : Real) * mesh : Real) *
            Complex.I := by
    have hk' : k ≤ height := by omega
    have hsub : height - 1 - k + 1 = height - k := by omega
    have hj : j0 + (height - 1 - k) + 1 = j0 + (height - k) := by
      rw [Nat.add_assoc, hsub]
    calc
      _ = isingReflectedCenteredRadialGridPosition mesh n
          (i0 + k) (j0 + (height - k)) := by rw [hj]
      _ = isingReflectedCenteredRadialGridPosition mesh n
          i0 (j0 + height) - ((k : Real) * mesh) * Complex.I :=
        isingReflectedCenteredRadialGridPosition_antidiagonal_sub
          mesh n i0 j0 height k hk'
      _ = p + ((height : Real) * mesh) * Complex.I -
            ((k : Real) * mesh) * Complex.I := by
        rw [show isingReflectedCenteredRadialGridPosition mesh n
            i0 (j0 + height) =
              p + ((height : Real) * mesh) * Complex.I by
          simpa [p] using
            isingReflectedCenteredRadialGridPosition_antidiagonal_add
              mesh n i0 j0 height height (le_refl height)]
      _ = _ := by apply Complex.ext <;> simp <;> ring
  have hleftTurn (k : Nat) (hk : k < height) :
      isingReflectedCenteredRadialGridPosition mesh n
          (i0 + k) (j0 + (height - 1 - k)) =
        (p.re +
          (p.im + (height : Real) * mesh - (k : Real) * mesh : Real) *
            Complex.I) - v := by
    have hs := isingReflectedCenteredRadialGridPosition_succ_j
      mesh n (i0 + k) (j0 + (height - 1 - k))
    have hs' :
        isingReflectedCenteredRadialGridPosition mesh n
            (i0 + k) (j0 + (height - 1 - k) + 1) =
          isingReflectedCenteredRadialGridPosition mesh n
              (i0 + k) (j0 + (height - 1 - k)) + v := by
      simpa [v] using hs
    rw [hleftBase k hk] at hs'
    linear_combination -hs'
  unfold reflectedRadialAxisStaircasePathIntegral
    axisTwoEdgeStaircasePathIntegral
  dsimp only
  congr 1
  · congr 1
    · congr 1
      · apply Finset.sum_congr rfl
        intro k _hk
        rw [hbottomBase k, hbottomTurn k]
      · apply Finset.sum_congr rfl
        intro k hk
        rw [hrightBase k (Finset.mem_range.mp hk),
          hrightTurn k (Finset.mem_range.mp hk)]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [htopBase k (Finset.mem_range.mp hk),
        htopTurn k (Finset.mem_range.mp hk)]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [hleftBase k (Finset.mem_range.mp hk),
      hleftTurn k (Finset.mem_range.mp hk)]




theorem reflectedRadialAxisStaircaseBoundaryIntegral_eq_zero_of_cellCR
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (i0 j0 width height : Nat)
    (hCR : ∀ a b, a < width + height -> b < width + height ->
      IsingCellCRAt F (i0 + a) (j0 + b)) :
    reflectedRadialAxisStaircaseBoundaryIntegral
      mesh F i0 j0 width height = 0 := by
  let H := reflectedRadialHorizontalEdgeIntegral mesh F
  let V := reflectedRadialVerticalEdgeIntegral mesh F
  let P : Nat -> Nat -> Complex := fun a b =>
    reflectedRadialDiscretePrimitive H V i0 j0 a b
  have hPi (a b : Nat) (ha : a < width + height)
      (hb : b ≤ width + height) :
      P (a + 1) b - P a b = H (i0 + a) (j0 + b) := by
    dsimp only [P, H, V]
    apply reflectedRadialDiscretePrimitive_succ_i_of_cellCR
    intro y hy
    exact hCR a y ha (lt_of_lt_of_le hy hb)
  have hPj (a b : Nat) :
      P a (b + 1) - P a b = V (i0 + a) (j0 + b) := by
    exact reflectedRadialDiscretePrimitive_succ_j H V i0 j0 a b
  let qb : Nat -> Complex := fun k => P (height + k) k
  let qr : Nat -> Complex := fun k => P (width + (height - k)) (width + k)
  let qt : Nat -> Complex := fun k => P (width - k) (height + (width - k))
  let ql : Nat -> Complex := fun k => P k (height - k)
  have hbottom (k : Nat) (hk : k < width) :
      H (i0 + height + k) (j0 + k) +
          V (i0 + height + k + 1) (j0 + k) =
        qb (k + 1) - qb k := by
    have hi := hPi (height + k) k (by omega) (by omega)
    have hj := hPj (height + k + 1) k
    dsimp only [qb]
    simp only [Nat.add_assoc]
    linear_combination -hi - hj
  have hright (k : Nat) (hk : k < height) :
      V (i0 + width + (height - 1 - k) + 1) (j0 + width + k) -
          H (i0 + width + (height - 1 - k)) (j0 + width + k + 1) =
        qr (k + 1) - qr k := by
    have hk1 : height - 1 - k + 1 = height - k := by omega
    have hknext : height - (k + 1) = height - 1 - k := by omega
    have hi := hPi (width + (height - 1 - k)) (width + k + 1)
      (by omega) (by omega)
    have hj := hPj (width + (height - k)) (width + k)
    have ha : width + (height - 1 - k) + 1 =
        width + (height - k) := by omega
    rw [ha] at hi
    dsimp only [qr]
    simp only [hknext, hk1, Nat.add_assoc]
    linear_combination hi - hj
  have htop (k : Nat) (hk : k < width) :
      -H (i0 + (width - 1 - k))
          (j0 + height + (width - 1 - k) + 1) -
          V (i0 + (width - 1 - k))
            (j0 + height + (width - 1 - k)) =
        qt (k + 1) - qt k := by
    have hk1 : width - 1 - k + 1 = width - k := by omega
    have hknext : width - (k + 1) = width - 1 - k := by omega
    have hi := hPi (width - 1 - k) (height + (width - k))
      (by omega) (by omega)
    have hj := hPj (width - 1 - k) (height + (width - 1 - k))
    have hb : height + (width - 1 - k) + 1 =
        height + (width - k) := by omega
    rw [hk1] at hi
    rw [hb] at hj
    dsimp only [qt]
    simp only [hknext, Nat.add_assoc]
    rw [hk1]
    linear_combination hi + hj
  have hleft (k : Nat) (hk : k < height) :
      -V (i0 + k) (j0 + (height - 1 - k)) +
          H (i0 + k) (j0 + (height - 1 - k)) =
        ql (k + 1) - ql k := by
    have hk1 : height - 1 - k + 1 = height - k := by omega
    have hknext : height - (k + 1) = height - 1 - k := by omega
    have hi := hPi k (height - 1 - k) (by omega) (by omega)
    have hj := hPj k (height - 1 - k)
    rw [hk1] at hj
    dsimp only [ql]
    simp only [hknext]
    linear_combination -hi + hj
  have hbottomSum :
      (∑ k ∈ Finset.range width,
        (H (i0 + height + k) (j0 + k) +
          V (i0 + height + k + 1) (j0 + k))) =
        qb width - qb 0 := by
    calc
      _ = ∑ k ∈ Finset.range width, (qb (k + 1) - qb k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hbottom k (Finset.mem_range.mp hk)
      _ = qb width - qb 0 := by
        simpa using sum_range_add_one_sub qb 0 width
  have hrightSum :
      (∑ k ∈ Finset.range height,
        (V (i0 + width + (height - 1 - k) + 1) (j0 + width + k) -
          H (i0 + width + (height - 1 - k)) (j0 + width + k + 1))) =
        qr height - qr 0 := by
    calc
      _ = ∑ k ∈ Finset.range height, (qr (k + 1) - qr k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hright k (Finset.mem_range.mp hk)
      _ = qr height - qr 0 := by
        simpa using sum_range_add_one_sub qr 0 height
  have htopSum :
      (∑ k ∈ Finset.range width,
        (-H (i0 + (width - 1 - k))
            (j0 + height + (width - 1 - k) + 1) -
          V (i0 + (width - 1 - k))
            (j0 + height + (width - 1 - k)))) =
        qt width - qt 0 := by
    calc
      _ = ∑ k ∈ Finset.range width, (qt (k + 1) - qt k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact htop k (Finset.mem_range.mp hk)
      _ = qt width - qt 0 := by
        simpa using sum_range_add_one_sub qt 0 width
  have hleftSum :
      (∑ k ∈ Finset.range height,
        (-V (i0 + k) (j0 + (height - 1 - k)) +
          H (i0 + k) (j0 + (height - 1 - k)))) =
        ql height - ql 0 := by
    calc
      _ = ∑ k ∈ Finset.range height, (ql (k + 1) - ql k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hleft k (Finset.mem_range.mp hk)
      _ = ql height - ql 0 := by
        simpa using sum_range_add_one_sub ql 0 height
  unfold reflectedRadialAxisStaircaseBoundaryIntegral
  change (∑ k ∈ Finset.range width,
      (H (i0 + height + k) (j0 + k) +
        V (i0 + height + k + 1) (j0 + k))) +
    (∑ k ∈ Finset.range height,
      (V (i0 + width + (height - 1 - k) + 1) (j0 + width + k) -
        H (i0 + width + (height - 1 - k)) (j0 + width + k + 1))) +
    (∑ k ∈ Finset.range width,
      (-H (i0 + (width - 1 - k))
          (j0 + height + (width - 1 - k) + 1) -
        V (i0 + (width - 1 - k))
          (j0 + height + (width - 1 - k)))) +
    (∑ k ∈ Finset.range height,
      (-V (i0 + k) (j0 + (height - 1 - k)) +
        H (i0 + k) (j0 + (height - 1 - k)))) = 0
  rw [hbottomSum, hrightSum, htopSum, hleftSum]
  dsimp only [qb, qr, qt, ql]
  simp
  ring


def reflectedRadialRectangleBoundaryIntegral
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (i0 j0 width height : Nat) : Complex :=
  (∑ i ∈ Finset.range width,
      reflectedRadialHorizontalEdgeIntegral mesh F (i0 + i) j0) +
    (∑ j ∈ Finset.range height,
      reflectedRadialVerticalEdgeIntegral mesh F (i0 + width) (j0 + j)) -
    (∑ i ∈ Finset.range width,
      reflectedRadialHorizontalEdgeIntegral mesh F (i0 + i) (j0 + height)) -
    (∑ j ∈ Finset.range height,
      reflectedRadialVerticalEdgeIntegral mesh F i0 (j0 + j))



theorem sum_reflectedRadialBilinearCellContour_eq_rectangleBoundary
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (i0 j0 width height : Nat) :
    (∑ j ∈ Finset.range height, ∑ i ∈ Finset.range width,
      reflectedRadialBilinearCellContour mesh
        (F (i0 + i) (j0 + j))
        (F (i0 + i + 1) (j0 + j))
        (F (i0 + i) (j0 + j + 1))
        (F (i0 + i + 1) (j0 + j + 1))) =
      reflectedRadialRectangleBoundaryIntegral mesh F i0 j0 width height := by
  let H : Nat -> Nat -> Complex :=
    reflectedRadialHorizontalEdgeIntegral mesh F
  let V : Nat -> Nat -> Complex :=
    reflectedRadialVerticalEdgeIntegral mesh F
  have hrow (j : Nat) :
      (∑ i ∈ Finset.range width,
        reflectedRadialBilinearCellContour mesh
          (F (i0 + i) j) (F (i0 + i + 1) j)
          (F (i0 + i) (j + 1)) (F (i0 + i + 1) (j + 1))) =
        (∑ i ∈ Finset.range width, H (i0 + i) j) +
          V (i0 + width) j -
          (∑ i ∈ Finset.range width, H (i0 + i) (j + 1)) - V i0 j := by
    simp only [reflectedRadialBilinearCellContour_eq_edgeCoboundary,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    change (∑ i ∈ Finset.range width, H (i0 + i) j) +
        (∑ i ∈ Finset.range width, V (i0 + i + 1) j) -
        (∑ i ∈ Finset.range width, H (i0 + i) (j + 1)) -
        (∑ i ∈ Finset.range width, V (i0 + i) j) = _
    have hV := sum_range_add_one_sub (fun i => V i j) i0 width
    have hV' : (∑ i ∈ Finset.range width, V (i0 + i + 1) j) -
        (∑ i ∈ Finset.range width, V (i0 + i) j) =
        V (i0 + width) j - V i0 j := by
      rw [← Finset.sum_sub_distrib]
      exact hV
    linear_combination hV'
  simp only [hrow]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hH := sum_range_sub_add_one
    (fun j => ∑ i ∈ Finset.range width, H (i0 + i) j) j0 height
  rw [Finset.sum_sub_distrib] at hH
  unfold reflectedRadialRectangleBoundaryIntegral
  dsimp only [H, V] at hH ⊢
  linear_combination hH



theorem reflectedRadialRectangleBoundaryIntegral_eq_zero_of_cellCR
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (i0 j0 width height : Nat)
    (hCR : forall i j, i < width -> j < height ->
      IsingCellCRAt F (i0 + i) (j0 + j)) :
    reflectedRadialRectangleBoundaryIntegral mesh F i0 j0 width height = 0 := by
  rw [← sum_reflectedRadialBilinearCellContour_eq_rectangleBoundary]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro i hi
  exact reflectedRadialBilinearCellContour_eq_zero_of_cellCR mesh _ _ _ _
    (hCR i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj))




def reflectedRadialCellRegionBoundaryIntegral
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (cells : Finset (Nat × Nat)) : Complex :=
  ∑ p ∈ cells, reflectedRadialBilinearCellContour mesh
    (F p.1 p.2) (F (p.1 + 1) p.2)
    (F p.1 (p.2 + 1)) (F (p.1 + 1) (p.2 + 1))



theorem reflectedRadialCellRegionBoundaryIntegral_eq_zero_of_cellCR
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (cells : Finset (Nat × Nat))
    (hCR : forall p, p ∈ cells -> IsingCellCRAt F p.1 p.2) :
    reflectedRadialCellRegionBoundaryIntegral mesh F cells = 0 := by
  unfold reflectedRadialCellRegionBoundaryIntegral
  apply Finset.sum_eq_zero
  intro p hp
  exact reflectedRadialBilinearCellContour_eq_zero_of_cellCR mesh _ _ _ _
    (hCR p hp)



theorem fkIsingSquareBoundaryRadialPatchFullObservableExtension_reflectedRegionContour_eq_zero
    (n m : Nat) (hn : 0 < n) (hm : m <= n) (mesh : Real)
    (cells : Finset (Nat × Nat))
    (hinterior : forall p, p ∈ cells ->
      p.1 + 2 < m ∧ p.2 + 2 < m) :
    reflectedRadialCellRegionBoundaryIntegral mesh
      (fkIsingSquareBoundaryRadialPatchFullObservableExtension n m hn hm)
      cells = 0 := by
  apply reflectedRadialCellRegionBoundaryIntegral_eq_zero_of_cellCR
  intro p hp
  exact fkIsingSquareBoundaryRadialPatchFullObservable_cellCR
    n m p.1 p.2 hn hm (hinterior p hp).1 (hinterior p hp).2





theorem
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_reflectedRegionContour_eq_zero
    (n : Nat) (hn : 0 < n) (mesh : Real)
    (cells : Finset (Nat × Nat))
    (hinterior : forall p, p ∈ cells ->
      p.1 + 2 < 2 * n ∧ p.2 + 2 < 2 * n) :
    reflectedRadialCellRegionBoundaryIntegral mesh
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn)
      cells = 0 := by
  apply reflectedRadialCellRegionBoundaryIntegral_eq_zero_of_cellCR
  intro p hp
  exact fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
    n p.1 p.2 hn (hinterior p hp).1 (hinterior p hp).2



theorem
    fkIsingSquareBoundaryCenteredRadialPatchNormalizedExtension_reflectedRegionContour_eq_zero
    (n : Nat) (hn : 0 < n) (gridScale normalizationScale : Real)
    (cells : Finset (Nat × Nat))
    (hinterior : forall p, p ∈ cells ->
      p.1 + 2 < 2 * n ∧ p.2 + 2 < 2 * n) :
    reflectedRadialCellRegionBoundaryIntegral gridScale
      (fun i j =>
        fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
            n hn i j /
          (Real.sqrt (2 * normalizationScale) : Complex))
      cells = 0 := by
  apply reflectedRadialCellRegionBoundaryIntegral_eq_zero_of_cellCR
  intro p hp
  exact (fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
    n p.1 p.2 hn (hinterior p hp).1 (hinterior p hp).2).div_const _



theorem
    fkIsingSquareBoundaryCenteredRadialPatch_reflectedCellPathIntegral_eq_zero
    (n i j : Nat) (hn : 0 < n)
    (hi : i + 2 < 2 * n) (hj : j + 2 < 2 * n)
    (gridScale normalizationScale : Real) :
    reflectedRadialBilinearCellPathIntegral gridScale
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          n hn i j / (Real.sqrt (2 * normalizationScale) : Complex))
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          n hn (i + 1) j / (Real.sqrt (2 * normalizationScale) : Complex))
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          n hn i (j + 1) / (Real.sqrt (2 * normalizationScale) : Complex))
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          n hn (i + 1) (j + 1) /
            (Real.sqrt (2 * normalizationScale) : Complex)) = 0 := by
  apply reflectedRadialBilinearCellPathIntegral_eq_zero_of_cellCR
  exact (fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
    n i j hn hi hj).div_const _




noncomputable def
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
    (k : Nat) : Complex -> Complex :=
  fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareMesh k)


theorem fkIsingExpandingSquareScale_mul_side (k : Nat) :
    fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k =
      (k + 1 : Nat) := by
  simp [fkIsingExpandingSquareScale, fkIsingExpandingSquareSide]
  field_simp



theorem fkIsingExpandingSquareScale_mul_side_tendsto_atTop :
    Tendsto (fun k =>
      fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k)
      atTop atTop := by
  simpa only [fkIsingExpandingSquareScale_mul_side] using
    ((tendsto_natCast_atTop_atTop (R := Real)).comp
      (tendsto_add_atTop_nat 1))

theorem fkIsingExpandingSquareScale_tendsto_zero :
    Tendsto fkIsingExpandingSquareScale atTop (nhds 0) := by
  have hadd : Tendsto (fun k : Nat => k + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hinv : Tendsto (fun k : Nat => (1 : Real) / (k + 1 : Nat))
      atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat.comp hadd
  change Tendsto (fun k : Nat => (1 : Real) / (k + 1 : Nat))
    atTop (nhds 0)
  exact hinv



theorem fkIsingExpandingSquareCenteredInteriorRadius_tendsto_atTop
    (layers : Real) :
    Tendsto (fun k =>
      fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k -
        layers * fkIsingExpandingSquareScale k) atTop atTop := by
  have hsmall : Tendsto (fun k =>
      -(layers * fkIsingExpandingSquareScale k)) atTop (nhds 0) := by
    simpa using
      (fkIsingExpandingSquareScale_tendsto_zero.const_mul layers).neg
  simpa [sub_eq_add_neg] using Filter.Tendsto.atTop_add
    fkIsingExpandingSquareScale_mul_side_tendsto_atTop hsmall

theorem fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior
    (R layers : Real) :
    ∀ᶠ k in atTop,
      R ≤ fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k -
        layers * fkIsingExpandingSquareScale k :=
  (tendsto_atTop.1
    (fkIsingExpandingSquareCenteredInteriorRadius_tendsto_atTop layers)) R




def shiftedRealGridFloor (mesh shift x : Real) : Real :=
  mesh * (((⌊x / mesh - shift⌋ : Int) : Real) + shift)



theorem shiftedRealGridFloor_error
    (mesh shift x : Real) (hmesh : 0 < mesh) :
    0 ≤ x - shiftedRealGridFloor mesh shift x ∧
      x - shiftedRealGridFloor mesh shift x < mesh := by
  let q : Int := ⌊x / mesh - shift⌋
  have hlo : (q : Real) ≤ x / mesh - shift := by
    exact_mod_cast Int.floor_le (x / mesh - shift)
  have hhi : x / mesh - shift < (q : Real) + 1 := by
    exact_mod_cast Int.lt_floor_add_one (x / mesh - shift)
  unfold shiftedRealGridFloor
  change 0 ≤ x - mesh * ((q : Real) + shift) ∧
    x - mesh * ((q : Real) + shift) < mesh
  constructor <;> (field_simp at hlo hhi ⊢ <;> nlinarith)

theorem abs_shiftedRealGridFloor_sub_lt
    (mesh shift x : Real) (hmesh : 0 < mesh) :
    |shiftedRealGridFloor mesh shift x - x| < mesh := by
  have h := shiftedRealGridFloor_error mesh shift x hmesh
  rw [abs_lt]
  constructor <;> linarith


theorem shiftedRealGridFloor_mono
    (mesh shift x y : Real) (hmesh : 0 < mesh) (hxy : x ≤ y) :
    shiftedRealGridFloor mesh shift x ≤
      shiftedRealGridFloor mesh shift y := by
  unfold shiftedRealGridFloor
  apply mul_le_mul_of_nonneg_left _ hmesh.le
  gcongr


def shiftedRealGridFloorSteps
    (mesh shift x y : Real) : Nat :=
  Int.toNat (⌊y / mesh - shift⌋ - ⌊x / mesh - shift⌋)

theorem shiftedRealGridFloor_add_steps
    (mesh shift x y : Real) (hmesh : 0 < mesh) (hxy : x ≤ y) :
    shiftedRealGridFloor mesh shift x +
        (shiftedRealGridFloorSteps mesh shift x y : Real) * mesh =
      shiftedRealGridFloor mesh shift y := by
  let qx : Int := ⌊x / mesh - shift⌋
  let qy : Int := ⌊y / mesh - shift⌋
  have hq : qx ≤ qy := by
    apply Int.floor_mono
    exact sub_le_sub_right (div_le_div_of_nonneg_right hxy hmesh.le) shift
  have hcast : (Int.toNat (qy - qx) : Int) = qy - qx :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hq)
  have hcastR : (Int.toNat (qy - qx) : Real) = (qy : Real) - (qx : Real) := by
    exact_mod_cast hcast
  unfold shiftedRealGridFloor shiftedRealGridFloorSteps
  change mesh * ((qx : Real) + shift) +
      (Int.toNat (qy - qx) : Real) * mesh =
    mesh * ((qy : Real) + shift)
  rw [hcastR]
  ring

theorem shiftedRealGridFloor_tendsto
    (mesh : Nat -> Real) (hmeshPos : ∀ k, 0 < mesh k)
    (hmesh : Tendsto mesh atTop (nhds 0)) (shift x : Real) :
    Tendsto (fun k => shiftedRealGridFloor (mesh k) shift x)
      atTop (nhds x) := by
  rw [Metric.tendsto_atTop] at hmesh ⊢
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hmesh epsilon hepsilon
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq]
  have hkMesh : mesh k < epsilon := by
    simpa [Real.dist_eq, abs_of_pos (hmeshPos k)] using hN k hk
  exact (abs_shiftedRealGridFloor_sub_lt
    (mesh k) shift x (hmeshPos k)).trans hkMesh




def reflectedRadialAxisSnap (mesh : Real) (z : Complex) : Complex :=
  shiftedRealGridFloor mesh (1 / 2) z.re +
  shiftedRealGridFloor mesh 0 z.im * Complex.I

def reflectedRadialAxisSnapWidth
    (mesh : Real) (z w : Complex) : Nat :=
  shiftedRealGridFloorSteps mesh (1 / 2) z.re w.re

def reflectedRadialAxisSnapHeight
    (mesh : Real) (z w : Complex) : Nat :=
  shiftedRealGridFloorSteps mesh 0 z.im w.im

theorem reflectedRadialAxisSnapWidth_mul_mesh_le
    (mesh : Real) (z w : Complex) (hmesh : 0 < mesh)
    (hre : z.re ≤ w.re) :
    (reflectedRadialAxisSnapWidth mesh z w : Real) * mesh ≤
      w.re - z.re + mesh := by
  have hadd := shiftedRealGridFloor_add_steps
    mesh (1 / 2) z.re w.re hmesh hre
  have hz := shiftedRealGridFloor_error mesh (1 / 2) z.re hmesh
  have hw := shiftedRealGridFloor_error mesh (1 / 2) w.re hmesh
  unfold reflectedRadialAxisSnapWidth
  nlinarith

theorem reflectedRadialAxisSnapHeight_mul_mesh_le
    (mesh : Real) (z w : Complex) (hmesh : 0 < mesh)
    (him : z.im ≤ w.im) :
    (reflectedRadialAxisSnapHeight mesh z w : Real) * mesh ≤
      w.im - z.im + mesh := by
  have hadd := shiftedRealGridFloor_add_steps
    mesh 0 z.im w.im hmesh him
  have hz := shiftedRealGridFloor_error mesh 0 z.im hmesh
  have hw := shiftedRealGridFloor_error mesh 0 w.im hmesh
  unfold reflectedRadialAxisSnapHeight
  nlinarith



theorem reflectedRadialAxisSnap_oppositeCorner
    (mesh : Real) (z w : Complex) (hmesh : 0 < mesh)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    (shiftedRealGridFloor mesh (1 / 2) z.re +
        (reflectedRadialAxisSnapWidth mesh z w : Real) * mesh : Real) +
      (shiftedRealGridFloor mesh 0 z.im +
        (reflectedRadialAxisSnapHeight mesh z w : Real) * mesh : Real) *
        Complex.I =
      reflectedRadialAxisSnap mesh w := by
  unfold reflectedRadialAxisSnapWidth reflectedRadialAxisSnapHeight
    reflectedRadialAxisSnap
  rw [shiftedRealGridFloor_add_steps mesh (1 / 2) z.re w.re hmesh hre,
    shiftedRealGridFloor_add_steps mesh 0 z.im w.im hmesh him]

theorem reflectedRadialAxisSnap_dist_lt
    (mesh : Real) (z : Complex) (hmesh : 0 < mesh) :
    dist (reflectedRadialAxisSnap mesh z) z < 2 * mesh := by
  rw [dist_eq_norm]
  have hre := abs_shiftedRealGridFloor_sub_lt mesh (1 / 2) z.re hmesh
  have him := abs_shiftedRealGridFloor_sub_lt mesh 0 z.im hmesh
  calc
    norm (reflectedRadialAxisSnap mesh z - z) ≤
        |(reflectedRadialAxisSnap mesh z - z).re| +
          |(reflectedRadialAxisSnap mesh z - z).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |shiftedRealGridFloor mesh (1 / 2) z.re - z.re| +
        |shiftedRealGridFloor mesh 0 z.im - z.im| := by
      simp [reflectedRadialAxisSnap]
    _ < 2 * mesh := by linarith

theorem reflectedRadialAxisSnap_tendsto
    (mesh : Nat -> Real) (hmeshPos : ∀ k, 0 < mesh k)
    (hmesh : Tendsto mesh atTop (nhds 0)) (z : Complex) :
    Tendsto (fun k => reflectedRadialAxisSnap (mesh k) z)
      atTop (nhds z) := by
  unfold reflectedRadialAxisSnap
  have hre := shiftedRealGridFloor_tendsto mesh hmeshPos hmesh (1 / 2) z.re
  have him := shiftedRealGridFloor_tendsto mesh hmeshPos hmesh 0 z.im
  simpa only [Complex.re_add_im] using
    hre.ofReal.add (him.ofReal.mul_const Complex.I)


def reflectedRadialAxisSnapI (n : Nat) (mesh : Real) (z : Complex) : Nat :=
  Int.toNat ((n : Int) + ⌊z.re / mesh - 1 / 2⌋ - ⌊z.im / mesh⌋)

def reflectedRadialAxisSnapJ (n : Nat) (mesh : Real) (z : Complex) : Nat :=
  Int.toNat ((n : Int) + ⌊z.re / mesh - 1 / 2⌋ + ⌊z.im / mesh⌋)




def reflectedRadialAxisSnapBaseI
    (n : Nat) (mesh : Real) (z w : Complex) : Nat :=
  Int.toNat ((n : Int) + ⌊z.re / mesh - 1 / 2⌋ - ⌊w.im / mesh⌋)

def reflectedRadialAxisSnapBaseJ
    (n : Nat) (mesh : Real) (z : Complex) : Nat :=
  Int.toNat ((n : Int) + ⌊z.re / mesh - 1 / 2⌋ + ⌊z.im / mesh⌋)



theorem reflectedRadialAxisFloor_box
    (n : Nat) (mesh x y : Real) (hmesh : 0 < mesh)
    (hinside : |x| + |y| + 3 * mesh ≤ mesh * n) :
    0 ≤ (n : Int) + ⌊x / mesh - 1 / 2⌋ - ⌊y / mesh⌋ ∧
      0 ≤ (n : Int) + ⌊x / mesh - 1 / 2⌋ + ⌊y / mesh⌋ ∧
      ⌊x / mesh - 1 / 2⌋ - ⌊y / mesh⌋ + 1 < (n : Int) ∧
      ⌊x / mesh - 1 / 2⌋ + ⌊y / mesh⌋ + 1 < (n : Int) := by
  let qx : Int := ⌊x / mesh - 1 / 2⌋
  let qy : Int := ⌊y / mesh⌋
  have hinside' : |x| / mesh + |y| / mesh + 3 ≤ (n : Real) := by
    have hdiv : (|x| + |y| + 3 * mesh) / mesh ≤ (n : Real) :=
      (div_le_iff₀ hmesh).2 (by nlinarith)
    convert hdiv using 1 <;> field_simp <;> ring
  have hxlo : -(|x| / mesh) ≤ x / mesh := by
    simpa only [neg_div] using
      div_le_div_of_nonneg_right (neg_abs_le x) hmesh.le
  have hxhi : x / mesh ≤ |x| / mesh := by
    exact div_le_div_of_nonneg_right (le_abs_self x) hmesh.le
  have hylo : -(|y| / mesh) ≤ y / mesh := by
    simpa only [neg_div] using
      div_le_div_of_nonneg_right (neg_abs_le y) hmesh.le
  have hyhi : y / mesh ≤ |y| / mesh := by
    exact div_le_div_of_nonneg_right (le_abs_self y) hmesh.le
  have hqxlo : x / mesh - 1 / 2 < (qx : Real) + 1 := by
    exact_mod_cast Int.lt_floor_add_one (x / mesh - 1 / 2)
  have hqxhi : (qx : Real) ≤ x / mesh - 1 / 2 := by
    exact_mod_cast Int.floor_le (x / mesh - 1 / 2)
  have hqylo : y / mesh < (qy : Real) + 1 := by
    exact_mod_cast Int.lt_floor_add_one (y / mesh)
  have hqyhi : (qy : Real) ≤ y / mesh := by
    exact_mod_cast Int.floor_le (y / mesh)
  have hminusLower : 0 ≤ (n : Int) + qx - qy := by
    have hreal : 0 < (n : Real) + (qx : Real) - (qy : Real) := by
      nlinarith
    exact_mod_cast hreal.le
  have hplusLower : 0 ≤ (n : Int) + qx + qy := by
    have hreal : 0 < (n : Real) + (qx : Real) + (qy : Real) := by
      nlinarith
    exact_mod_cast hreal.le
  have hminusUpper : qx - qy + 1 < (n : Int) := by
    have hreal : (qx : Real) - (qy : Real) + 1 < (n : Real) := by
      nlinarith
    exact_mod_cast hreal
  have hplusUpper : qx + qy + 1 < (n : Int) := by
    have hreal : (qx : Real) + (qy : Real) + 1 < (n : Real) := by
      nlinarith
    exact_mod_cast hreal
  simpa [qx, qy] using
    And.intro hminusLower
      (And.intro hplusLower (And.intro hminusUpper hplusUpper))



theorem isingReflectedCenteredRadialGridPosition_snap
    (n : Nat) (mesh : Real) (z : Complex)
    (hi : 0 ≤ (n : Int) + ⌊z.re / mesh - 1 / 2⌋ - ⌊z.im / mesh⌋)
    (hj : 0 ≤ (n : Int) + ⌊z.re / mesh - 1 / 2⌋ + ⌊z.im / mesh⌋) :
    isingReflectedCenteredRadialGridPosition mesh n
        (reflectedRadialAxisSnapI n mesh z)
        (reflectedRadialAxisSnapJ n mesh z) =
      reflectedRadialAxisSnap mesh z := by
  let qx : Int := ⌊z.re / mesh - 1 / 2⌋
  let qy : Int := ⌊z.im / mesh⌋
  let ii : Int := (n : Int) + qx - qy
  let jj : Int := (n : Int) + qx + qy
  have hii : (ii.toNat : Int) = ii := Int.toNat_of_nonneg (by simpa [ii, qx, qy] using hi)
  have hjj : (jj.toNat : Int) = jj := Int.toNat_of_nonneg (by simpa [jj, qx, qy] using hj)
  have hiiR : (ii.toNat : Real) = (n : Real) + (qx : Real) - (qy : Real) := by
    exact_mod_cast hii
  have hjjR : (jj.toNat : Real) = (n : Real) + (qx : Real) + (qy : Real) := by
    exact_mod_cast hjj
  rw [isingReflectedCenteredRadialGridPosition_eq]
  unfold reflectedRadialAxisSnap shiftedRealGridFloor
  rw [show reflectedRadialAxisSnapI n mesh z = ii.toNat by rfl,
    show reflectedRadialAxisSnapJ n mesh z = jj.toNat by rfl]
  simp only [sub_zero]
  change
    (mesh * (((ii.toNat : Real) + (jj.toNat : Real) + 1) / 2 - n) : Real) +
        (mesh * (((jj.toNat : Real) - (ii.toNat : Real)) / 2) : Real) *
          Complex.I =
      (mesh * ((qx : Real) + 1 / 2) : Real) +
        (mesh * ((qy : Real) + 0) : Real) * Complex.I
  rw [hiiR, hjjR]
  ring



theorem isingReflectedCenteredRadialGridPosition_axisSnapBase
    (n : Nat) (mesh : Real) (z w : Complex)
    (hmesh : 0 < mesh) (him : z.im ≤ w.im)
    (hi0 : 0 ≤ (n : Int) + ⌊z.re / mesh - 1 / 2⌋ - ⌊w.im / mesh⌋)
    (hj0 : 0 ≤ (n : Int) + ⌊z.re / mesh - 1 / 2⌋ + ⌊z.im / mesh⌋) :
    isingReflectedCenteredRadialGridPosition mesh n
        (reflectedRadialAxisSnapBaseI n mesh z w +
          reflectedRadialAxisSnapHeight mesh z w)
        (reflectedRadialAxisSnapBaseJ n mesh z) =
      reflectedRadialAxisSnap mesh z := by
  let qx : Int := ⌊z.re / mesh - 1 / 2⌋
  let qyz : Int := ⌊z.im / mesh⌋
  let qyw : Int := ⌊w.im / mesh⌋
  have hqy : qyz ≤ qyw := by
    apply Int.floor_mono
    exact div_le_div_of_nonneg_right him hmesh.le
  have hdiff : 0 ≤ qyw - qyz := sub_nonneg.mpr hqy
  have hsum0 : 0 ≤ (n : Int) + qx - qyz := by
    have hbase : 0 ≤ (n : Int) + qx - qyw := by
      simpa [qx, qyw] using hi0
    omega
  have hIndex :
      reflectedRadialAxisSnapBaseI n mesh z w +
          reflectedRadialAxisSnapHeight mesh z w =
        reflectedRadialAxisSnapI n mesh z := by
    have hInt :
        (reflectedRadialAxisSnapBaseI n mesh z w : Int) +
            (reflectedRadialAxisSnapHeight mesh z w : Int) =
          (reflectedRadialAxisSnapI n mesh z : Int) := by
      rw [show (reflectedRadialAxisSnapBaseI n mesh z w : Int) =
          (n : Int) + qx - qyw by
        exact Int.toNat_of_nonneg (by simpa [qx, qyw] using hi0),
        show (reflectedRadialAxisSnapHeight mesh z w : Int) = qyw - qyz by
          simpa [reflectedRadialAxisSnapHeight, shiftedRealGridFloorSteps,
            qyw, qyz] using Int.toNat_of_nonneg hdiff,
        show (reflectedRadialAxisSnapI n mesh z : Int) =
            (n : Int) + qx - qyz by
          exact Int.toNat_of_nonneg hsum0]
      ring
    exact_mod_cast hInt
  rw [hIndex]
  apply isingReflectedCenteredRadialGridPosition_snap
  · simpa [qx, qyz] using hsum0
  · simpa [reflectedRadialAxisSnapBaseJ] using hj0




theorem fkIsingExpandingSquare_eventually_axisSnap_interior
    (z w : Complex) (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    ∀ᶠ k in atTop,
      0 ≤ (fkIsingExpandingSquareSide k : Int) +
          ⌊z.re / fkIsingExpandingSquareScale k - 1 / 2⌋ -
          ⌊w.im / fkIsingExpandingSquareScale k⌋ ∧
      0 ≤ (fkIsingExpandingSquareSide k : Int) +
          ⌊z.re / fkIsingExpandingSquareScale k - 1 / 2⌋ +
          ⌊z.im / fkIsingExpandingSquareScale k⌋ ∧
      reflectedRadialAxisSnapBaseI
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareScale k) z w +
          reflectedRadialAxisSnapWidth
            (fkIsingExpandingSquareScale k) z w +
          reflectedRadialAxisSnapHeight
            (fkIsingExpandingSquareScale k) z w + 1 <
        2 * fkIsingExpandingSquareSide k ∧
      reflectedRadialAxisSnapBaseJ
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareScale k) z +
          reflectedRadialAxisSnapWidth
            (fkIsingExpandingSquareScale k) z w +
          reflectedRadialAxisSnapHeight
            (fkIsingExpandingSquareScale k) z w + 1 <
        2 * fkIsingExpandingSquareSide k := by
  filter_upwards
    [fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior
      (|z.re| + |w.im|) 3,
    fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior
      (|z.re| + |z.im|) 3,
    fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior
      (|w.re| + |z.im|) 3,
    fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior
      (|w.re| + |w.im|) 3] with k hzw hzz hwz hww
  let n := fkIsingExpandingSquareSide k
  let mesh := fkIsingExpandingSquareScale k
  let qxz : Int := ⌊z.re / mesh - 1 / 2⌋
  let qxw : Int := ⌊w.re / mesh - 1 / 2⌋
  let qyz : Int := ⌊z.im / mesh⌋
  let qyw : Int := ⌊w.im / mesh⌋
  have hmesh : 0 < mesh := fkIsingExpandingSquareScale_pos k
  have hzw' : |z.re| + |w.im| + 3 * mesh ≤ mesh * n := by
    dsimp only [mesh, n]
    nlinarith
  have hzz' : |z.re| + |z.im| + 3 * mesh ≤ mesh * n := by
    dsimp only [mesh, n]
    nlinarith
  have hwz' : |w.re| + |z.im| + 3 * mesh ≤ mesh * n := by
    dsimp only [mesh, n]
    nlinarith
  have hww' : |w.re| + |w.im| + 3 * mesh ≤ mesh * n := by
    dsimp only [mesh, n]
    nlinarith
  have hboxZW := reflectedRadialAxisFloor_box n mesh z.re w.im hmesh hzw'
  have hboxZZ := reflectedRadialAxisFloor_box n mesh z.re z.im hmesh hzz'
  have hboxWZ := reflectedRadialAxisFloor_box n mesh w.re z.im hmesh hwz'
  have hboxWW := reflectedRadialAxisFloor_box n mesh w.re w.im hmesh hww'
  have hqx : qxz ≤ qxw := by
    apply Int.floor_mono
    exact sub_le_sub_right (div_le_div_of_nonneg_right hre hmesh.le) (1 / 2)
  have hqy : qyz ≤ qyw := by
    apply Int.floor_mono
    exact div_le_div_of_nonneg_right him hmesh.le
  have hi0 : 0 ≤ (n : Int) + qxz - qyw := by
    simpa [qxz, qyw] using hboxZW.1
  have hj0 : 0 ≤ (n : Int) + qxz + qyz := by
    simpa [qxz, qyz] using hboxZZ.2.1
  have hiUpper : qxw - qyz + 1 < (n : Int) := by
    simpa [qxw, qyz] using hboxWZ.2.2.1
  have hjUpper : qxw + qyw + 1 < (n : Int) := by
    simpa [qxw, qyw] using hboxWW.2.2.2
  have hbaseI :
      (reflectedRadialAxisSnapBaseI n mesh z w : Int) =
        (n : Int) + qxz - qyw := by
    exact Int.toNat_of_nonneg (by simpa [qxz, qyw] using hi0)
  have hbaseJ :
      (reflectedRadialAxisSnapBaseJ n mesh z : Int) =
        (n : Int) + qxz + qyz := by
    exact Int.toNat_of_nonneg (by simpa [qxz, qyz] using hj0)
  have hwidth :
      (reflectedRadialAxisSnapWidth mesh z w : Int) = qxw - qxz := by
    simpa [reflectedRadialAxisSnapWidth, shiftedRealGridFloorSteps,
      qxw, qxz] using Int.toNat_of_nonneg (sub_nonneg.mpr hqx)
  have hheight :
      (reflectedRadialAxisSnapHeight mesh z w : Int) = qyw - qyz := by
    simpa [reflectedRadialAxisSnapHeight, shiftedRealGridFloorSteps,
      qyw, qyz] using Int.toNat_of_nonneg (sub_nonneg.mpr hqy)
  have hiNat :
      reflectedRadialAxisSnapBaseI n mesh z w +
          reflectedRadialAxisSnapWidth mesh z w +
          reflectedRadialAxisSnapHeight mesh z w + 1 < 2 * n := by
    have hiInt :
        (reflectedRadialAxisSnapBaseI n mesh z w : Int) +
            (reflectedRadialAxisSnapWidth mesh z w : Int) +
            (reflectedRadialAxisSnapHeight mesh z w : Int) + 1 <
          2 * (n : Int) := by
      rw [hbaseI, hwidth, hheight]
      omega
    exact_mod_cast hiInt
  have hjNat :
      reflectedRadialAxisSnapBaseJ n mesh z +
          reflectedRadialAxisSnapWidth mesh z w +
          reflectedRadialAxisSnapHeight mesh z w + 1 < 2 * n := by
    have hjInt :
        (reflectedRadialAxisSnapBaseJ n mesh z : Int) +
            (reflectedRadialAxisSnapWidth mesh z w : Int) +
            (reflectedRadialAxisSnapHeight mesh z w : Int) + 1 <
          2 * (n : Int) := by
      rw [hbaseJ, hwidth, hheight]
      omega
    exact_mod_cast hjInt
  simpa [n, mesh, qxz, qyz] using
    And.intro hi0 (And.intro hj0 (And.intro hiNat hjNat))

theorem fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_continuous
    (k : Nat) :
    Continuous (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k) :=
  fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_continuous
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareMesh k)



theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral
    (n i j : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n) :
    complexDisplacementIntegral
        (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
          n hn gridScale normalizationScale)
        (isingReflectedCenteredRadialGridPosition gridScale n i j)
        ((gridScale : Complex) / 2 * (1 - Complex.I)) =
      ((fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
            ⟨i, by omega⟩ ⟨j, by omega⟩ /
          (Real.sqrt (2 * normalizationScale) : Complex) +
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
            ⟨i + 1, by omega⟩ ⟨j, by omega⟩ /
          (Real.sqrt (2 * normalizationScale) : Complex)) / 2) *
        ((gridScale : Complex) / 2 * (1 - Complex.I)) := by
  apply complexDisplacementIntegral_eq_average_mul
  intro t ht
  have hpoint :
      isingReflectedCenteredRadialGridPosition gridScale n i j +
          (t : Complex) * ((gridScale : Complex) / 2 * (1 - Complex.I)) =
        isingReflectedCenteredRadialGridCellPoint
          gridScale n i j t 0 := by
    rw [isingReflectedCenteredRadialGridCellPoint_eq]
    simp
  rw [hpoint]
  rw [show isingReflectedCenteredRadialGridCellPoint
      gridScale n i j t 0 =
        (starRingEnd Complex)
          (isingCenteredRadialGridCellPoint gridScale n i j t 0) by rfl]
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_cellPoint
    n i j hn gridScale normalizationScale hgridScale hi hj
    t 0 ht.1 ht.2 (le_refl 0) zero_le_one]
  simp [complexBilinearCell]



theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral
    (n i j : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n) :
    complexDisplacementIntegral
        (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
          n hn gridScale normalizationScale)
        (isingReflectedCenteredRadialGridPosition gridScale n i j)
        ((gridScale : Complex) / 2 * (1 + Complex.I)) =
      ((fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
            ⟨i, by omega⟩ ⟨j, by omega⟩ /
          (Real.sqrt (2 * normalizationScale) : Complex) +
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
            ⟨i, by omega⟩ ⟨j + 1, by omega⟩ /
          (Real.sqrt (2 * normalizationScale) : Complex)) / 2) *
        ((gridScale : Complex) / 2 * (1 + Complex.I)) := by
  apply complexDisplacementIntegral_eq_average_mul
  intro t ht
  have hpoint :
      isingReflectedCenteredRadialGridPosition gridScale n i j +
          (t : Complex) * ((gridScale : Complex) / 2 * (1 + Complex.I)) =
        isingReflectedCenteredRadialGridCellPoint
          gridScale n i j 0 t := by
    rw [isingReflectedCenteredRadialGridCellPoint_eq]
    simp
  rw [hpoint]
  rw [show isingReflectedCenteredRadialGridCellPoint
      gridScale n i j 0 t =
        (starRingEnd Complex)
          (isingCenteredRadialGridCellPoint gridScale n i j 0 t) by rfl]
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_cellPoint
    n i j hn gridScale normalizationScale hgridScale hi hj
    0 t (le_refl 0) zero_le_one ht.1 ht.2]
  simp [complexBilinearCell]



theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral_eq_edge
    (n i j : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n) :
    complexDisplacementIntegral
        (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
          n hn gridScale normalizationScale)
        (isingReflectedCenteredRadialGridPosition gridScale n i j)
        ((gridScale : Complex) / 2 * (1 - Complex.I)) =
      reflectedRadialHorizontalEdgeIntegral gridScale
        (fun a b =>
          fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
              n hn a b /
            (Real.sqrt (2 * normalizationScale) : Complex)) i j := by
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral
    n i j hn gridScale normalizationScale hgridScale hi hj]
  unfold reflectedRadialHorizontalEdgeIntegral
  dsimp only
  rw [fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_apply
      n hn i j (by omega) (by omega),
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_apply
      n hn (i + 1) j hi (by omega)]
  ring



theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral_eq_edge
    (n i j : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n) :
    complexDisplacementIntegral
        (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
          n hn gridScale normalizationScale)
        (isingReflectedCenteredRadialGridPosition gridScale n i j)
        ((gridScale : Complex) / 2 * (1 + Complex.I)) =
      reflectedRadialVerticalEdgeIntegral gridScale
        (fun a b =>
          fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
              n hn a b /
            (Real.sqrt (2 * normalizationScale) : Complex)) i j := by
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral
    n i j hn gridScale normalizationScale hgridScale hi hj]
  unfold reflectedRadialVerticalEdgeIntegral
  dsimp only
  rw [fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_apply
      n hn i j (by omega) (by omega),
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_apply
      n hn i (j + 1) (by omega) hj]
  ring



theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negIEdgeIntegral_eq_edge
    (n i j : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n) :
    complexDisplacementIntegral
        (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
          n hn gridScale normalizationScale)
        (isingReflectedCenteredRadialGridPosition gridScale n (i + 1) j)
        (-((gridScale : Complex) / 2 * (1 - Complex.I))) =
      -reflectedRadialHorizontalEdgeIntegral gridScale
        (fun a b =>
          fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
              n hn a b /
            (Real.sqrt (2 * normalizationScale) : Complex)) i j := by
  rw [isingReflectedCenteredRadialGridPosition_succ_i,
    complexDisplacementIntegral_reverse]
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral_eq_edge
    n i j hn gridScale normalizationScale hgridScale hi hj]



theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negJEdgeIntegral_eq_edge
    (n i j : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n) :
    complexDisplacementIntegral
        (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
          n hn gridScale normalizationScale)
        (isingReflectedCenteredRadialGridPosition gridScale n i (j + 1))
        (-((gridScale : Complex) / 2 * (1 + Complex.I))) =
      -reflectedRadialVerticalEdgeIntegral gridScale
        (fun a b =>
          fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
              n hn a b /
            (Real.sqrt (2 * normalizationScale) : Complex)) i j := by
  rw [isingReflectedCenteredRadialGridPosition_succ_j,
    complexDisplacementIntegral_reverse]
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral_eq_edge
    n i j hn gridScale normalizationScale hgridScale hi hj]




theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedAxisStaircasePathIntegral_eq_boundary
    (n i0 j0 width height : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i0 + width + height + 1 < 2 * n)
    (hj : j0 + width + height + 1 < 2 * n) :
    reflectedRadialAxisStaircasePathIntegral
        (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
          n hn gridScale normalizationScale)
        gridScale n i0 j0 width height =
      reflectedRadialAxisStaircaseBoundaryIntegral gridScale
        (fun i j =>
          fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
              n hn i j /
            (Real.sqrt (2 * normalizationScale) : Complex))
        i0 j0 width height := by
  let f :=
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
      n hn gridScale normalizationScale
  let F : Nat -> Nat -> Complex := fun i j =>
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn i j /
      (Real.sqrt (2 * normalizationScale) : Complex)
  let u : Complex := (gridScale : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (gridScale : Complex) / 2 * (1 + Complex.I)
  have hbottom :
      (∑ k ∈ Finset.range width,
        (complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition
              gridScale n (i0 + height + k) (j0 + k)) u +
          complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition
              gridScale n (i0 + height + k + 1) (j0 + k)) v)) =
      ∑ k ∈ Finset.range width,
        (reflectedRadialHorizontalEdgeIntegral gridScale F
            (i0 + height + k) (j0 + k) +
          reflectedRadialVerticalEdgeIntegral gridScale F
            (i0 + height + k + 1) (j0 + k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    dsimp only [f, F, u, v]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral_eq_edge
      n (i0 + height + k) (j0 + k) hn gridScale normalizationScale
      hgridScale (by omega) (by omega)]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral_eq_edge
      n (i0 + height + k + 1) (j0 + k) hn gridScale normalizationScale
      hgridScale (by omega) (by omega)]
  have hright :
      (∑ k ∈ Finset.range height,
        (complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + width + (height - 1 - k) + 1) (j0 + width + k)) v +
          complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + width + (height - 1 - k) + 1)
              (j0 + width + k + 1)) (-u))) =
      ∑ k ∈ Finset.range height,
        (reflectedRadialVerticalEdgeIntegral gridScale F
            (i0 + width + (height - 1 - k) + 1) (j0 + width + k) -
          reflectedRadialHorizontalEdgeIntegral gridScale F
            (i0 + width + (height - 1 - k)) (j0 + width + k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    dsimp only [f, F, u, v]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral_eq_edge
      n (i0 + width + (height - 1 - k) + 1) (j0 + width + k)
      hn gridScale normalizationScale hgridScale (by omega) (by omega)]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negIEdgeIntegral_eq_edge
      n (i0 + width + (height - 1 - k)) (j0 + width + k + 1)
      hn gridScale normalizationScale hgridScale (by omega) (by omega)]
    ring
  have htop :
      (∑ k ∈ Finset.range width,
        (complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + (width - 1 - k) + 1)
              (j0 + height + (width - 1 - k) + 1)) (-u) +
          complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + (width - 1 - k))
              (j0 + height + (width - 1 - k) + 1)) (-v))) =
      ∑ k ∈ Finset.range width,
        (-reflectedRadialHorizontalEdgeIntegral gridScale F
            (i0 + (width - 1 - k))
            (j0 + height + (width - 1 - k) + 1) -
          reflectedRadialVerticalEdgeIntegral gridScale F
            (i0 + (width - 1 - k))
            (j0 + height + (width - 1 - k))) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    dsimp only [f, F, u, v]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negIEdgeIntegral_eq_edge
      n (i0 + (width - 1 - k))
      (j0 + height + (width - 1 - k) + 1)
      hn gridScale normalizationScale hgridScale (by omega) (by omega)]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negJEdgeIntegral_eq_edge
      n (i0 + (width - 1 - k))
      (j0 + height + (width - 1 - k))
      hn gridScale normalizationScale hgridScale (by omega) (by omega)]
    ring
  have hleft :
      (∑ k ∈ Finset.range height,
        (complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + k) (j0 + (height - 1 - k) + 1)) (-v) +
          complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + k) (j0 + (height - 1 - k))) u)) =
      ∑ k ∈ Finset.range height,
        (-reflectedRadialVerticalEdgeIntegral gridScale F
            (i0 + k) (j0 + (height - 1 - k)) +
          reflectedRadialHorizontalEdgeIntegral gridScale F
            (i0 + k) (j0 + (height - 1 - k))) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    dsimp only [f, F, u, v]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negJEdgeIntegral_eq_edge
      n (i0 + k) (j0 + (height - 1 - k))
      hn gridScale normalizationScale hgridScale (by omega) (by omega)]
    rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral_eq_edge
      n (i0 + k) (j0 + (height - 1 - k))
      hn gridScale normalizationScale hgridScale (by omega) (by omega)]
  unfold reflectedRadialAxisStaircasePathIntegral
    reflectedRadialAxisStaircaseBoundaryIntegral
  dsimp only
  change
    (∑ k ∈ Finset.range width,
      (complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition
            gridScale n (i0 + height + k) (j0 + k)) u +
        complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition
            gridScale n (i0 + height + k + 1) (j0 + k)) v)) +
      (∑ k ∈ Finset.range height,
        (complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + width + (height - 1 - k) + 1) (j0 + width + k)) v +
          complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + width + (height - 1 - k) + 1)
              (j0 + width + k + 1)) (-u))) +
      (∑ k ∈ Finset.range width,
        (complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + (width - 1 - k) + 1)
              (j0 + height + (width - 1 - k) + 1)) (-u) +
          complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + (width - 1 - k))
              (j0 + height + (width - 1 - k) + 1)) (-v))) +
      (∑ k ∈ Finset.range height,
        (complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + k) (j0 + (height - 1 - k) + 1)) (-v) +
          complexDisplacementIntegral f
            (isingReflectedCenteredRadialGridPosition gridScale n
              (i0 + k) (j0 + (height - 1 - k))) u)) = _
  rw [hbottom, hright, htop, hleft]



theorem
    fkIsingExpandingBoundarySquareCenteredReflectedRegionContour_eq_zero
    (k : Nat) (cells : Finset (Nat × Nat))
    (hinterior : forall p, p ∈ cells ->
      p.1 + 2 < 2 * fkIsingExpandingSquareSide k ∧
      p.2 + 2 < 2 * fkIsingExpandingSquareSide k) :
    reflectedRadialCellRegionBoundaryIntegral
      (fkIsingExpandingSquareScale k)
      (fun i j =>
        fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k) i j /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex))
      cells = 0 := by
  exact
    fkIsingSquareBoundaryCenteredRadialPatchNormalizedExtension_reflectedRegionContour_eq_zero
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareMesh k)
      cells hinterior




theorem
    fkIsingExpandingBoundarySquareCenteredReflectedAxisStaircaseContour_eq_zero
    (k i0 j0 width height : Nat)
    (hi : i0 + width + height + 1 <
      2 * fkIsingExpandingSquareSide k)
    (hj : j0 + width + height + 1 <
      2 * fkIsingExpandingSquareSide k) :
    reflectedRadialAxisStaircaseBoundaryIntegral
      (fkIsingExpandingSquareScale k)
      (fun i j =>
        fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k) i j /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex))
      i0 j0 width height = 0 := by
  apply reflectedRadialAxisStaircaseBoundaryIntegral_eq_zero_of_cellCR
  intro a b ha hb
  apply IsingCellCRAt.div_const
  apply fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
  · omega
  · omega



theorem
    fkIsingExpandingBoundarySquareCenteredReflectedAxisStaircasePathIntegral_eq_zero
    (k i0 j0 width height : Nat)
    (hi : i0 + width + height + 1 <
      2 * fkIsingExpandingSquareSide k)
    (hj : j0 + width + height + 1 <
      2 * fkIsingExpandingSquareSide k) :
    reflectedRadialAxisStaircasePathIntegral
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k)
      i0 j0 width height = 0 := by
  unfold fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
  rw [fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedAxisStaircasePathIntegral_eq_boundary
    (fkIsingExpandingSquareSide k) i0 j0 width height
    (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareMesh k)
    (fkIsingExpandingSquareScale_pos k).ne' hi hj]
  exact
    fkIsingExpandingBoundarySquareCenteredReflectedAxisStaircaseContour_eq_zero
      k i0 j0 width height hi hj



theorem
    fkIsingExpandingBoundarySquare_eventually_axisSnapStaircasePathIntegral_eq_zero
    (z w : Complex) (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    ∀ᶠ k in atTop,
      reflectedRadialAxisStaircasePathIntegral
          (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k)
          (fkIsingExpandingSquareScale k)
          (fkIsingExpandingSquareSide k)
          (reflectedRadialAxisSnapBaseI
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareScale k) z w)
          (reflectedRadialAxisSnapBaseJ
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareScale k) z)
          (reflectedRadialAxisSnapWidth
            (fkIsingExpandingSquareScale k) z w)
          (reflectedRadialAxisSnapHeight
            (fkIsingExpandingSquareScale k) z w) = 0 := by
  filter_upwards
    [fkIsingExpandingSquare_eventually_axisSnap_interior z w hre him]
      with k hk
  exact
    fkIsingExpandingBoundarySquareCenteredReflectedAxisStaircasePathIntegral_eq_zero
      k
      (reflectedRadialAxisSnapBaseI
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareScale k) z w)
      (reflectedRadialAxisSnapBaseJ
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareScale k) z)
      (reflectedRadialAxisSnapWidth
        (fkIsingExpandingSquareScale k) z w)
      (reflectedRadialAxisSnapHeight
        (fkIsingExpandingSquareScale k) z w)
      hk.2.2.1 hk.2.2.2



theorem fkIsingExpandingBoundarySquareCenteredReflectedCellPathIntegral_eq_zero
    (k i j : Nat)
    (hi : i + 2 < 2 * fkIsingExpandingSquareSide k)
    (hj : j + 2 < 2 * fkIsingExpandingSquareSide k) :
    reflectedRadialBilinearCellPathIntegral
      (fkIsingExpandingSquareScale k)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          (fkIsingExpandingSquareSide k)
          (fkIsingExpandingSquareSide_pos k) i j /
        (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex))
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          (fkIsingExpandingSquareSide k)
          (fkIsingExpandingSquareSide_pos k) (i + 1) j /
        (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex))
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          (fkIsingExpandingSquareSide k)
          (fkIsingExpandingSquareSide_pos k) i (j + 1) /
        (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex))
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          (fkIsingExpandingSquareSide k)
          (fkIsingExpandingSquareSide_pos k) (i + 1) (j + 1) /
        (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) = 0 := by
  exact
    fkIsingSquareBoundaryCenteredRadialPatch_reflectedCellPathIntegral_eq_zero
      (fkIsingExpandingSquareSide k) i j
      (fkIsingExpandingSquareSide_pos k) hi hj
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareMesh k)

theorem reflectedRadialBilinearCellContour_eq_zero_of_IsingCellCRAt
    (mesh : Real) (F : Nat -> Nat -> Complex) (i j : Nat)
    (hCR : IsingCellCRAt F i j) :
    reflectedRadialBilinearCellContour mesh
      (F i j) (F (i + 1) j) (F i (j + 1)) (F (i + 1) (j + 1)) = 0 := by
  exact reflectedRadialBilinearCellContour_eq_zero_of_cellCR mesh _ _ _ _ hCR

namespace FKIsingCaratheodoryApproximation


abbrev BoundaryRadialTensorTentGeometry.VanishingRectangleContourError
    (A : FKIsingCaratheodoryApproximation)
    (G : BoundaryRadialTensorTentGeometry A) :=
  StatMech.Universality.VanishingRectangleContourError
    (BoundaryRadialTensorTentGeometry.interpolant A G)



abbrev BoundaryRadialTensorTentGeometry.ReflectedVanishingRectangleContourError
    (A : FKIsingCaratheodoryApproximation)
    (G : BoundaryRadialTensorTentGeometry A) :=
  StatMech.Universality.VanishingRectangleContourError
    (BoundaryRadialTensorTentGeometry.reflectedInterpolant A G)



theorem BoundaryRadialTensorTentGeometry.subsequentialMorera_of_contourError
    (A : FKIsingCaratheodoryApproximation)
    (hU : A.U = Set.univ)
    (G : BoundaryRadialTensorTentGeometry A)
    (H : BoundaryRadialTensorTentGeometry.VanishingRectangleContourError A G) :
    forall (phi psi : Nat -> Nat) (f : Complex -> Complex),
      StrictMono phi -> StrictMono psi ->
      TendstoLocallyUniformlyOn
        (fun n => BoundaryRadialTensorTentGeometry.interpolant A G
          (phi (psi n))) f atTop A.U ->
      Complex.IsConservativeOn f A.U := by
  intro phi psi f hphi hpsi hlimit
  rw [hU] at hlimit ⊢
  exact H.isConservativeOn_subsequentialLimit
    (BoundaryRadialTensorTentGeometry.interpolant_continuous A G)
    (hphi.comp hpsi).tendsto_atTop hlimit




theorem BoundaryRadialTensorTentGeometry.reflected_subsequentialMorera_of_contourError
    (A : FKIsingCaratheodoryApproximation)
    (hU : A.reflect.U = Set.univ)
    (G : BoundaryRadialTensorTentGeometry A)
    (H : BoundaryRadialTensorTentGeometry.ReflectedVanishingRectangleContourError
      A G) :
    forall (phi psi : Nat -> Nat) (f : Complex -> Complex),
      StrictMono phi -> StrictMono psi ->
      TendstoLocallyUniformlyOn
        (fun n => BoundaryRadialTensorTentGeometry.reflectedInterpolant A G
          (phi (psi n))) f atTop A.reflect.U ->
      Complex.IsConservativeOn f A.reflect.U := by
  intro phi psi f hphi hpsi hlimit
  rw [hU] at hlimit ⊢
  exact H.isConservativeOn_subsequentialLimit
    (BoundaryRadialTensorTentGeometry.reflectedInterpolant_continuous A G)
    (hphi.comp hpsi).tendsto_atTop hlimit

end FKIsingCaratheodoryApproximation

end

end StatMech.Universality
