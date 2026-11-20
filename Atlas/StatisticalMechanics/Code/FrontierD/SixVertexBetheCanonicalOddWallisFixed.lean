/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalOddWallis





namespace StatMech.FrontierD

open Filter Topology Finset MeasureTheory

noncomputable section

theorem abs_mul_cos_sub_sin_le_abs_cube_div_two
    {x : Real} (hx : |x| <= 1) :
    |x * Real.cos x - Real.sin x| <= |x| ^ 3 / 2 := by
  let u := |x|
  have hu0 : 0 <= u := abs_nonneg x
  have hu1 : u <= 1 := hx
  by_cases hx0 : x = 0
  · simp [hx0]
  have huPos : 0 < u := abs_pos.mpr hx0
  have hsinLower : u - u ^ 3 / 4 <= Real.sin u :=
    (Real.sin_gt_sub_cube huPos hu1).le
  have hsinUpper : Real.sin u <= u := Real.sin_le hu0
  have hcosLower : 1 - u ^ 2 / 2 <= Real.cos u :=
    Real.one_sub_sq_div_two_le_cos
  have hcosUpper : Real.cos u <= 1 := Real.cos_le_one u
  have hgUpper : u * Real.cos u - Real.sin u <= u ^ 3 / 2 := by
    nlinarith
  have hgLower : -(u ^ 3 / 2) <=
      u * Real.cos u - Real.sin u := by
    nlinarith
  have habs : |u * Real.cos u - Real.sin u| <= u ^ 3 / 2 :=
    (abs_le).2 ⟨hgLower, hgUpper⟩
  rcases le_total 0 x with hxPos | hxNeg
  · simpa [u, abs_of_nonneg hxPos] using habs
  · have habs' : |(-x) * Real.cos (-x) - Real.sin (-x)| <=
        (-x) ^ 3 / 2 := by
      simpa [u, abs_of_nonpos hxNeg] using habs
    calc
      |x * Real.cos x - Real.sin x| =
          |(-x) * Real.cos (-x) - Real.sin (-x)| := by
        rw [Real.cos_neg, Real.sin_neg]
        rw [show (-x) * Real.cos x - -Real.sin x =
          -(x * Real.cos x - Real.sin x) by ring, abs_neg]
      _ <= (-x) ^ 3 / 2 := habs'
      _ = |x| ^ 3 / 2 := by rw [abs_of_nonpos hxNeg]

theorem abs_sixVertexSincDerivative_le_abs_div_two
    {x : Real} (hx : |x| <= 1) :
    |sixVertexSincDerivative x| <= |x| / 2 := by
  by_cases hx0 : x = 0
  · simp [sixVertexSincDerivative, hx0]
  rw [sixVertexSincDerivative, if_neg hx0, abs_div, abs_pow]
  have hnum := abs_mul_cos_sub_sin_le_abs_cube_div_two hx
  have hxabs : 0 < |x| := abs_pos.mpr hx0
  calc
    |x * Real.cos x - Real.sin x| / |x| ^ 2 <=
        (|x| ^ 3 / 2) / |x| ^ 2 := by gcongr
    _ = |x| / 2 := by field_simp [hxabs.ne']

theorem continuousAt_sixVertexSincDerivative_zero :
    ContinuousAt sixVertexSincDerivative 0 := by
  rw [ContinuousAt, show sixVertexSincDerivative 0 = 0 by
    simp [sixVertexSincDerivative]]
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hdelta : 0 < min 1 (2 * epsilon) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : Real) hdelta] with x hx
  rw [Metric.mem_ball, Real.dist_eq] at hx
  simp only [sub_zero] at hx
  have hxOne : |x| <= 1 := (lt_min_iff.mp hx).1.le
  have hxEps : |x| / 2 < epsilon := by
    have := (lt_min_iff.mp hx).2
    linarith
  rw [Real.dist_eq, sub_zero]
  exact (abs_sixVertexSincDerivative_le_abs_div_two hxOne).trans_lt hxEps

theorem continuous_sixVertexSincDerivative :
    Continuous sixVertexSincDerivative := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · simpa [hx] using continuousAt_sixVertexSincDerivative_zero
  · have hquot : ContinuousAt
        (fun y : Real => (y * Real.cos y - Real.sin y) / y ^ 2) x := by
      exact ((continuousAt_id.mul Real.continuous_cos.continuousAt).sub
        Real.continuous_sin.continuousAt).div (continuousAt_id.pow 2)
          (pow_ne_zero 2 hx)
    apply hquot.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [sixVertexSincDerivative, hy]

def sixVertexBetheDesingularizedLogObservableDerivative
    (c x : Real) : Real :=
  -(c ^ 2 - 1) * Real.sin x /
      ((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x) -
    (1 / 2 : Real) *
      (sixVertexSincDerivative (x / 2) / Real.sinc (x / 2))

theorem hasDerivAt_sixVertexBetheDesingularizedLogObservable
    {c x : Real} (hc : 2 < c) (hx : x ∈ Set.Icc 0 Real.pi) :
    HasDerivAt (sixVertexBetheDesingularizedLogObservable c)
      (sixVertexBetheDesingularizedLogObservableDerivative c x) x := by
  let a := c ^ 2 - 1
  let A : Real -> Real := fun y => a ^ 2 + 1 + 2 * a * Real.cos y
  let S : Real -> Real := fun y => Real.sinc (y / 2)
  have hApos : 0 < A x := by
    have ha : 1 < a := by dsimp [a]; nlinarith
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x, sq_nonneg (a - 1)]
  have hSpos : 0 < S x := by
    rcases hx.1.eq_or_lt with rfl | hx0
    · simp [S]
    · have hhalf0 : x / 2 ≠ 0 := by positivity
      dsimp [S]
      rw [Real.sinc_of_ne_zero hhalf0]
      exact div_pos (Real.sin_pos_of_pos_of_lt_pi (by nlinarith)
        (by nlinarith [hx.2, Real.pi_pos])) (by linarith)
  have hAderiv : HasDerivAt A (-2 * a * Real.sin x) x := by
    dsimp [A]
    convert (Real.hasDerivAt_cos x).const_mul (2 * a) |>.const_add
      (a ^ 2 + 1) using 1 <;> ring
  have hSderiv : HasDerivAt S
      ((1 / 2 : Real) * sixVertexSincDerivative (x / 2)) x := by
    dsimp [S]
    convert (hasDerivAt_sinc (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2) using 1 <;> ring
  have hfirst := (hAderiv.log hApos.ne').const_mul (1 / 2 : Real)
  have hsecond := hSderiv.log hSpos.ne'
  unfold sixVertexBetheDesingularizedLogObservable
    sixVertexBetheDesingularizedLogObservableDerivative
  dsimp [a, A, S] at hfirst hsecond ⊢
  convert hfirst.sub hsecond using 1
  ring

theorem continuousOn_sixVertexBetheDesingularizedLogObservableDerivative
    {c : Real} (hc : 2 < c) :
    ContinuousOn (sixVertexBetheDesingularizedLogObservableDerivative c)
      (Set.Icc 0 Real.pi) := by
  let a := c ^ 2 - 1
  let A : Real -> Real := fun x => a ^ 2 + 1 + 2 * a * Real.cos x
  let S : Real -> Real := fun x => Real.sinc (x / 2)
  have hAcont : Continuous A := by
    dsimp [A]
    fun_prop
  have hScont : Continuous S :=
    Real.continuous_sinc.comp (continuous_id.div_const 2)
  have hDcont : Continuous (fun x : Real =>
      sixVertexSincDerivative (x / 2)) :=
    continuous_sixVertexSincDerivative.comp (continuous_id.div_const 2)
  have hApos (x : Real) : 0 < A x := by
    have ha : 1 < a := by dsimp [a]; nlinarith
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x, sq_nonneg (a - 1)]
  have hSpos (x : Real) (hx : x ∈ Set.Icc 0 Real.pi) : 0 < S x := by
    rcases hx.1.eq_or_lt with rfl | hx0
    · simp [S]
    · have hhalf0 : x / 2 ≠ 0 := by positivity
      dsimp [S]
      rw [Real.sinc_of_ne_zero hhalf0]
      exact div_pos (Real.sin_pos_of_pos_of_lt_pi (by nlinarith)
        (by nlinarith [hx.2, Real.pi_pos])) (by linarith)
  unfold sixVertexBetheDesingularizedLogObservableDerivative
  apply ContinuousOn.sub
  · exact ((continuous_const.mul Real.continuous_sin).div hAcont
      (fun x => (hApos x).ne')).continuousOn
  · exact continuous_const.continuousOn.mul
      (hDcont.continuousOn.div hScont.continuousOn
        (fun x hx => (hSpos x hx).ne'))

theorem abs_intervalIntegral_sub_const_mul_le_of_bound
    {f : Real -> Real} {a b z E : Real} (hab : a <= b)
    (hf : ContinuousOn f (Set.Icc a b)) (hE : 0 <= E)
    (hbound : ∀ x ∈ Set.Icc a b, |f x - z| <= E) :
    |(∫ x in a..b, f x) - (b - a) * z| <= E * (b - a) := by
  have hfint : IntervalIntegrable f volume a b :=
    hf.intervalIntegrable_of_Icc hab
  have hrewrite :
      (∫ x in a..b, f x) - (b - a) * z =
        ∫ x in a..b, (f x - z) := by
    rw [intervalIntegral.integral_sub hfint intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
  rw [hrewrite]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := E) (f := fun x => f x - z)
    (fun x hx => by
      rw [Set.uIoc_of_le hab] at hx
      rw [Real.norm_eq_abs]
      exact hbound x ⟨hx.1.le, hx.2⟩)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  exact h

theorem abs_two_halfIncrement_sub_fullIncrement_le
    {H D : Real -> Real} {a b E : Real} (hab : a <= b)
    (hH : ContinuousOn H (Set.Icc a b))
    (hD : ContinuousOn D (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt H (D x) x)
    (hE : 0 <= E)
    (hclose : ∀ x ∈ Set.Icc a b,
      |D x - D ((a + b) / 2)| <= E) :
    |2 * (H ((a + b) / 2) - H a) - (H b - H a)| <=
      E * (b - a) := by
  let m := (a + b) / 2
  have ham : a <= m := by dsimp [m]; linarith
  have hmb : m <= b := by dsimp [m]; linarith
  have hleftSub : Set.Icc a m ⊆ Set.Icc a b := fun x hx =>
    ⟨hx.1, hx.2.trans hmb⟩
  have hrightSub : Set.Icc m b ⊆ Set.Icc a b := fun x hx =>
    ⟨ham.trans hx.1, hx.2⟩
  have hleftInt : IntervalIntegrable D volume a m :=
    (hD.mono hleftSub).intervalIntegrable_of_Icc ham
  have hrightInt : IntervalIntegrable D volume m b :=
    (hD.mono hrightSub).intervalIntegrable_of_Icc hmb
  have hleftFTC : (∫ x in a..m, D x) = H m - H a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hderiv x (hleftSub (by simpa [Set.uIcc_of_le ham] using hx)))
      hleftInt
  have hrightFTC : (∫ x in m..b, D x) = H b - H m := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hderiv x (hrightSub (by simpa [Set.uIcc_of_le hmb] using hx)))
      hrightInt
  have hleftBound :
      |(∫ x in a..m, D x) - (m - a) * D m| <= E * (m - a) :=
    by
      simpa [m] using
        (abs_intervalIntegral_sub_const_mul_le_of_bound ham
          (hD.mono hleftSub) hE (fun x hx => hclose x (hleftSub hx)))
  have hrightBound :
      |(∫ x in m..b, D x) - (b - m) * D m| <= E * (b - m) :=
    by
      simpa [m] using
        (abs_intervalIntegral_sub_const_mul_le_of_bound hmb
          (hD.mono hrightSub) hE (fun x hx => hclose x (hrightSub hx)))
  have hhalf : m - a = b - m := by dsimp [m]; ring
  rw [hleftFTC] at hleftBound
  rw [hrightFTC] at hrightBound
  calc
    |2 * (H m - H a) - (H b - H a)| =
        |((H m - H a) - (m - a) * D m) -
          ((H b - H m) - (b - m) * D m)| := by
      rw [hhalf]
      congr 1
      ring
    _ <= |(H m - H a) - (m - a) * D m| +
        |(H b - H m) - (b - m) * D m| := abs_sub _ _
    _ <= E * (m - a) + E * (b - m) :=
      add_le_add hleftBound hrightBound
    _ = E * (b - a) := by ring

theorem abs_two_halfIncrementSum_sub_endpoint_le
    {H D : Real -> Real} {n : Nat} (a : Nat -> Real) {E : Real}
    (ha : ∀ j, j <= n -> a j ∈ Set.Icc 0 Real.pi)
    (hordered : ∀ j, j < n -> a j <= a (j + 1))
    (hH : ContinuousOn H (Set.Icc 0 Real.pi))
    (hD : ContinuousOn D (Set.Icc 0 Real.pi))
    (hderiv : ∀ x ∈ Set.Icc 0 Real.pi, HasDerivAt H (D x) x)
    (hE : 0 <= E)
    (hclose : ∀ j, j < n -> ∀ x ∈ Set.Icc (a j) (a (j + 1)),
      |D x - D ((a j + a (j + 1)) / 2)| <= E) :
    |2 * ∑ j : Fin n,
        (H ((a j.val + a (j.val + 1)) / 2) - H (a j.val)) -
        (H (a n) - H (a 0))| <= E * (a n - a 0) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : Nat => H ((a j + a (j + 1)) / 2) - H (a j)) n]
  have hcell (j : Nat) (hj : j < n) :
      |2 * (H ((a j + a (j + 1)) / 2) - H (a j)) -
          (H (a (j + 1)) - H (a j))| <=
        E * (a (j + 1) - a j) := by
    have hsub : Set.Icc (a j) (a (j + 1)) ⊆ Set.Icc 0 Real.pi :=
      fun x hx => ⟨(ha j hj.le).1.trans hx.1,
        hx.2.trans (ha (j + 1) (by omega)).2⟩
    exact abs_two_halfIncrement_sub_fullIncrement_le (hordered j hj)
      (hH.mono hsub) (hD.mono hsub)
      (fun x hx => hderiv x (hsub hx)) hE (hclose j hj)
  have htel :
      (∑ j ∈ Finset.range n, (H (a (j + 1)) - H (a j))) =
        H (a n) - H (a 0) := by
    have h := Finset.sum_range_sub' (fun j => H (a j)) n
    rw [Finset.sum_sub_distrib] at h ⊢
    linarith
  have hrewrite :
      2 * ∑ j ∈ Finset.range n,
          (H ((a j + a (j + 1)) / 2) - H (a j)) -
          (H (a n) - H (a 0)) =
        ∑ j ∈ Finset.range n,
          (2 * (H ((a j + a (j + 1)) / 2) - H (a j)) -
            (H (a (j + 1)) - H (a j))) := by
    rw [← htel, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hrewrite]
  calc
    |∑ j ∈ Finset.range n,
        (2 * (H ((a j + a (j + 1)) / 2) - H (a j)) -
          (H (a (j + 1)) - H (a j)))| <=
        ∑ j ∈ Finset.range n,
          |2 * (H ((a j + a (j + 1)) / 2) - H (a j)) -
            (H (a (j + 1)) - H (a j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ j ∈ Finset.range n, E * (a (j + 1) - a j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hcell j (Finset.mem_range.mp hj)
    _ = E * (a n - a 0) := by
      rw [← Finset.mul_sum]
      congr 1
      have h := Finset.sum_range_sub' a n
      rw [Finset.sum_sub_distrib] at h ⊢
      linarith

def sixVertexCanonicalOddHalfPartitionRoot
    {c : Real} (hc : 2 < c) (s k j : Nat) : Real :=
  if hj : j < s + k + 2 then
    sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k)
      ⟨j, by omega⟩
  else 0

@[simp] theorem sixVertexCanonicalOddHalfPartitionRoot_eq
    {c : Real} (hc : 2 < c) (s k j : Nat) (hj : j < s + k + 2) :
    sixVertexCanonicalOddHalfPartitionRoot hc s k j =
      sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k)
        ⟨j, by omega⟩ := by
  simp [sixVertexCanonicalOddHalfPartitionRoot, hj]

theorem sixVertexCanonicalOddHalfPartitionRoot_left
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) :
    sixVertexCanonicalOddHalfPartitionRoot hc s k j.val =
      sixVertexCanonicalOddLeftHalfRoot hc s k j := by
  unfold sixVertexCanonicalOddLeftHalfRoot
  rw [sixVertexCanonicalOddHalfPartitionRoot_eq hc s k j.val (by omega)]

theorem sixVertexCanonicalOddHalfPartitionRoot_right
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) :
    sixVertexCanonicalOddHalfPartitionRoot hc s k (j.val + 1) =
      sixVertexCanonicalOddRightHalfRoot hc s k j := by
  unfold sixVertexCanonicalOddRightHalfRoot
  rw [sixVertexCanonicalOddHalfPartitionRoot_eq hc s k (j.val + 1)
    (by omega)]

theorem sixVertexCanonicalOddHalfPartitionRoot_last
    {c : Real} (hc : 2 < c) (s k : Nat) :
    sixVertexCanonicalOddHalfPartitionRoot hc s k (s + k + 1) =
      sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1)) := by
  simp [sixVertexCanonicalOddBoundaryHalfRoot]

theorem sixVertexCanonicalOddFirstLeftHalfRoot_le_of_densityLower
    {c : Real} (hc : 2 < c) (s k : Nat) {lower : Real}
    (hlower : 0 < lower)
    (hdensity : ∀ x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x) :
    sixVertexCanonicalOddLeftHalfRoot hc s k
        (0 : Fin (s + k + 1)) <=
      1 / (2 * (sixVertexFourWidth (2 * s + 1) k : Real) * lower) := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  let rho := sixVertexFiniteRootDensity c N n p
  let a := sixVertexCanonicalOddLeftHalfRoot hc s k
    (0 : Fin (s + k + 1))
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have ha : 0 < a := by
    dsimp [a, sixVertexCanonicalOddLeftHalfRoot]
    exact (sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) (0 : Fin (2 * s + 1 + k + 1))).1
  have hpSymm : SixVertexRootSymmetric p :=
    (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
      (2 * s + 1 + k)).2.1
  have hint := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p 0 a
  have hzero := sixVertexBetheCountingFunction_zero_of_symmetric c N hpSymm
  have hroot := sixVertexCanonicalOddLeftHalfRoot_countingFunction hc s k
    (0 : Fin (s + k + 1))
  have hmass : (∫ x in (0 : Real)..a, rho x) = 1 / (2 * (N : Real)) := by
    rw [show (∫ x in (0 : Real)..a, rho x) =
        sixVertexBetheCountingFunction c N n p a -
          sixVertexBetheCountingFunction c N n p 0 by
      simpa [rho] using hint]
    rw [hzero]
    have hroot' : sixVertexBetheCountingFunction c N n p a =
        (1 / 2 : Real) / N := by simpa [N, n, p, a] using hroot
    rw [hroot']
    field_simp [hNreal.ne']
    ring
  have hmono := intervalIntegral.integral_mono_on ha.le
    (continuous_const.intervalIntegrable (μ := volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N n p).intervalIntegrable _ _)
    (fun x _ => by simpa [rho, N, n, p] using hdensity x)
  rw [intervalIntegral.integral_const, hmass] at hmono
  simp only [smul_eq_mul, sub_zero] at hmono
  dsimp [a, N] at hmono ⊢
  rw [show 1 / (2 * (sixVertexFourWidth (2 * s + 1) k : Real) * lower) =
      (1 / (2 * (sixVertexFourWidth (2 * s + 1) k : Real))) / lower by
    ring]
  exact (le_div_iff₀ hlower).2 hmono

theorem tendsto_sixVertexCanonicalOddFirstLeftHalfRoot
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k => sixVertexCanonicalOddLeftHalfRoot hc s k
      (0 : Fin (s + k + 1))) atTop (nhds 0) := by
  let lower := sixVertexCanonicalHalfDensityFloor hc
  have hlower : 0 < lower := sixVertexCanonicalHalfDensityFloor_pos hc
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s + 1) k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hden : Tendsto (fun k =>
      (2 * lower) * (sixVertexFourWidth (2 * s + 1) k : Real))
      atTop atTop := hwidth.const_mul_atTop (mul_pos (by norm_num) hlower)
  have hmajor : Tendsto (fun k =>
      1 / (2 * (sixVertexFourWidth (2 * s + 1) k : Real) * lower))
      atTop (nhds 0) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (tendsto_const_nhds.div_atTop hden :
        Tendsto (fun k => (1 : Real) /
          ((2 * lower) * (sixVertexFourWidth (2 * s + 1) k : Real)))
          atTop (nhds 0))
  have hshift : Tendsto (fun k : Nat => 2 * s + 1 + k) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by omega)).tendsto_atTop
  have hfloor := hshift.eventually
    (eventually_sixVertexCanonicalHalfDensityFloor_le hc)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) ?_ hmajor
  filter_upwards [hfloor] with k hk
  have hk' : ∀ x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x := by
    simpa [lower, sixVertexFourWidth] using hk
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos]
  · exact sixVertexCanonicalOddFirstLeftHalfRoot_le_of_densityLower
      hc s k hlower hk'
  · dsimp [sixVertexCanonicalOddLeftHalfRoot]
    exact (sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) (0 : Fin (2 * s + 1 + k + 1))).1

theorem tendsto_sixVertexCanonicalOddFixedHalfIncrementError
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k =>
      2 * ∑ j : Fin (s + k + 1),
        (sixVertexBetheDesingularizedLogObservable c
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
          sixVertexBetheDesingularizedLogObservable c
            (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
      (sixVertexBetheDesingularizedLogObservable c
          (sixVertexCanonicalOddBoundaryHalfRoot hc s k
            (0 : Fin (s + 1))) -
        sixVertexBetheDesingularizedLogObservable c
          (sixVertexCanonicalOddLeftHalfRoot hc s k
            (0 : Fin (s + k + 1))))) atTop (nhds 0) := by
  let H := sixVertexBetheDesingularizedLogObservable c
  let D := sixVertexBetheDesingularizedLogObservableDerivative c
  let lower := sixVertexCanonicalHalfDensityFloor hc
  have hlower : 0 < lower := sixVertexCanonicalHalfDensityFloor_pos hc
  have hH : ContinuousOn H (Set.Icc 0 Real.pi) :=
    continuousOn_sixVertexBetheDesingularizedLogObservable hc
  have hD : ContinuousOn D (Set.Icc 0 Real.pi) :=
    continuousOn_sixVertexBetheDesingularizedLogObservableDerivative hc
  have hderiv : ∀ x ∈ Set.Icc 0 Real.pi, HasDerivAt H (D x) x := by
    intro x hx
    exact hasDerivAt_sixVertexBetheDesingularizedLogObservable hc hx
  have huniform : UniformContinuousOn D (Set.Icc 0 Real.pi) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hD
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s + 1) k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hden := hwidth.atTop_mul_const hlower
  have hmesh : Tendsto (fun k =>
      1 / ((sixVertexFourWidth (2 * s + 1) k : Real) * lower))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
  have hshift : Tendsto (fun k : Nat => 2 * s + 1 + k) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by omega)).tendsto_atTop
  have hfloor := hshift.eventually
    (eventually_sixVertexCanonicalHalfDensityFloor_le hc)
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let E := epsilon / (Real.pi + 1)
  have hE : 0 < E := by dsimp [E]; positivity
  rcases Metric.uniformContinuousOn_iff.mp huniform E hE with
    ⟨delta, hdelta, hmod⟩
  have hmeshEventually : ∀ᶠ k : Nat in atTop,
      1 / ((sixVertexFourWidth (2 * s + 1) k : Real) * lower) < delta := by
    have hball := (Metric.tendsto_nhds.mp hmesh) delta hdelta
    filter_upwards [hball] with k hk
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (by positivity)] at hk
    exact hk
  filter_upwards [hfloor, hmeshEventually] with k hkFloor hkMesh
  let n := s + k + 1
  let a : Nat -> Real := sixVertexCanonicalOddHalfPartitionRoot hc s k
  have hkDensity : ∀ x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x := by
    simpa [lower, sixVertexFourWidth] using hkFloor
  have ha (j : Nat) (hj : j <= n) : a j ∈ Set.Icc 0 Real.pi := by
    have hjlt : j < s + k + 2 := by dsimp [n] at hj; omega
    rw [show a j =
        sixVertexCanonicalDensityPerronPositiveHalfRoots hc
          (2 * s + 1 + k) ⟨j, by omega⟩ by
      exact sixVertexCanonicalOddHalfPartitionRoot_eq hc s k j hjlt]
    have hmem := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨j, by omega⟩
    exact ⟨hmem.1.le, hmem.2.le⟩
  have hordered (j : Nat) (hj : j < n) : a j <= a (j + 1) := by
    let jf : Fin (s + k + 1) := ⟨j, by simpa [n] using hj⟩
    rw [show a j = sixVertexCanonicalOddLeftHalfRoot hc s k
        jf by
          dsimp [a, jf]
          exact sixVertexCanonicalOddHalfPartitionRoot_left hc s k jf]
    rw [show a (j + 1) = sixVertexCanonicalOddRightHalfRoot hc s k
        jf by
          dsimp [a, jf]
          exact sixVertexCanonicalOddHalfPartitionRoot_right hc s k jf]
    have horder := (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
      (2 * s + 1 + k)).1
    dsimp [sixVertexCanonicalOddLeftHalfRoot,
      sixVertexCanonicalOddRightHalfRoot,
      sixVertexCanonicalDensityPerronPositiveHalfRoots,
      sixVertexEvenPositiveHalfProjection]
    exact (horder (by simp [Fin.lt_def])).le
  have hclose (j : Nat) (hj : j < n) (x : Real)
      (hx : x ∈ Set.Icc (a j) (a (j + 1))) :
      |D x - D ((a j + a (j + 1)) / 2)| <= E := by
    let jf : Fin (s + k + 1) := ⟨j, by simpa [n] using hj⟩
    have hgap := sixVertexCanonicalOddHalfRoot_gap_le_of_densityLower
      hc s k hlower hkDensity jf
    have haj : a j = sixVertexCanonicalOddLeftHalfRoot hc s k jf := by
      dsimp [a]
      exact sixVertexCanonicalOddHalfPartitionRoot_left hc s k jf
    have haj1 : a (j + 1) = sixVertexCanonicalOddRightHalfRoot hc s k jf := by
      dsimp [a]
      exact sixVertexCanonicalOddHalfPartitionRoot_right hc s k jf
    have hxGlobal : x ∈ Set.Icc 0 Real.pi :=
      ⟨(ha j hj.le).1.trans hx.1, hx.2.trans (ha (j + 1) (by omega)).2⟩
    have hmidGlobal : (a j + a (j + 1)) / 2 ∈ Set.Icc 0 Real.pi := by
      have hjmem := ha j hj.le
      have hj1mem := ha (j + 1) (by omega)
      constructor <;> nlinarith [hjmem.1, hjmem.2, hj1mem.1, hj1mem.2]
    have hdist : dist x ((a j + a (j + 1)) / 2) < delta := by
      rw [Real.dist_eq]
      have hinside : |x - (a j + a (j + 1)) / 2| <= a (j + 1) - a j := by
        rw [abs_le]
        constructor <;> nlinarith [hx.1, hx.2]
      calc
        _ <= a (j + 1) - a j := hinside
        _ <= 1 / ((sixVertexFourWidth (2 * s + 1) k : Real) * lower) := by
          simpa [haj, haj1] using hgap
        _ < delta := hkMesh
    have := hmod x hxGlobal ((a j + a (j + 1)) / 2) hmidGlobal hdist
    simpa [Real.dist_eq] using this.le
  have hbound := abs_two_halfIncrementSum_sub_endpoint_le a ha hordered
    hH hD hderiv hE.le hclose
  have hlen : a n - a 0 <= Real.pi := by
    linarith [(ha n le_rfl).2, (ha 0 (by omega)).1]
  have hbound' :
      |2 * ∑ j : Fin (s + k + 1),
          (H (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
            H (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
        (H (sixVertexCanonicalOddBoundaryHalfRoot hc s k
            (0 : Fin (s + 1))) -
          H (sixVertexCanonicalOddLeftHalfRoot hc s k
            (0 : Fin (s + k + 1))))| <= E * (a n - a 0) := by
    simpa [n, a, sixVertexCanonicalOddMidpointHalfRoot,
      sixVertexCanonicalOddHalfPartitionRoot_left,
      sixVertexCanonicalOddHalfPartitionRoot_right,
      sixVertexCanonicalOddHalfPartitionRoot_last] using hbound
  rw [Real.dist_eq, sub_zero]
  change |2 * ∑ j : Fin (s + k + 1),
      (H (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
        H (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
      (H (sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1))) -
        H (sixVertexCanonicalOddLeftHalfRoot hc s k
          (0 : Fin (s + k + 1))))| < epsilon
  calc
    _ <= E * (a n - a 0) := hbound'
    _ <= E * Real.pi := mul_le_mul_of_nonneg_left hlen hE.le
    _ < epsilon := by
      dsimp [E]
      have hpi : 0 < Real.pi := Real.pi_pos
      calc
        epsilon / (Real.pi + 1) * Real.pi <
            epsilon / (Real.pi + 1) * (Real.pi + 1) := by
          exact mul_lt_mul_of_pos_left (by linarith)
            (div_pos hepsilon (by positivity))
        _ = epsilon := by field_simp

theorem tendsto_sixVertexCanonicalOddFixedHalfIncrement
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k =>
      2 * ∑ j : Fin (s + k + 1),
        (sixVertexBetheDesingularizedLogObservable c
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
          sixVertexBetheDesingularizedLogObservable c
            (sixVertexCanonicalOddLeftHalfRoot hc s k j))) atTop
      (nhds (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) +
        Real.log Real.pi - Real.log (c ^ 2))) := by
  let H := sixVertexBetheDesingularizedLogObservable c
  have hH : ContinuousOn H (Set.Icc 0 Real.pi) :=
    continuousOn_sixVertexBetheDesingularizedLogObservable hc
  let boundary : Nat -> Real := fun k =>
    sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1))
  let first : Nat -> Real := fun k =>
    sixVertexCanonicalOddLeftHalfRoot hc s k (0 : Fin (s + k + 1))
  have hboundaryRoot : Tendsto boundary atTop (nhds Real.pi) := by
    exact tendsto_sixVertexCanonicalOddBoundaryHalfRoot hc s
      (0 : Fin (s + 1))
  have hboundaryMem : ∀ᶠ k : Nat in atTop,
      boundary k ∈ Set.Icc 0 Real.pi := by
    apply Eventually.of_forall
    intro k
    dsimp [boundary, sixVertexCanonicalOddBoundaryHalfRoot]
    have hmem := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨s + k + 1, by omega⟩
    exact ⟨hmem.1.le, hmem.2.le⟩
  have hboundaryWithin : Tendsto boundary atTop
      (nhdsWithin Real.pi (Set.Icc 0 Real.pi)) := by
    rw [nhdsWithin]
    exact Filter.tendsto_inf.mpr
      ⟨hboundaryRoot, Filter.tendsto_principal.mpr hboundaryMem⟩
  have hboundaryH : Tendsto (fun k => H (boundary k)) atTop
      (nhds (H Real.pi)) := by
    have hHpi : Tendsto H (nhdsWithin Real.pi (Set.Icc 0 Real.pi))
        (nhds (H Real.pi)) := hH Real.pi ⟨Real.pi_pos.le, le_rfl⟩
    exact hHpi.comp hboundaryWithin
  have hfirstRoot : Tendsto first atTop (nhds 0) := by
    exact tendsto_sixVertexCanonicalOddFirstLeftHalfRoot hc s
  have hfirstMem : ∀ᶠ k : Nat in atTop,
      first k ∈ Set.Icc 0 Real.pi := by
    apply Eventually.of_forall
    intro k
    dsimp [first, sixVertexCanonicalOddLeftHalfRoot]
    have hmem := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) (0 : Fin (2 * s + 1 + k + 1))
    exact ⟨hmem.1.le, hmem.2.le⟩
  have hfirstWithin : Tendsto first atTop
      (nhdsWithin 0 (Set.Icc 0 Real.pi)) := by
    rw [nhdsWithin]
    exact Filter.tendsto_inf.mpr
      ⟨hfirstRoot, Filter.tendsto_principal.mpr hfirstMem⟩
  have hfirstH : Tendsto (fun k => H (first k)) atTop (nhds (H 0)) := by
    have hHzero : Tendsto H (nhdsWithin 0 (Set.Icc 0 Real.pi))
        (nhds (H 0)) := hH 0 ⟨le_rfl, Real.pi_pos.le⟩
    exact hHzero.comp hfirstWithin
  have herror := tendsto_sixVertexCanonicalOddFixedHalfIncrementError hc s
  have hcomb := herror.add (hboundaryH.sub hfirstH)
  have hpi := sixVertexBetheDesingularizedLogObservable_pi hc
  have hzero := sixVertexBetheDesingularizedLogObservable_zero hc
  convert hcomb using 1
  · funext k
    dsimp [boundary, first, H]
    ring
  · dsimp [H] at hpi hzero ⊢
    rw [hpi, hzero]
    ring

end

end StatMech.FrontierD
