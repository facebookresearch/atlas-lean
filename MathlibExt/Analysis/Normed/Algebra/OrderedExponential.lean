/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MathlibExt.Analysis.Normed.Algebra.ExponentialLimit

/-!
# Time-ordered products and the time-ordered exponential

For `Y : ℝ → 𝔸` in a real Banach algebra `𝔸` with `‖(1 : 𝔸)‖ = 1`, the grid product
`gridProd Y t M = ∏_{g < tM} (1 + M⁻¹ Y (g / M))` (factors ordered by increasing `g` from
left to right) is the Euler discretization of the ODE `U' = U Y`, `U 0 = 1`. A bounded
piecewise continuous `Y` (continuous within `[0, t]` off a finite set) has a unique
time-ordered exponential: the continuous solution of the Volterra equation
`U s = 1 + ∫₀ˢ U r * Y r dr` (`existsUnique_isOrderedExp`). If `Y_M → Y₀` uniformly on
`[0, t]`, the grid products converge to it (`tendsto_gridProd`). For constant `Y ≡ A` the
limit is `exp (t • A)`; for a two-piece `Y` it is `exp (t₁ • A) * exp ((t - t₁) • B)`.

This is the limit that passes from discrete-time chains with transition matrices
`1 + Q / M + o(1 / M)` and time-dependent rates to their continuous-time counterparts.

## References

* The product-integral argument is standard; see e.g. J. D. Dollard and C. N. Friedman,
  *Product Integration with Application to Differential Equations*, Addison-Wesley, 1979.
-/

@[expose] public section

open Filter Topology Set MeasureTheory

namespace NormedSpace



section BanachAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- `Y` is **piecewise continuous on `[0, t]`**: continuous within `[0, t]` at every point of
`[0, t]` outside a finite set (no one-sided limits are required; boundedness is a separate
hypothesis wherever it is used). -/
def PiecewiseContinuousOn {E : Type*} [TopologicalSpace E] (Y : ℝ → E) (t : ℝ) : Prop :=
  ∃ S : Finset ℝ, ∀ s ∈ Icc 0 t, s ∉ S → ContinuousWithinAt Y (Icc 0 t) s

/-- `U` is a **time-ordered exponential** of `Y` on `[0, t]`: `U` is continuous on `[0, t]`,
`r ↦ U r * Y r` is integrable on `[0, t]`, and `U s = 1 + ∫₀ˢ U r * Y r dr` for `s ∈ [0, t]`
(the Volterra form of `U' = U Y`, `U 0 = 1`; later times multiply on the right). -/
def IsOrderedExp (Y U : ℝ → 𝔸) (t : ℝ) : Prop :=
  ContinuousOn U (Icc 0 t) ∧ IntervalIntegrable (fun r => U r * Y r) volume 0 t ∧
    ∀ s ∈ Icc 0 t, U s = 1 + ∫ r in (0 : ℝ)..s, U r * Y r

/-- The grid product `∏_{g < t M} (1 + M⁻¹ Y(g / M))` over the natural numbers `g < t M`
(that is, `g < ⌈t M⌉₊`), factors ordered by increasing `g` from left to right. -/
noncomputable def gridProd (Y : ℝ → 𝔸) (t : ℝ) (M : ℕ) : 𝔸 :=
  ((List.range ⌈t * M⌉₊).map fun g : ℕ => 1 + (M : ℝ)⁻¹ • Y (g / M)).prod

private lemma hasDerivAt_mul_left_aux {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    {f : ℝ → R} {f' : R} {x : ℝ} (c : R)
    (hf : HasDerivAt f f' x) : HasDerivAt (fun y => c * f y) (c * f') x := by
  rw [hasDerivAt_iff_isLittleO] at hf ⊢
  refine (hf.const_mul_left c).congr_left fun y => ?_
  simp only [mul_sub, mul_smul_comm]

private lemma hasDerivAt_exp_smul_aux {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [CompleteSpace R] (A : R) (x : ℝ) :
    HasDerivAt (fun u : ℝ => exp (u • A)) (exp (x • A) * A) x :=
  hasDerivAt_exp_smul_const (𝕂 := ℝ) A x

private lemma continuous_exp_smul_aux {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [CompleteSpace R] (A : R) : Continuous fun u : ℝ => exp (u • A) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_exp_smul_aux A x).continuousAt

private lemma integral_exp_smul_aux {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [CompleteSpace R] (A : R) {a b : ℝ} (hab : a ≤ b) :
    ∫ r in a..b, exp (r • A) * A = exp (b • A) - exp (a • A) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_exp_smul_aux A x)
    (((continuous_exp_smul_aux A).mul continuous_const).continuousOn.intervalIntegrable_of_Icc hab)

private lemma integral_mul_exp_smul_aux {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [CompleteSpace R] (c A : R) {a b : ℝ} (hab : a ≤ b) :
    ∫ r in a..b, c * (exp (r • A) * A) = c * exp (b • A) - c * exp (a • A) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => c * exp (u • A))
    (fun x _ => hasDerivAt_mul_left_aux c (hasDerivAt_exp_smul_aux A x))
    ((continuous_const.mul
      ((continuous_exp_smul_aux A).mul continuous_const)).continuousOn.intervalIntegrable_of_Icc
        hab)

private lemma integral_real_exp_aux {L s : ℝ} (hs : 0 ≤ s) :
    ∫ r in (0 : ℝ)..s, Real.exp (r * L) * L = Real.exp (s * L) - 1 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun u : ℝ => Real.exp (u * L)) (Real.exp (x * L) * L) x := by
    intro x
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (𝔸 := ℝ) L x
    simp only [smul_eq_mul] at h
    rw [← Real.exp_eq_exp_ℝ] at h
    exact h
  have hc : Continuous fun u : ℝ => Real.exp (u * L) * L :=
    (Real.continuous_exp.comp (continuous_id.mul continuous_const)).mul continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hc.continuousOn.intervalIntegrable_of_Icc hs)]
  simp

private lemma norm_integral_mul_le_aux {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    {W Y : ℝ → R} {s C K : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hY : ∀ r ∈ Icc 0 s, ‖Y r‖ ≤ C)
    (hW : ∀ r ∈ Icc 0 s, ‖W r‖ ≤ K * Real.exp (r * (2 * C + 1))) :
    ‖∫ r in (0 : ℝ)..s, W r * Y r‖ ≤ K / 2 * Real.exp (s * (2 * C + 1)) := by
  set L := 2 * C + 1 with hL
  have hL0 : 0 < L := by linarith
  have hcont : Continuous fun r : ℝ => Real.exp (r * L) * L :=
    (Real.continuous_exp.comp (continuous_id.mul continuous_const)).mul continuous_const
  calc ‖∫ r in (0 : ℝ)..s, W r * Y r‖
      ≤ ∫ r in (0 : ℝ)..s, K * C / L * (Real.exp (r * L) * L) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hs (ae_of_all _ fun r hr => ?_)
          ((continuous_const.mul hcont).intervalIntegrable _ _)
        have hr' : r ∈ Icc 0 s := Ioc_subset_Icc_self hr
        calc ‖W r * Y r‖ ≤ ‖W r‖ * ‖Y r‖ := norm_mul_le _ _
          _ ≤ K * Real.exp (r * L) * C :=
            mul_le_mul (hW r hr') (hY r hr') (norm_nonneg _)
              (mul_nonneg hK (Real.exp_pos _).le)
          _ = K * C / L * (Real.exp (r * L) * L) := by field_simp
    _ = K * C / L * (Real.exp (s * L) - 1) := by
        rw [intervalIntegral.integral_const_mul, integral_real_exp_aux hs]
    _ ≤ K / 2 * Real.exp (s * L) := by
        have h1 : K * C / L ≤ K / 2 := by
          rw [div_le_div_iff₀ hL0 two_pos]
          nlinarith
        have he1 : 1 ≤ Real.exp (s * L) := Real.one_le_exp (mul_nonneg hs hL0.le)
        calc K * C / L * (Real.exp (s * L) - 1) ≤ K / 2 * (Real.exp (s * L) - 1) :=
              mul_le_mul_of_nonneg_right h1 (by linarith)
          _ ≤ K / 2 * Real.exp (s * L) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private lemma intervalIntegrable_of_pwc_aux {E : Type*} [NormedAddCommGroup E] {Y : ℝ → E}
    {t C : ℝ} (ht : 0 ≤ t) (hY : PiecewiseContinuousOn Y t)
    (hb : ∀ s ∈ Icc 0 t, ‖Y s‖ ≤ C) : IntervalIntegrable Y volume 0 t := by
  obtain ⟨S, hS⟩ := hY
  have hc : ContinuousOn Y (Icc 0 t \ (S : Set ℝ)) := fun s hs =>
    (hS s hs.1 hs.2).mono sdiff_subset
  have hm : AEStronglyMeasurable Y (volume.restrict (Icc 0 t \ (S : Set ℝ))) :=
    hc.aestronglyMeasurable (measurableSet_Icc.diff S.finite_toSet.measurableSet)
  rw [Measure.restrict_congr_set (sdiff_ae_eq_self.2 (measure_mono_null inter_subset_right
    (S.finite_toSet.measure_zero _)))] at hm
  refine IntervalIntegrable.mono_fun' (g := fun _ => C) intervalIntegrable_const ?_ ?_
  · rw [uIoc_of_le ht]
    exact hm.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  · rw [uIoc_of_le ht]
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => hb s (Ioc_subset_Icc_self hs)

/-- **Well-posedness.** A bounded piecewise continuous `Y` has a time-ordered exponential on
`[0, t]`, unique on `[0, t]`. -/
theorem existsUnique_isOrderedExp {Y : ℝ → 𝔸} {t : ℝ} (ht : 0 ≤ t)
    (hY : PiecewiseContinuousOn Y t) (hb : ∃ C, ∀ s ∈ Icc 0 t, ‖Y s‖ ≤ C) :
    ∃ U, IsOrderedExp Y U t ∧ ∀ V, IsOrderedExp Y V t → EqOn V U (Icc 0 t) := by
  obtain ⟨C₀, hC₀⟩ := hb
  obtain ⟨C, hC0, hYC⟩ : ∃ C, 0 ≤ C ∧ ∀ s ∈ Icc 0 t, ‖Y s‖ ≤ C :=
    ⟨max C₀ 0, le_max_right _ _, fun s hs => (hC₀ s hs).trans (le_max_left _ _)⟩
  have hYi : IntervalIntegrable Y volume 0 t := intervalIntegrable_of_pwc_aux ht hY hYC
  have hsub : ∀ s ∈ Icc 0 t, Icc 0 s ⊆ Icc 0 t := fun s hs => Icc_subset_Icc le_rfl hs.2
  have hmulI : ∀ V : ℝ → 𝔸, ContinuousOn V (Icc 0 t) → ∀ s ∈ Icc 0 t,
      IntervalIntegrable (fun r => V r * Y r) volume 0 s := by
    intro V hV s hs
    refine (hYi.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hs))).continuousOn_mul
      ?_
    rw [uIcc_of_le hs.1]
    exact hV.mono (hsub s hs)
  have hL0 : 0 < 2 * C + 1 := by linarith
  have hgeom : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  -- Grönwall: a continuous solution of the homogeneous equation vanishes on `[0, t]`.
  have hzero : ∀ W : ℝ → 𝔸, ContinuousOn W (Icc 0 t) →
      (∀ s ∈ Icc 0 t, W s = ∫ r in (0 : ℝ)..s, W r * Y r) → ∀ s ∈ Icc 0 t, W s = 0 := by
    intro W hWc hWeq
    obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hWc
    obtain ⟨K, hK0, hK⟩ : ∃ K, 0 ≤ K ∧ ∀ s ∈ Icc 0 t, ‖W s‖ ≤ K :=
      ⟨max K₀ 0, le_max_right _ _, fun s hs => (hK₀ s hs).trans (le_max_left _ _)⟩
    have hbound : ∀ n : ℕ, ∀ s ∈ Icc 0 t,
        ‖W s‖ ≤ K * (1 / 2) ^ n * Real.exp (s * (2 * C + 1)) := by
      intro n
      induction n with
      | zero =>
        intro s hs
        rw [pow_zero, mul_one]
        exact (hK s hs).trans
          (le_mul_of_one_le_right hK0 (Real.one_le_exp (mul_nonneg hs.1 hL0.le)))
      | succ n ih =>
        intro s hs
        rw [hWeq s hs]
        calc _ ≤ K * (1 / 2) ^ n / 2 * Real.exp (s * (2 * C + 1)) :=
              norm_integral_mul_le_aux hs.1 hC0 (mul_nonneg hK0 (by positivity))
                (fun r hr => hYC r (hsub s hs hr)) (fun r hr => ih r (hsub s hs hr))
          _ = K * (1 / 2) ^ (n + 1) * Real.exp (s * (2 * C + 1)) := by ring
    intro s hs
    have hlim := (hgeom.const_mul K).mul_const (Real.exp (s * (2 * C + 1)))
    rw [mul_zero, zero_mul] at hlim
    exact norm_le_zero_iff.1 (ge_of_tendsto' hlim fun n => hbound n s hs)
  -- Picard iterates.
  obtain ⟨u, hu0, husucc⟩ : ∃ u : ℕ → ℝ → 𝔸, (∀ s, u 0 s = 1) ∧
      ∀ n s, u (n + 1) s = 1 + ∫ r in (0 : ℝ)..s, u n r * Y r :=
    ⟨fun n => Nat.rec (fun _ => 1) (fun _ v s => 1 + ∫ r in (0 : ℝ)..s, v r * Y r) n,
      fun _ => rfl, fun _ _ => rfl⟩
  have hcont : ∀ n, ContinuousOn (u n) (Icc 0 t) := by
    intro n
    induction n with
    | zero => exact continuousOn_const.congr fun s _ => hu0 s
    | succ n ih =>
      refine (continuousOn_const.add (uIcc_of_le ht ▸
        intervalIntegral.continuousOn_primitive_interval' (hmulI _ ih t ⟨ht, le_rfl⟩)
          left_mem_uIcc)).congr fun s _ => husucc n s
  have hdiff : ∀ n : ℕ, ∀ s ∈ Icc 0 t,
      ‖u (n + 1) s - u n s‖ ≤ (1 / 2) ^ (n + 1) * Real.exp (s * (2 * C + 1)) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      rw [husucc, hu0, add_sub_cancel_left]
      calc _ ≤ 1 / 2 * Real.exp (s * (2 * C + 1)) :=
            norm_integral_mul_le_aux hs.1 hC0 zero_le_one (fun r hr => hYC r (hsub s hs hr))
              fun r hr => by
                rw [hu0, norm_one, one_mul]
                exact Real.one_le_exp (mul_nonneg hr.1 hL0.le)
        _ = _ := by ring
    | succ n ih =>
      intro s hs
      have heq : u (n + 1 + 1) s - u (n + 1) s =
          ∫ r in (0 : ℝ)..s, (u (n + 1) r - u n r) * Y r := by
        rw [husucc (n + 1) s, husucc n s, add_sub_add_left_eq_sub,
          ← intervalIntegral.integral_sub (hmulI _ (hcont _) s hs) (hmulI _ (hcont _) s hs)]
        simp_rw [sub_mul]
      rw [heq]
      calc _ ≤ (1 / 2) ^ (n + 1) / 2 * Real.exp (s * (2 * C + 1)) :=
            norm_integral_mul_le_aux hs.1 hC0 (by positivity)
              (fun r hr => hYC r (hsub s hs hr)) (fun r hr => ih r (hsub s hs hr))
        _ = _ := by ring
  -- The iterates converge uniformly on `[0, t]`.
  obtain ⟨D, hD0, hD⟩ : ∃ D, 0 ≤ D ∧ D = Real.exp (t * (2 * C + 1)) :=
    ⟨_, (Real.exp_pos _).le, rfl⟩
  have hdist : ∀ s ∈ Icc 0 t, ∀ n : ℕ, dist (u n s) (u (n + 1) s) ≤ D / 2 / 2 ^ n := by
    intro s hs n
    rw [dist_comm, dist_eq_norm]
    calc ‖u (n + 1) s - u n s‖ ≤ (1 / 2) ^ (n + 1) * Real.exp (s * (2 * C + 1)) :=
          hdiff n s hs
      _ ≤ (1 / 2) ^ (n + 1) * D := by
          rw [hD]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_right hs.2 hL0.le)) (by positivity)
      _ = D / 2 / 2 ^ n := by rw [one_div_pow, div_div, ← pow_succ', one_div_mul_eq_div]
  obtain ⟨U, hU⟩ : ∃ U : ℝ → 𝔸, ∀ s ∈ Icc 0 t, Tendsto (fun n => u n s) atTop (𝓝 (U s)) :=
    ⟨fun s => limUnder atTop fun n => u n s, fun s hs => tendsto_nhds_limUnder
      (cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two (hdist s hs)))⟩
  have hclose : ∀ s ∈ Icc 0 t, ∀ n : ℕ, dist (u n s) (U s) ≤ D * (1 / 2) ^ n := by
    intro s hs n
    rw [one_div_pow, mul_one_div]
    exact dist_le_of_le_geometric_two_of_tendsto (hdist s hs) (hU s hs) n
  have hDgeom : Tendsto (fun n : ℕ => D * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    have h := hgeom.const_mul D
    rwa [mul_zero] at h
  have hunif : TendstoUniformlyOn u U atTop (Icc 0 t) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hDgeom.eventually (gt_mem_nhds hε)] with n hn s hs
    rw [dist_comm]
    exact (hclose s hs n).trans_lt hn
  have hUc : ContinuousOn U (Icc 0 t) := hunif.continuousOn (Frequently.of_forall hcont)
  have hUeq : ∀ s ∈ Icc 0 t, U s = 1 + ∫ r in (0 : ℝ)..s, U r * Y r := by
    intro s hs
    have h1 : Tendsto (fun n => u (n + 1) s) atTop (𝓝 (U s)) :=
      (tendsto_add_atTop_iff_nat 1).2 (hU s hs)
    have h2 : Tendsto (fun n => u (n + 1) s) atTop
        (𝓝 (1 + ∫ r in (0 : ℝ)..s, U r * Y r)) := by
      simp_rw [husucc]
      refine tendsto_const_nhds.add ?_
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hb : ∀ n : ℕ,
          ‖(∫ r in (0 : ℝ)..s, u n r * Y r) - ∫ r in (0 : ℝ)..s, U r * Y r‖ ≤
            D * (1 / 2) ^ n * C * |s - 0| := by
        intro n
        rw [← intervalIntegral.integral_sub (hmulI _ (hcont n) s hs) (hmulI _ hUc s hs)]
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
        rw [uIoc_of_le hs.1] at hr
        have hr' : r ∈ Icc 0 t := hsub s hs (Ioc_subset_Icc_self hr)
        rw [← sub_mul]
        calc ‖(u n r - U r) * Y r‖ ≤ ‖u n r - U r‖ * ‖Y r‖ := norm_mul_le _ _
          _ ≤ D * (1 / 2) ^ n * C :=
              mul_le_mul (by rw [← dist_eq_norm]; exact hclose r hr' n) (hYC r hr')
                (norm_nonneg _) (mul_nonneg hD0 (by positivity))
      refine squeeze_zero (fun _ => norm_nonneg _) hb ?_
      have h := (hDgeom.mul_const C).mul_const |s - 0|
      rwa [zero_mul, zero_mul] at h
    exact tendsto_nhds_unique h1 h2
  refine ⟨U, ⟨hUc, hmulI U hUc t ⟨ht, le_rfl⟩, hUeq⟩, fun V hV s hs => ?_⟩
  have hW : ∀ r ∈ Icc 0 t, V r - U r = ∫ x in (0 : ℝ)..r, (V x - U x) * Y x := by
    intro r hr
    rw [hV.2.2 r hr, hUeq r hr, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (hmulI _ hV.1 r hr) (hmulI _ hUc r hr)]
    simp_rw [sub_mul]
  exact sub_eq_zero.1 (hzero (fun r => V r - U r) (hV.1.sub hUc) hW s hs)

private lemma norm_listProd_sub_le_aux {R : Type*} [NormedRing R] {f V : ℕ → R} {N : ℕ}
    {a : ℝ} (ha : 1 ≤ a) (hf : ∀ g < N, ‖f g‖ ≤ a) (hV0 : V 0 = 1) :
    ‖((List.range N).map f).prod - V N‖ ≤
      a ^ N * ∑ g ∈ Finset.range N, ‖V g * f g - V (g + 1)‖ := by
  induction N with
  | zero => simp [hV0]
  | succ n ih =>
    have ih' := ih fun g hg => hf g (Nat.lt_succ_of_lt hg)
    rw [List.prod_range_succ, Finset.sum_range_succ]
    have hsplit : ((List.range n).map f).prod * f n - V (n + 1) =
        (((List.range n).map f).prod - V n) * f n + (V n * f n - V (n + 1)) := by noncomm_ring
    rw [hsplit]
    have hfn := hf n (Nat.lt_succ_self n)
    have hS : 0 ≤ ∑ g ∈ Finset.range n, ‖V g * f g - V (g + 1)‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hpow : 1 ≤ a ^ (n + 1) := one_le_pow₀ ha
    have ha0 : 0 ≤ a := zero_le_one.trans ha
    calc ‖(((List.range n).map f).prod - V n) * f n + (V n * f n - V (n + 1))‖
        ≤ ‖((List.range n).map f).prod - V n‖ * ‖f n‖ + ‖V n * f n - V (n + 1)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
      _ ≤ (a ^ n * ∑ g ∈ Finset.range n, ‖V g * f g - V (g + 1)‖) * a +
          ‖V n * f n - V (n + 1)‖ :=
          add_le_add (mul_le_mul ih' hfn (norm_nonneg _)
            (mul_nonneg (pow_nonneg ha0 _) hS)) le_rfl
      _ = a ^ (n + 1) * ∑ g ∈ Finset.range n, ‖V g * f g - V (g + 1)‖ +
          ‖V n * f n - V (n + 1)‖ := by ring
      _ ≤ a ^ (n + 1) * ∑ g ∈ Finset.range n, ‖V g * f g - V (g + 1)‖ +
          a ^ (n + 1) * ‖V n * f n - V (n + 1)‖ :=
          add_le_add le_rfl (le_mul_of_one_le_left (norm_nonneg _) hpow)
      _ = a ^ (n + 1) * (∑ g ∈ Finset.range n, ‖V g * f g - V (g + 1)‖ +
          ‖V n * f n - V (n + 1)‖) := by ring

private lemma exists_delta_aux {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {t : ℝ}
    {K : Set ℝ} (ht : 0 ≤ t) (hK : IsCompact K) (hKt : K ⊆ Icc 0 t)
    (hf : ∀ x ∈ K, ContinuousWithinAt f (Icc 0 t) x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ Icc 0 t, dist x y < δ → ‖f x - f y‖ < ε := by
  obtain ⟨c, hcc, hcI, hcid⟩ : ∃ c : ℝ → ℝ, Continuous c ∧ (∀ x, c x ∈ Icc 0 t) ∧
      ∀ x ∈ Icc 0 t, c x = x :=
    ⟨fun x => max 0 (min x t), continuous_const.max (continuous_id.min continuous_const),
      fun x => ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩,
      fun x hx => by simp only [min_eq_left hx.2, max_eq_right hx.1]⟩
  have hgc : ∀ x ∈ K, ContinuousAt (f ∘ c) x := by
    intro x hx
    have h1 : ContinuousWithinAt f (Icc 0 t) (c x) := by
      rw [hcid x (hKt hx)]
      exact hf x hx
    exact (continuousWithinAt_univ _ _).1 (h1.comp hcc.continuousWithinAt fun y _ => hcI y)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_uniformity_dist.1
    (hK.uniformContinuousAt_of_continuousAt (f ∘ c) hgc (Metric.dist_mem_uniformity hε))
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  have h : dist (f (c x)) (f (c y)) < ε := hδ' hxy hx
  rwa [hcid x (hKt hx), hcid y hy, dist_eq_norm] at h

private lemma exists_oscillation_bound_aux {E : Type*} [NormedAddCommGroup E] {Y : ℝ → E}
    {t C ε : ℝ} (ht : 0 ≤ t) (hY : PiecewiseContinuousOn Y t)
    (hC : ∀ s ∈ Icc 0 t, ‖Y s‖ ≤ C) (hε : 0 < ε) :
    ∃ δ > 0, ∃ ψ : ℝ → ℝ, (∀ a b, IntervalIntegrable ψ volume a b) ∧
      ∫ r in (0 : ℝ)..t, ψ r ≤ ε * (t + 1) ∧
      ∀ x ∈ Icc 0 t, ∀ y ∈ Icc 0 t, x ≤ y → y - x < δ → ‖Y x - Y y‖ ≤ ψ y := by
  obtain ⟨S, hS⟩ := hY
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, ht⟩)
  have hden : 0 < 8 * C * S.card + 1 := by
    have : 0 ≤ 8 * C * S.card := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    linarith
  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ = ε / (8 * C * S.card + 1) :=
    ⟨_, div_pos hε hden, rfl⟩
  set B : Set ℝ := ⋃ p ∈ S, Metric.ball p (2 * ρ) with hB
  set B' : Set ℝ := ⋃ p ∈ S, Metric.ball p ρ with hB'
  have hBm : MeasurableSet B :=
    (isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball).measurableSet
  have hB'o : IsOpen B' := isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball
  have hKc : ∀ x ∈ Icc 0 t \ B', ContinuousWithinAt Y (Icc 0 t) x := fun x hx =>
    hS x hx.1 fun hxS => hx.2 (mem_iUnion₂.2 ⟨x, hxS, Metric.mem_ball_self hρ0⟩)
  obtain ⟨δ, hδ, hδY⟩ := exists_delta_aux ht (isCompact_Icc.diff hB'o) sdiff_subset hKc hε
  have hind_i : ∀ a b : ℝ, IntervalIntegrable (B.indicator fun _ => 2 * C) volume a b :=
    fun a b => ⟨(intervalIntegrable_const (c := 2 * C) (a := a) (b := b)).1.indicator hBm,
      (intervalIntegrable_const (c := 2 * C) (a := a) (b := b)).2.indicator hBm⟩
  refine ⟨min δ ρ, lt_min hδ hρ0, fun r => ε + B.indicator (fun _ => 2 * C) r,
    fun a b => intervalIntegrable_const.add (hind_i a b), ?_, ?_⟩
  · show ∫ r in (0 : ℝ)..t, (ε + B.indicator (fun _ => 2 * C) r) ≤ ε * (t + 1)
    have hvol : (volume (B ∩ Ioc 0 t)).toReal ≤ S.card * (2 * (2 * ρ)) := by
      refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg (Nat.cast_nonneg _) (by linarith)) ?_
      calc volume (B ∩ Ioc 0 t) ≤ volume B := measure_mono inter_subset_left
        _ ≤ ∑ p ∈ S, volume (Metric.ball p (2 * ρ)) := measure_biUnion_finset_le S _
        _ = ∑ p ∈ S, ENNReal.ofReal (2 * (2 * ρ)) := by simp only [Real.volume_ball]
        _ = ENNReal.ofReal (S.card * (2 * (2 * ρ))) := by
            rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (p := (S.card : ℝ))
              (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have hind : ∫ r in (0 : ℝ)..t, B.indicator (fun _ => 2 * C) r ≤ ε := by
      rw [intervalIntegral.integral_of_le ht, integral_indicator_const _ hBm, smul_eq_mul,
        measureReal_def, Measure.restrict_apply hBm]
      calc (volume (B ∩ Ioc 0 t)).toReal * (2 * C) ≤ S.card * (2 * (2 * ρ)) * (2 * C) :=
            mul_le_mul_of_nonneg_right hvol (by linarith)
        _ = 8 * C * S.card * ρ := by ring
        _ ≤ ε := by
            rw [hρ, mul_div_assoc', div_le_iff₀ hden]
            nlinarith
    rw [intervalIntegral.integral_add intervalIntegrable_const (hind_i 0 t),
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    nlinarith
  · intro x hx y hy hxy hyx
    show ‖Y x - Y y‖ ≤ ε + B.indicator (fun _ => 2 * C) y
    by_cases hyB : y ∈ B
    · rw [indicator_of_mem hyB]
      calc ‖Y x - Y y‖ ≤ ‖Y x‖ + ‖Y y‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hC x hx) (hC y hy)
        _ ≤ ε + 2 * C := by linarith
    · rw [indicator_of_notMem hyB, add_zero]
      have hxK : x ∈ Icc 0 t \ B' := by
        refine ⟨hx, fun hxB' => hyB ?_⟩
        obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hxB'
        refine mem_iUnion₂.2 ⟨p, hp, ?_⟩
        rw [Metric.mem_ball] at hxp ⊢
        have hyx' : dist y x < ρ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hxy)]
          exact hyx.trans_le (min_le_right _ _)
        calc dist y p ≤ dist y x + dist x p := dist_triangle _ _ _
          _ < ρ + ρ := add_lt_add hyx' hxp
          _ = 2 * ρ := by ring
      have hxy' : dist x y < δ := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hxy)]
        exact hyx.trans_le (min_le_left _ _)
      exact (hδY x hxK y hy hxy').le

/-- **Time-ordered product limit.** If `Y M → Y₀` uniformly on `[0, t]`, with `Y₀` bounded
and piecewise continuous, and `U` is the time-ordered exponential of `Y₀` on `[0, t]`, then
`∏_{g < t M} (1 + M⁻¹ Y_M(g / M)) → U t`. -/
theorem tendsto_gridProd {Y : ℕ → ℝ → 𝔸} {Y₀ U : ℝ → 𝔸} {t : ℝ} (ht : 0 ≤ t)
    (hconv : TendstoUniformlyOn Y Y₀ atTop (Icc 0 t)) (hY₀ : PiecewiseContinuousOn Y₀ t)
    (hb : ∃ C, ∀ s ∈ Icc 0 t, ‖Y₀ s‖ ≤ C) (hU : IsOrderedExp Y₀ U t) :
    Tendsto (fun M : ℕ => gridProd (Y M) t M) atTop (𝓝 (U t)) := by
  obtain ⟨hUc, hUi, hUeq⟩ := hU
  obtain ⟨C₀, hC₀⟩ := hb
  obtain ⟨C, hC0, hYC⟩ : ∃ C, 0 ≤ C ∧ ∀ s ∈ Icc 0 t, ‖Y₀ s‖ ≤ C :=
    ⟨max C₀ 0, le_max_right _ _, fun s hs => (hC₀ s hs).trans (le_max_left _ _)⟩
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hUc
  obtain ⟨KU, hKU0, hKU⟩ : ∃ K, 0 ≤ K ∧ ∀ s ∈ Icc 0 t, ‖U s‖ ≤ K :=
    ⟨max K₀ 0, le_max_right _ _, fun s hs => (hK₀ s hs).trans (le_max_left _ _)⟩
  have h0t : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, ht⟩
  have hU0 : U 0 = 1 := by simpa using hUeq 0 h0t
  have hint : ∀ x ∈ Icc 0 t, ∀ y ∈ Icc 0 t,
      IntervalIntegrable (fun r => U r * Y₀ r) volume x y := fun x hx y hy =>
    hUi.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc hx) (Icc_subset_uIcc hy))
  set A : ℝ := Real.exp ((C + 1) * (t + 1)) * (1 + (KU + C) * t + KU * (t + 1)) with hA
  have hA0 : 0 ≤ A := by
    have h1 : 0 ≤ (KU + C) * t := mul_nonneg (add_nonneg hKU0 hC0) ht
    have h2 : 0 ≤ KU * (t + 1) := mul_nonneg hKU0 (by linarith)
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  suffices H : ∀ ε > 0, ∀ᶠ M : ℕ in atTop, ‖gridProd (Y M) t M - U t‖ ≤ A * ε by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [H (ε / (A + 1)) (div_pos hε (by linarith))] with M hM
    rw [dist_eq_norm]
    calc ‖gridProd (Y M) t M - U t‖ ≤ A * (ε / (A + 1)) := hM
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
          nlinarith
  intro ε hε
  obtain ⟨δ₁, hδ₁, ψ, hψi, hψint, hψ⟩ := exists_oscillation_bound_aux ht hY₀ hYC hε
  obtain ⟨δ₂, hδ₂, hUδ⟩ := Metric.uniformContinuousOn_iff_le.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hUc) ε hε
  have hM1 : ∀ᶠ M : ℕ in atTop, (1 : ℝ) / M < min δ₁ δ₂ :=
    tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds (lt_min hδ₁ hδ₂))
  have hM2 : ∀ᶠ M : ℕ in atTop, KU * (C + 1) / M ≤ ε :=
    (tendsto_const_div_atTop_nhds_zero_nat (KU * (C + 1))).eventually (ge_mem_nhds hε)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv (min ε 1) (lt_min hε one_pos), hM1, hM2,
    eventually_gt_atTop 0] with M hYM hM1 hM2 hM0
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 hM0
  have hM1' : (1 : ℝ) ≤ M := Nat.one_le_cast.2 hM0
  -- Grid points `g / M`, clipped at `t`.
  set N := ⌈t * M⌉₊ with hN
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun g : ℕ => min ((g : ℝ) / M) t := ⟨_, rfl⟩
  have hcI : ∀ g, c g ∈ Icc 0 t := fun g => by
    rw [hc]
    exact ⟨le_min (div_nonneg (Nat.cast_nonneg _) hMpos.le) ht, min_le_right _ _⟩
  have hc0 : c 0 = 0 := by
    rw [hc]
    simp [ht]
  have hcN : c N = t := by
    rw [hc]
    refine min_eq_right ?_
    rw [le_div_iff₀ hMpos]
    exact Nat.le_ceil _
  have hcg : ∀ g < N, c g = g / M := fun g hg => by
    rw [hc]
    refine min_eq_left ?_
    rw [div_le_iff₀ hMpos]
    exact (Nat.lt_ceil.1 hg).le
  have hcmono : ∀ g, c g ≤ c (g + 1) := fun g => by
    rw [hc]
    exact min_le_min_right _ (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ g)
      hMpos.le)
  have hclen : ∀ g < N, c (g + 1) - c g ≤ 1 / M := fun g hg => by
    have h1 : c (g + 1) ≤ ((g + 1 : ℕ) : ℝ) / M := by
      rw [hc]
      exact min_le_left _ _
    rw [Nat.cast_succ, add_div] at h1
    rw [hcg g hg]
    linarith
  have hNM : (N : ℝ) / M ≤ t + 1 / M := by
    rw [div_le_iff₀ hMpos, add_mul, one_div_mul_cancel hMpos.ne']
    exact (Nat.ceil_lt_add_one (mul_nonneg ht hMpos.le)).le
  -- Bounds on the factors.
  have hYMC : ∀ s ∈ Icc 0 t, ‖Y M s‖ ≤ C + 1 := fun s hs => by
    have h1 := hYM s hs
    rw [dist_comm, dist_eq_norm] at h1
    have h2 := norm_sub_norm_le (Y M s) (Y₀ s)
    have h3 := hYC s hs
    have h4 : min ε 1 ≤ 1 := min_le_right _ _
    linarith
  have hCM : 0 ≤ (C + 1) / (M : ℝ) := div_nonneg (by linarith) hMpos.le
  have hfac : ∀ g < N, ‖(1 : 𝔸) + (M : ℝ)⁻¹ • Y M (g / M)‖ ≤ 1 + (C + 1) / M := fun g hg => by
    calc ‖(1 : 𝔸) + (M : ℝ)⁻¹ • Y M (g / M)‖ ≤ ‖(1 : 𝔸)‖ + ‖(M : ℝ)⁻¹ • Y M (g / M)‖ :=
          norm_add_le _ _
      _ = 1 + (M : ℝ)⁻¹ * ‖Y M (g / M)‖ := by
          rw [norm_one, norm_smul, norm_inv, Real.norm_natCast]
      _ ≤ 1 + (M : ℝ)⁻¹ * (C + 1) := by
          gcongr
          rw [← hcg g hg]
          exact hYMC _ (hcI g)
      _ = 1 + (C + 1) / M := by rw [inv_mul_eq_div]
  -- Discrete Grönwall against `U` at the clipped grid points.
  have hmain := norm_listProd_sub_le_aux (f := fun g : ℕ => 1 + (M : ℝ)⁻¹ • Y M (g / M))
    (V := fun g => U (c g)) (N := N) (le_add_of_nonneg_right hCM) hfac
    (by simp only [hc0, hU0])
  simp only [hcN] at hmain
  -- Local errors.
  set φ : ℝ → ℝ := fun r => KU * ε + KU * ψ r + ε * C with hφ
  have hφi : ∀ a b, IntervalIntegrable φ volume a b := fun a b =>
    (intervalIntegrable_const.add ((hψi a b).const_mul KU)).add intervalIntegrable_const
  have hloc : ∀ g < N, ‖U (c g) * (1 + (M : ℝ)⁻¹ • Y M (g / M)) - U (c (g + 1))‖ ≤
      ((M : ℝ)⁻¹ - (c (g + 1) - c g)) * (KU * (C + 1)) + ∫ r in c g..c (g + 1), φ r := by
    intro g hg
    have hag : c g = g / M := hcg g hg
    have haI := hcI g
    have hbI := hcI (g + 1)
    have hab := hcmono g
    have hlen := hclen g hg
    rw [← hag]
    have hUba : U (c (g + 1)) - U (c g) = ∫ r in c g..c (g + 1), U r * Y₀ r := by
      rw [hUeq _ hbI, hUeq _ haI, add_sub_add_left_eq_sub,
        intervalIntegral.integral_interval_sub_left (hint 0 h0t _ hbI) (hint 0 h0t _ haI)]
    have heq : U (c g) * (1 + (M : ℝ)⁻¹ • Y M (c g)) - U (c (g + 1)) =
        ((M : ℝ)⁻¹ - (c (g + 1) - c g)) • (U (c g) * Y M (c g)) +
          ∫ r in c g..c (g + 1), (U (c g) * Y M (c g) - U r * Y₀ r) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hint _ haI _ hbI),
        intervalIntegral.integral_const, ← hUba, mul_add, mul_one, mul_smul_comm]
      simp only [sub_smul]
      abel
    have hpt : ∀ r ∈ Ioc (c g) (c (g + 1)), ‖U (c g) * Y M (c g) - U r * Y₀ r‖ ≤ φ r := by
      intro r hr
      have hrI : r ∈ Icc 0 t := ⟨haI.1.trans hr.1.le, hr.2.trans hbI.2⟩
      have hra : r - c g < min δ₁ δ₂ := by linarith [hr.2]
      have h1 : ‖Y M (c g) - Y₀ (c g)‖ ≤ ε := by
        rw [← dist_eq_norm, dist_comm]
        exact (hYM _ haI).le.trans (min_le_left _ _)
      have h2 : ‖Y₀ (c g) - Y₀ r‖ ≤ ψ r :=
        hψ _ haI r hrI hr.1.le (hra.trans_le (min_le_left _ _))
      have h3 : ‖U (c g) - U r‖ ≤ ε := by
        rw [← dist_eq_norm]
        refine hUδ _ haI r hrI ?_
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hr.1])]
        exact (hra.trans_le (min_le_right _ _)).le
      have hsplit : U (c g) * Y M (c g) - U r * Y₀ r = U (c g) * (Y M (c g) - Y₀ (c g)) +
          U (c g) * (Y₀ (c g) - Y₀ r) + (U (c g) - U r) * Y₀ r := by noncomm_ring
      rw [hsplit]
      calc ‖U (c g) * (Y M (c g) - Y₀ (c g)) + U (c g) * (Y₀ (c g) - Y₀ r) +
            (U (c g) - U r) * Y₀ r‖
          ≤ ‖U (c g) * (Y M (c g) - Y₀ (c g))‖ + ‖U (c g) * (Y₀ (c g) - Y₀ r)‖ +
            ‖(U (c g) - U r) * Y₀ r‖ := norm_add₃_le
        _ ≤ KU * ε + KU * ψ r + ε * C := by
            gcongr
            · exact (norm_mul_le _ _).trans (mul_le_mul (hKU _ haI) h1 (norm_nonneg _) hKU0)
            · exact (norm_mul_le _ _).trans (mul_le_mul (hKU _ haI) h2 (norm_nonneg _) hKU0)
            · exact (norm_mul_le _ _).trans (mul_le_mul h3 (hYC r hrI) (norm_nonneg _) hε.le)
    have hcoef : 0 ≤ (M : ℝ)⁻¹ - (c (g + 1) - c g) := by
      rw [one_div] at hlen
      linarith
    rw [heq]
    calc ‖((M : ℝ)⁻¹ - (c (g + 1) - c g)) • (U (c g) * Y M (c g)) +
          ∫ r in c g..c (g + 1), (U (c g) * Y M (c g) - U r * Y₀ r)‖
        ≤ ‖((M : ℝ)⁻¹ - (c (g + 1) - c g)) • (U (c g) * Y M (c g))‖ +
          ‖∫ r in c g..c (g + 1), (U (c g) * Y M (c g) - U r * Y₀ r)‖ := norm_add_le _ _
      _ ≤ ((M : ℝ)⁻¹ - (c (g + 1) - c g)) * (KU * (C + 1)) + ∫ r in c g..c (g + 1), φ r := by
          refine add_le_add ?_ (intervalIntegral.norm_integral_le_of_norm_le hab
            (ae_of_all _ hpt) (hφi _ _))
          rw [norm_smul, Real.norm_of_nonneg hcoef]
          exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
            (mul_le_mul (hKU _ haI) (hYMC _ haI) (norm_nonneg _) hKU0)) hcoef
  -- Summing the local errors.
  have hsum : ∑ g ∈ Finset.range N,
      ‖U (c g) * (1 + (M : ℝ)⁻¹ • Y M (g / M)) - U (c (g + 1))‖ ≤
        ((N : ℝ) / M - t) * (KU * (C + 1)) + ∫ r in (0 : ℝ)..t, φ r := by
    calc _ ≤ ∑ g ∈ Finset.range N,
          (((M : ℝ)⁻¹ - (c (g + 1) - c g)) * (KU * (C + 1)) + ∫ r in c g..c (g + 1), φ r) :=
          Finset.sum_le_sum fun g hg => hloc g (Finset.mem_range.1 hg)
      _ = ((N : ℝ) / M - t) * (KU * (C + 1)) + ∫ r in (0 : ℝ)..t, φ r := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
            Finset.sum_range_sub (f := c), Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hφi _ _), hc0, hcN,
            sub_zero, div_eq_mul_inv]
  have hφint : ∫ r in (0 : ℝ)..t, φ r ≤ KU * (ε * (t + 1)) + t * (KU * ε + ε * C) := by
    have h : ∫ r in (0 : ℝ)..t, φ r =
        t * (KU * ε) + KU * (∫ r in (0 : ℝ)..t, ψ r) + t * (ε * C) := by
      rw [hφ, intervalIntegral.integral_add
        (intervalIntegrable_const.add ((hψi 0 t).const_mul KU)) intervalIntegrable_const,
        intervalIntegral.integral_add intervalIntegrable_const ((hψi 0 t).const_mul KU),
        intervalIntegral.integral_const, intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul, smul_eq_mul, smul_eq_mul, sub_zero]
    rw [h]
    calc t * (KU * ε) + KU * (∫ r in (0 : ℝ)..t, ψ r) + t * (ε * C)
        ≤ t * (KU * ε) + KU * (ε * (t + 1)) + t * (ε * C) :=
          add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hψint hKU0)) le_rfl
      _ = KU * (ε * (t + 1)) + t * (KU * ε + ε * C) := by ring
  have hpow : (1 + (C + 1) / M) ^ N ≤ Real.exp ((C + 1) * (t + 1)) := by
    have hNM' : (N : ℝ) / M ≤ t + 1 := by
      have : 1 / (M : ℝ) ≤ 1 := by
        rw [div_le_one hMpos]
        exact hM1'
      linarith
    calc (1 + (C + 1) / M) ^ N ≤ Real.exp ((C + 1) / M) ^ N :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp ((C + 1) / M)]) N
      _ = Real.exp ((C + 1) * ((N : ℝ) / M)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
      _ ≤ Real.exp ((C + 1) * (t + 1)) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hNM' (by linarith))
  have hbr : ((N : ℝ) / M - t) * (KU * (C + 1)) + ∫ r in (0 : ℝ)..t, φ r ≤
      (1 + (KU + C) * t + KU * (t + 1)) * ε := by
    have h1 : ((N : ℝ) / M - t) * (KU * (C + 1)) ≤ ε := by
      calc ((N : ℝ) / M - t) * (KU * (C + 1)) ≤ 1 / M * (KU * (C + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hKU0 (by linarith))
        _ = KU * (C + 1) / M := by ring
        _ ≤ ε := hM2
    calc ((N : ℝ) / M - t) * (KU * (C + 1)) + ∫ r in (0 : ℝ)..t, φ r
        ≤ ε + (KU * (ε * (t + 1)) + t * (KU * ε + ε * C)) := add_le_add h1 hφint
      _ = (1 + (KU + C) * t + KU * (t + 1)) * ε := by ring
  have hS0 : 0 ≤ ∑ g ∈ Finset.range N,
      ‖U (c g) * (1 + (M : ℝ)⁻¹ • Y M (g / M)) - U (c (g + 1))‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc ‖gridProd (Y M) t M - U t‖
      ≤ (1 + (C + 1) / M) ^ N * ∑ g ∈ Finset.range N,
          ‖U (c g) * (1 + (M : ℝ)⁻¹ • Y M (g / M)) - U (c (g + 1))‖ := hmain
    _ ≤ Real.exp ((C + 1) * (t + 1)) *
          (((N : ℝ) / M - t) * (KU * (C + 1)) + ∫ r in (0 : ℝ)..t, φ r) :=
        mul_le_mul hpow hsum hS0 (Real.exp_pos _).le
    _ ≤ Real.exp ((C + 1) * (t + 1)) * ((1 + (KU + C) * t + KU * (t + 1)) * ε) :=
        mul_le_mul_of_nonneg_left hbr (Real.exp_pos _).le
    _ = A * ε := by
        rw [hA]
        ring

/-- **Constant `Y`:** `s ↦ exp (s A)` is the time-ordered exponential of `Y ≡ A`. -/
theorem isOrderedExp_const (A : 𝔸) (t : ℝ) :
    IsOrderedExp (fun _ => A) (fun s => exp (s • A)) t := by
  have hc := continuous_exp_smul_aux A
  refine ⟨hc.continuousOn, (hc.mul continuous_const).intervalIntegrable _ _, fun s hs => ?_⟩
  show exp (s • A) = 1 + ∫ r in (0 : ℝ)..s, exp (r • A) * A
  rw [integral_exp_smul_aux A hs.1, zero_smul, exp_zero]
  abel

/-- **Two-piece `Y`:** for `Y = A` on `[0, t₁)` and `Y = B` from `t₁` on, the time-ordered
exponential is `exp (s A)` up to `t₁` and `exp (t₁ A) * exp ((s - t₁) B)` after. -/
theorem isOrderedExp_piecewise (A B : 𝔸) {t₁ t : ℝ} (h₁ : 0 ≤ t₁) (h : t₁ ≤ t) :
    IsOrderedExp (fun s => if s < t₁ then A else B)
      (fun s => if s ≤ t₁ then exp (s • A) else exp (t₁ • A) * exp ((s - t₁) • B)) t := by
  have hcA := continuous_exp_smul_aux A
  have hcB := continuous_exp_smul_aux B
  have hUc : Continuous fun s : ℝ =>
      if s ≤ t₁ then exp (s • A) else exp (t₁ • A) * exp ((s - t₁) • B) := by
    refine Continuous.if_le hcA
      (continuous_const.mul (hcB.comp (continuous_id.sub continuous_const)))
      continuous_id continuous_const fun x hx => ?_
    have hx' : x = t₁ := hx
    rw [hx']
    simp
  have hYm : AEStronglyMeasurable (fun s : ℝ => if s < t₁ then A else B) volume :=
    (StronglyMeasurable.ite measurableSet_Iio stronglyMeasurable_const
      stronglyMeasurable_const).aestronglyMeasurable
  have hYi : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => if s < t₁ then A else B) volume a b :=
    fun a b => IntervalIntegrable.mono_fun' (g := fun _ => ‖A‖ + ‖B‖) intervalIntegrable_const
      hYm.restrict (ae_of_all _ fun s => by
        dsimp only
        split_ifs
        · exact le_add_of_nonneg_right (norm_nonneg _)
        · exact le_add_of_nonneg_left (norm_nonneg _))
  have hUYi : ∀ a b : ℝ, IntervalIntegrable (fun r : ℝ =>
      (if r ≤ t₁ then exp (r • A) else exp (t₁ • A) * exp ((r - t₁) • B)) *
        (if r < t₁ then A else B)) volume a b :=
    fun a b => (hYi a b).continuousOn_mul hUc.continuousOn
  have hI1 : ∀ s, 0 ≤ s → s ≤ t₁ → ∫ r in (0 : ℝ)..s,
      (if r ≤ t₁ then exp (r • A) else exp (t₁ • A) * exp ((r - t₁) • B)) *
        (if r < t₁ then A else B) = exp (s • A) - 1 := by
    intro s hs0 hs1
    have hae : ∀ᵐ r ∂volume, r ∈ uIoc 0 s →
        (if r ≤ t₁ then exp (r • A) else exp (t₁ • A) * exp ((r - t₁) • B)) *
          (if r < t₁ then A else B) = exp (r • A) * A := by
      filter_upwards [(Set.countable_singleton t₁).ae_notMem volume] with r hr hrs
      rw [uIoc_of_le hs0] at hrs
      have hrt : r < t₁ := lt_of_le_of_ne (hrs.2.trans hs1) hr
      rw [ite_eq_left hrt.le, ite_eq_left hrt]
    rw [intervalIntegral.integral_congr_ae hae, integral_exp_smul_aux A hs0, zero_smul, exp_zero]
  refine ⟨hUc.continuousOn, hUYi 0 t, fun s hs => ?_⟩
  show (if s ≤ t₁ then exp (s • A) else exp (t₁ • A) * exp ((s - t₁) • B)) =
    1 + ∫ r in (0 : ℝ)..s, (if r ≤ t₁ then exp (r • A) else exp (t₁ • A) * exp ((r - t₁) • B)) *
      (if r < t₁ then A else B)
  by_cases hst : s ≤ t₁
  · rw [ite_eq_left hst, hI1 s hs.1 hst]
    abel
  · rw [not_le] at hst
    have hI2 : ∫ r in t₁..s,
        (if r ≤ t₁ then exp (r • A) else exp (t₁ • A) * exp ((r - t₁) • B)) *
          (if r < t₁ then A else B) = exp (t₁ • A) * exp ((s - t₁) • B) - exp (t₁ • A) := by
      have hcongr : EqOn (fun r : ℝ =>
          (if r ≤ t₁ then exp (r • A) else exp (t₁ • A) * exp ((r - t₁) • B)) *
            (if r < t₁ then A else B))
          (fun r => (fun x : ℝ => exp (t₁ • A) * (exp (x • B) * B)) (r - t₁)) (uIcc t₁ s) := by
        intro r hr
        rw [uIcc_of_le hst.le] at hr
        rcases eq_or_lt_of_le hr.1 with hr1 | hr1
        · subst hr1
          simp
        · simp only [ite_eq_right (not_le.2 hr1), ite_eq_right (not_lt.2 hr1.le), mul_assoc]
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_comp_sub_right
        (fun x : ℝ => exp (t₁ • A) * (exp (x • B) * B)) t₁, sub_self,
        integral_mul_exp_smul_aux _ B (sub_nonneg.2 hst.le), zero_smul, exp_zero, mul_one]
    rw [ite_eq_right (not_le.2 hst), ← intervalIntegral.integral_add_adjacent_intervals (hUYi 0 t₁)
      (hUYi t₁ s), hI1 t₁ h₁ le_rfl, hI2]
    abel

/-- **Acceptance, constant `Y`:** `∏_{g < t M} (1 + M⁻¹ A) → exp (t A)`. -/
theorem tendsto_gridProd_const (A : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun M : ℕ => gridProd (fun _ => A) t M) atTop (𝓝 (exp (t • A))) := by
  have hm : Tendsto (fun M : ℕ => ((⌈t * M⌉₊ : ℕ) : ℝ) / M) atTop (𝓝 t) :=
    (tendsto_nat_ceil_mul_div_atTop ht).comp tendsto_natCast_atTop_atTop
  refine (tendsto_one_add_inv_smul_pow (m := fun M : ℕ => ⌈t * M⌉₊)
    (tendsto_const_nhds (x := A)) hm).congr fun M => ?_
  simp [gridProd, List.map_const', List.prod_replicate]


/-- **Acceptance, two-piece `Y`:** the grid products converge to
`exp (t₁ A) * exp ((t - t₁) B)`. -/
theorem tendsto_gridProd_piecewise (A B : 𝔸) {t₁ t : ℝ} (h₁ : 0 ≤ t₁) (h : t₁ ≤ t) :
    Tendsto (fun M : ℕ => gridProd (fun s => if s < t₁ then A else B) t M) atTop
      (𝓝 (exp (t₁ • A) * exp ((t - t₁) • B))) := by
  have ht : 0 ≤ t := h₁.trans h
  have hle : ∀ M : ℕ, ⌈t₁ * M⌉₊ ≤ ⌈t * M⌉₊ := fun M =>
    Nat.ceil_mono (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg M))
  have hm₁ : Tendsto (fun M : ℕ => ((⌈t₁ * M⌉₊ : ℕ) : ℝ) / M) atTop (𝓝 t₁) :=
    (tendsto_nat_ceil_mul_div_atTop h₁).comp tendsto_natCast_atTop_atTop
  have hm₂ : Tendsto (fun M : ℕ => ((⌈t * M⌉₊ - ⌈t₁ * M⌉₊ : ℕ) : ℝ) / M) atTop
      (𝓝 (t - t₁)) := by
    have h2 : Tendsto (fun M : ℕ => ((⌈t * M⌉₊ : ℕ) : ℝ) / M) atTop (𝓝 t) :=
      (tendsto_nat_ceil_mul_div_atTop ht).comp tendsto_natCast_atTop_atTop
    refine (h2.sub hm₁).congr fun M => ?_
    rw [Nat.cast_sub (hle M), sub_div]
  refine ((tendsto_one_add_inv_smul_pow (m := fun M : ℕ => ⌈t₁ * M⌉₊)
    (tendsto_const_nhds (x := A)) hm₁).mul
    (tendsto_one_add_inv_smul_pow (m := fun M : ℕ => ⌈t * M⌉₊ - ⌈t₁ * M⌉₊)
      (tendsto_const_nhds (x := B)) hm₂)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with M hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsplit : ⌈t * M⌉₊ = ⌈t₁ * M⌉₊ + (⌈t * M⌉₊ - ⌈t₁ * M⌉₊) := by
    have := hle M
    omega
  have hA : ∀ g ∈ List.range ⌈t₁ * M⌉₊,
      (1 + (M : ℝ)⁻¹ • (fun s => if s < t₁ then A else B) ((g : ℝ) / M)) =
        1 + (M : ℝ)⁻¹ • A := by
    intro g hg
    have hg' : (g : ℝ) < t₁ * M := Nat.lt_ceil.1 (List.mem_range.1 hg)
    have : (g : ℝ) / M < t₁ := (div_lt_iff₀ hMpos).2 hg'
    simp [this]
  have hB : ∀ g ∈ (List.range (⌈t * M⌉₊ - ⌈t₁ * M⌉₊)).map (⌈t₁ * M⌉₊ + ·),
      (1 + (M : ℝ)⁻¹ • (fun s => if s < t₁ then A else B) ((g : ℝ) / M)) =
        1 + (M : ℝ)⁻¹ • B := by
    intro g hg
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    have hc : t₁ * M ≤ ((⌈t₁ * M⌉₊ + j : ℕ) : ℝ) := by
      have := Nat.le_ceil (t₁ * M)
      push_cast
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have : ¬ ((⌈t₁ * M⌉₊ + j : ℕ) : ℝ) / M < t₁ := by
      rw [div_lt_iff₀ hMpos]
      linarith
    simp only [this, ↓reduceIte]
  simp only [gridProd]
  rw [hsplit, List.range_add, List.map_append, List.prod_append, List.map_congr_left hA,
    List.map_congr_left hB, List.map_const', List.map_const', List.prod_replicate,
    List.prod_replicate, List.length_range, List.length_map, List.length_range,
    Nat.add_sub_cancel_left]


end BanachAlgebra

end NormedSpace
