/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# A four-function HRT configuration

The translates by one and by the square root of two, together with the original function and its
frequency-one modulation, form a linearly independent family for every nonzero function in
$L^2(ℝ)$. The proof compares products along the integer orbits of the inverse Fourier transform.
-/

@[expose] public section

open Set MeasureTheory Filter Function FourierTransform
open scoped ENNReal Topology FourierTransform ComplexConjugate

namespace MathlibExt.Analysis.FourFunctionHRTWanted

/-- **Frequency-one modulation factor.** The function $\mathbb{R} \to \mathbb{C}$ given by
$x \mapsto e^{2\pi i x}$; multiplying a function by it modulates that function by frequency one. -/
noncomputable def modulationOne (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- **A four-function case of the HRT conjecture.** For every function
$g : \mathbb{R} \to \mathbb{C}$ in $L^2(\mathbb{R})$ that is not zero almost everywhere, the four
functions $g(x)$, $g(x - 1)$, $g(x - \sqrt{2})$ and $e^{2\pi i x} g(x)$ are linearly independent:
whenever $c_0, c_1, c_2, c_3 \in \mathbb{C}$ satisfy
$c_0 g(x) + c_1 g(x - 1) + c_2 g(x - \sqrt{2}) + c_3 e^{2\pi i x} g(x) = 0$ for almost every
$x \in \mathbb{R}$, we have $c_0 = c_1 = c_2 = c_3 = 0$. -/
def conjecture : Prop :=
  ∀ g : ℝ → ℂ, MemLp g 2 volume → ¬(g =ᵐ[volume] 0) →
    ∀ c₀ c₁ c₂ c₃ : ℂ,
      (fun x ↦ c₀ * g x + c₁ * g (x - 1) + c₂ * g (x - Real.sqrt 2) +
        c₃ * modulationOne x * g x) =ᵐ[volume] 0 →
      c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0

noncomputable section

private abbrev L2 := Lp ℂ 2 (volume : Measure ℝ)

private def shift (a : ℝ) : L2 →ₗᵢ[ℂ] L2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (· + a) (measurePreserving_add_right volume a)

private theorem coe_shift (a : ℝ) (f : L2) :
    ⇑(shift a f) =ᵐ[volume] fun x ↦ f (x + a) :=
  Lp.coeFn_compMeasurePreserving _ _

private def e (x : ℝ) : ℂ := (Real.fourierChar x : Circle)

private theorem norm_e (x : ℝ) : ‖e x‖ = 1 := Circle.norm_coe _

private theorem phase_mem (a : ℝ) : MemLp (fun x : ℝ ↦ e (a * x)) ∞ volume :=
  memLp_top_of_bound (by unfold e; fun_prop) 1 (.of_forall fun x ↦ (norm_e _).le)

private def modulate (a : ℝ) : L2 →L[ℂ] L2 :=
  ((ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2) ((phase_mem a).toLp _)

private theorem coe_modulate (a : ℝ) (f : L2) :
    ⇑(modulate a f) =ᵐ[volume] fun x ↦ e (a * x) * f x := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ((phase_mem a).toLp _) f,
    (phase_mem a).coeFn_toLp] with x hx hx'
  exact hx.trans (congrArg (· * f x) hx')

private theorem schwartz_shift (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    shift a (f.toLp 2) = (f.compSubConstCLM ℂ (-a)).toLp 2 := by
  apply Lp.ext
  filter_upwards [coe_shift a (f.toLp 2),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp
      (f.coeFn_toLp 2 volume),
    (f.compSubConstCLM ℂ (-a)).coeFn_toLp 2] with x hx hy hz
  simpa using hx.trans (hy.trans (by simpa using hz.symm))

private theorem point_shift (g : ℝ → ℂ) (a x : ℝ) :
    𝓕 (g ∘ (· + a)) x = e (a * x) * 𝓕 g x := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ ℝ) g a) x
  change 𝓕 (g ∘ (· + a)) x = (Real.fourierChar ((innerₗ ℝ) a x)) • 𝓕 g x at h
  simpa [Circle.smul_def, e, Real.inner_apply, mul_comm] using h

-- Extend translation covariance from Schwartz functions to the Plancherel transform by density.
private theorem ft_shift (a : ℝ) (f : L2) : 𝓕 (shift a f) = modulate a (𝓕 f) := by
  apply DenseRange.induction_on (p := fun g : L2 ↦ 𝓕 (shift a g) = modulate a (𝓕 g))
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) (μ := volume) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq (continuous_fourier.comp (shift a).continuous)
      ((modulate a).continuous.comp continuous_fourier)
  intro g
  change 𝓕 (shift a (g.toLp 2)) = modulate a (𝓕 (g.toLp 2))
  rw [schwartz_shift, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (g.compSubConstCLM ℂ (-a))).coeFn_toLp 2,
    coe_modulate a ((𝓕 g).toLp 2), (𝓕 g).coeFn_toLp 2] with x hx hy hz
  rw [hx, hy, hz, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have hcoe : ⇑(g.compSubConstCLM ℂ (-a)) = g ∘ (fun x ↦ x + a) := by ext; simp
  rw [hcoe]
  exact point_shift g a x

private theorem ift_shift (a : ℝ) (f : L2) : 𝓕⁻ (shift a f) = modulate (-a) (𝓕⁻ f) := by
  apply DenseRange.induction_on (p := fun g : L2 ↦ 𝓕⁻ (shift a g) = modulate (-a) (𝓕⁻ g))
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) (μ := volume) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq (continuous_fourierInv.comp (shift a).continuous)
      ((modulate (-a)).continuous.comp continuous_fourierInv)
  intro g
  change 𝓕⁻ (shift a (g.toLp 2)) = modulate (-a) (𝓕⁻ (g.toLp 2))
  rw [schwartz_shift, SchwartzMap.toLp_fourierInv_eq, SchwartzMap.toLp_fourierInv_eq]
  apply Lp.ext
  filter_upwards [(𝓕⁻ (g.compSubConstCLM ℂ (-a))).coeFn_toLp 2,
    coe_modulate (-a) ((𝓕⁻ g).toLp 2), (𝓕⁻ g).coeFn_toLp 2] with x hx hy hz
  rw [hx, hy, hz, SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe]
  have hcoe : ⇑(g.compSubConstCLM ℂ (-a)) = g ∘ (fun x ↦ x + a) := by ext; simp
  rw [hcoe]
  simpa [Real.fourierInv_eq_fourier_neg, neg_mul, mul_neg] using point_shift g a (-x)

private theorem relation_in_L2 {g : ℝ → ℂ} (hg : MemLp g 2 volume) (a b c d : ℂ)
    (h : (fun x ↦ a * g x + b * g (x - 1) + c * g (x - Real.sqrt 2) +
      d * modulationOne x * g x) =ᵐ[volume] 0) :
    a • hg.toLp g + b • shift (-1) (hg.toLp g) + c • shift (-Real.sqrt 2) (hg.toLp g) +
      d • modulate 1 (hg.toLp g) = 0 := by
  let f := hg.toLp g
  let u := b • shift (-1) f
  let v := c • shift (-Real.sqrt 2) f
  let w := d • modulate 1 f
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (a • f + u + v) w, Lp.coeFn_add (a • f + u) v,
    Lp.coeFn_add (a • f) u, Lp.coeFn_smul a f, Lp.coeFn_smul b (shift (-1) f),
    Lp.coeFn_smul c (shift (-Real.sqrt 2) f), Lp.coeFn_smul d (modulate 1 f),
    coe_shift (-1) f, coe_shift (-Real.sqrt 2) f, coe_modulate 1 f, hg.coeFn_toLp,
    (measurePreserving_add_right volume (-1 : ℝ)).quasiMeasurePreserving.ae_eq_comp hg.coeFn_toLp,
    (measurePreserving_add_right volume (-Real.sqrt 2)).quasiMeasurePreserving.ae_eq_comp
      hg.coeFn_toLp, h, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)]
  intro x h₁ h₂ h₃ h₄ h₅ h₆ h₇ ht hs hm hf hf' hf'' hx hz
  change ((a • f + u + v + w : L2) x) = _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h₁ h₂ h₃ h₄ h₅ h₆ h₇
  change u x = _ at h₅
  change v x = _ at h₆
  change w x = _ at h₇
  change f x = _ at hf
  change f (x + -1) = _ at hf'
  change f (x + -Real.sqrt 2) = _ at hf''
  rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, ht, hs, hm, hf, hf', hf'', hz]
  simpa [sub_eq_add_neg, mul_assoc, e, modulationOne, Real.fourierChar_apply] using hx

-- In the inverse Fourier domain the modulation becomes a shift by one.
private theorem transformed_relation {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    (hn : ¬(g =ᵐ[volume] 0)) (a b c d : ℂ)
    (h : (fun x ↦ a * g x + b * g (x - 1) + c * g (x - Real.sqrt 2) +
      d * modulationOne x * g x) =ᵐ[volume] 0) :
    ∃ F : L2, F ≠ 0 ∧ ∀ᵐ x : ℝ, (a + b * e x + c * e (Real.sqrt 2 * x)) * F x +
      d * F (x + 1) = 0 := by
  let F : L2 := 𝓕⁻ (hg.toLp g)
  have hF0 : 𝓕 F = hg.toLp g := (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _
  have hmod : 𝓕⁻ (modulate 1 (hg.toLp g)) = shift 1 F := by
    rw [← hF0, ← ft_shift]
    exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm_apply_apply _
  have hl := congrArg (fun u : L2 ↦ 𝓕⁻ u) (relation_in_L2 hg a b c d h)
  simp only [fourierInv_add, fourierInv_smul, ift_shift, neg_neg, hmod, fourierInv_zero] at hl
  refine ⟨F, fun hF ↦ hn (hg.coeFn_toLp.symm.trans ?_), ?_⟩
  · have h0 : hg.toLp g = 0 := by
      rw [← hF0, hF]
      exact (Lp.fourierTransformₗᵢ ℝ ℂ).map_zero
    rw [h0]
    exact Lp.coeFn_zero ..
  let u := b • modulate 1 F
  let v := c • modulate (Real.sqrt 2) F
  let w := d • shift 1 F
  change a • F + u + v + w = 0 at hl
  filter_upwards [Lp.coeFn_add (a • F + u + v) w, Lp.coeFn_add (a • F + u) v,
    Lp.coeFn_add (a • F) u, Lp.coeFn_smul a F, Lp.coeFn_smul b (modulate 1 F),
    Lp.coeFn_smul c (modulate (Real.sqrt 2) F), Lp.coeFn_smul d (shift 1 F),
    coe_modulate 1 F, coe_modulate (Real.sqrt 2) F, coe_shift 1 F,
    Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇ hb hc hd hz
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h₁ h₂ h₃ h₄ h₅ h₆ h₇
  change u x = _ at h₅
  change v x = _ at h₆
  change w x = _ at h₇
  rw [hl, hz, h₂, h₃, h₄, h₅, h₆, h₇, hb, hc, hd, one_mul] at h₁
  change (0 : ℂ) = _ at h₁
  linear_combination -h₁

private def periodSum (T : ℝ) (u : ℝ → ℝ≥0∞) (x : ℝ) := ∑' n : ℤ, u (x + n * T)

private theorem periodSum_meas {T : ℝ} {u : ℝ → ℝ≥0∞} (hu : AEMeasurable u) :
    AEMeasurable (periodSum T u) :=
  AEMeasurable.tsum fun n ↦ hu.comp_quasiMeasurePreserving
    (measurePreserving_add_right volume ((n : ℤ) * T)).quasiMeasurePreserving

private theorem integral_periodSum {T : ℝ} (hT : 0 < T) (y : ℝ) {u : ℝ → ℝ≥0∞}
    (hu : AEMeasurable u) :
    ∫⁻ x in Ioc y (y + T), periodSum T u x = ∫⁻ x, u x := by
  rw [(isAddFundamentalDomain_Ioc hT y volume).lintegral_eq_tsum'' u]
  rw [← (AddSubgroup.zmultiplesEquivInt hT.ne').symm.toEquiv.tsum_eq]
  unfold periodSum
  rw [lintegral_tsum (f := fun (n : ℤ) (x : ℝ) ↦ u (x + n * T))
    (μ := volume.restrict (Ioc y (y + T))) (fun n ↦ (hu.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume ((n : ℝ) * T)).quasiMeasurePreserving).restrict)]
  apply tsum_congr
  intro n
  change _ = ∫⁻ x in _, u (((AddSubgroup.zmultiplesEquivInt hT.ne').symm n : ℝ) + x)
  simp [AddSubgroup.coe_zmultiplesEquivInt_symm_apply, zsmul_eq_mul, add_comm]

private theorem periodSum_finite {T : ℝ} (hT : 0 < T) {u : ℝ → ℝ≥0∞}
    (hu : AEMeasurable u) (hi : (∫⁻ x, u x) ≠ ∞) :
    ∀ᵐ x, periodSum T u x < ∞ := by
  have h (q : ℚ) : ∀ᵐ x, x ∈ Ioc (q : ℝ) (q + T) → periodSum T u x < ∞ := by
    apply (ae_restrict_iff' measurableSet_Ioc).mp
    apply ae_lt_top' (periodSum_meas hu).restrict
    rwa [integral_periodSum hT _ hu]
  filter_upwards [ae_all_iff.2 h] with x hx
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show x - T < x by linarith)
  exact hx q ⟨hq₂, by linarith⟩

private theorem periodSum_shift (T : ℝ) (u : ℝ → ℝ≥0∞) (x : ℝ) (k : ℤ) :
    periodSum T u (x + k * T) = periodSum T u x := by
  unfold periodSum
  convert (Equiv.addLeft k).tsum_eq (fun n : ℤ ↦ u (x + n * T)) using 2 with n
  simp [add_mul, add_assoc]

private theorem ae_periodic_integral {u : ℝ → ℝ≥0∞} (hu : AEMeasurable u)
    (hi : (∫⁻ x, u x) ≠ ∞) (hp : ∀ᵐ x, u (x + 1) = u x) : u =ᵐ[volume] 0 := by
  have hinv : ∀ n : ℕ, ∀ᵐ x, u (x + n) = u x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      filter_upwards [ih, (measurePreserving_add_right volume (n : ℝ)).quasiMeasurePreserving.ae
        (p := fun x ↦ u (x + 1) = u x) hp] with x hx hy
      simpa [add_assoc] using hy.trans hx
  filter_upwards [ae_all_iff.2 hinv, periodSum_finite zero_lt_one hu hi] with x hx hs
  by_contra h
  have hpos : 0 < u x := pos_iff_ne_zero.mpr h
  have hsub := tsum_comp_le_tsum_of_injective (Nat.cast_injective (R := ℤ)) (fun k : ℤ ↦ u (x + k))
  simp only [periodSum, mul_one] at hs
  simp only [Int.cast_natCast, hx, ENNReal.tsum_const_eq_top_of_ne_zero hpos.ne'] at hsub
  exact hs.not_ge hsub

-- Normalize by the total mass on each T-orbit. The resulting density is integrable and
-- invariant under translation by one, so it vanishes.
private theorem no_periodic_weight {u p : ℝ → ℝ≥0∞} {T : ℝ} (hT : 0 < T)
    (hu : AEMeasurable u) (hi : (∫⁻ x, u x) ≠ ∞)
    (hp : Periodic p T) (hpos : ∀ᵐ x, p x ≠ 0 ∧ p x ≠ ∞)
    (hr : ∀ᵐ x, u (x + 1) = p x * u x) : u =ᵐ[volume] 0 := by
  let w (x : ℝ) := u x / periodSum T u x
  have hw : AEMeasurable w := hu.div (periodSum_meas hu)
  have hmass (x : ℝ) : periodSum T w x ≤ 1 := by
    change (∑' k : ℤ, u (x + k * T) / periodSum T u (x + k * T)) ≤ 1
    simp_rw [periodSum_shift, div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_inv_le_one _
  have hwi : (∫⁻ x, w x) ≠ ∞ := by
    rw [← integral_periodSum hT 0 hw]
    apply ne_top_of_le_ne_top _ (lintegral_mono (g := fun _ ↦ 1) hmass)
    simp
  have hper : ∀ᵐ x, w (x + 1) = w x := by
    have hshift (k : ℤ) :=
      (measurePreserving_add_right volume ((k : ℝ) * T)).quasiMeasurePreserving.ae
        (p := fun x ↦ u (x + 1) = p x * u x) hr
    filter_upwards [hr, hpos, ae_all_iff.2 hshift] with x hx hpx hk
    have hs : periodSum T u (x + 1) = p x * periodSum T u x := by
      unfold periodSum
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro k
      have he : p (x + k * T) = p x := by simpa [zsmul_eq_mul] using hp.zsmul k x
      simpa only [add_right_comm x 1, ← he] using hk k
    change u (x + 1) / _ = _
    rw [hx, hs]
    exact ENNReal.mul_div_mul_left _ _ hpx.1 hpx.2
  filter_upwards [ae_periodic_integral hw hwi hper, periodSum_finite hT hu hi] with x hx hs
  change u x / periodSum T u x = 0 at hx
  exact (ENNReal.div_eq_zero_iff.mp hx).resolve_right hs.ne

private theorem square_integral_fin (F : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫⁻ x, ‖F x‖ₑ ^ 2) ≠ ∞ := by
  simpa using (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
    (f := (F : ℝ → ℂ)) two_ne_zero ENNReal.ofNat_ne_top (Lp.memLp F)).ne

private theorem orbit_decay (F : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ᵐ x, Tendsto (fun n : ℤ ↦ ‖F (x + n)‖) cofinite (𝓝 0) := by
  have hm : AEMeasurable (fun x : ℝ ↦ ‖F x‖ₑ ^ 2) := (Lp.aestronglyMeasurable F).eNorm.pow_const _
  filter_upwards [periodSum_finite zero_lt_one hm (square_integral_fin F)] with x hx
  simp only [periodSum, mul_one] at hx
  have ht := ENNReal.tendsto_cofinite_zero_of_tsum_ne_top hx.ne
  have hr := (ENNReal.continuousAt_toReal (x := 0) ENNReal.zero_ne_top).tendsto.comp ht
  simpa [Function.comp_def, ENNReal.toReal_pow, Real.sqrt_sq (norm_nonneg _)] using
    (Real.continuous_sqrt.tendsto _).comp hr

private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  exact congrArg (fun z : Circle ↦ (z : ℂ)) (Real.fourierChar.map_add_eq_mul x y)

private theorem e_int (k : ℤ) : e k = 1 := by
  simp [e, Real.fourierChar_apply', Circle.exp_two_pi_mul_int]

private theorem ae_ne_of_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : AnalyticOnNhd ℝ f univ) (hne : ¬∀ x, f x = 0) :
    ∀ᵐ x, f x ≠ 0 := by
  rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
  · exact (hne fun x ↦ h (mem_univ x)).elim
  · have hd := (mem_codiscrete'.mp (show {x | f x ≠ 0} ∈ codiscrete ℝ from h)).2
    exact ((HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd).measure_zero volume

private theorem analytic_e (t x : ℝ) : AnalyticAt ℝ (fun y ↦ e (t * y)) x := by
  unfold e
  simp only [Real.fourierChar_apply]
  apply (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp
  apply AnalyticAt.mul _ analyticAt_const
  exact (Complex.ofRealCLM.analyticAt _).comp
    (analyticAt_const.mul (analyticAt_const.mul analyticAt_id))

private theorem e_half : e (1/2) = -1 := by
  unfold e
  rw [Real.fourierChar_apply, show 2 * Real.pi * (1 / 2) = Real.pi by ring]
  exact Complex.exp_pi_mul_I

private theorem e_quarter : e (1/4) = Complex.I := by
  have h : 2 * Real.pi * (1/4) = Real.pi / 2 := by ring
  unfold e
  rw [Real.fourierChar_apply, h, Complex.ofReal_div, Complex.ofReal_ofNat]
  exact Complex.exp_pi_div_two_mul_I

private theorem e_sqrt_ne : e (Real.sqrt 2) ≠ 1 := by
  intro h
  have h' : Circle.exp (2 * Real.pi * Real.sqrt 2) = 1 := Subtype.ext h
  obtain ⟨k,hk⟩ := Circle.exp_eq_one.mp h'
  exact irrational_sqrt_two.ne_int k
    (mul_left_cancel₀ (show 2 * Real.pi ≠ 0 by positivity) (hk.trans (mul_comm _ _)))

private def trig (a b c : ℂ) (x : ℝ) := a + b * e x + c * e (Real.sqrt 2 * x)

private theorem trig_ae_ne {a b c : ℂ} (hn : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    ∀ᵐ x, trig a b c x ≠ 0 := by
  apply ae_ne_of_analytic
  · intro x _
    have he : AnalyticAt ℝ e x := by simpa using analytic_e 1 x
    exact (analyticAt_const.add (analyticAt_const.mul he)).add
      (analyticAt_const.mul (analytic_e _ _))
  intro h
  have h0 := h 0
  have h1 := h 1
  have h2 := h (1/2)
  simp only [trig, mul_zero, show e 0 = 1 by simp [e], mul_one] at h0
  simp only [trig, mul_one, show e 1 = 1 by simpa using e_int 1] at h1
  have hc : c = 0 := by
    have hp : c * (e (Real.sqrt 2) - 1) = 0 := by linear_combination h1 - h0
    exact (mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr e_sqrt_ne)
  simp only [trig, e_half, hc, zero_mul, add_zero, mul_neg, mul_one] at h2
  exact hn ⟨by linear_combination (h0 + h2 - hc) / 2,
    by linear_combination (h0 - h2 - hc) / 2, hc⟩

-- A fixed level of the squared norm is discrete unless the level equation is an identity.
-- Evaluating at four phases rules out that identity when both coefficients are nonzero.
private theorem unequal_norm_ae (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ᵐ x, ‖a + b * e x‖ ≠ ‖c‖ := by
  let f (x : ℝ) := Complex.normSq (a + b * e x) - Complex.normSq c
  have haff (x : ℝ) : AnalyticAt ℝ (fun y ↦ a + b * e y) x :=
    analyticAt_const.add (analyticAt_const.mul (by simpa using analytic_e 1 x))
  have haf : AnalyticOnNhd ℝ f univ := by
    intro x _
    have hr := (Complex.reCLM.analyticAt _).comp (haff x)
    have hi := (Complex.imCLM.analyticAt _).comp (haff x)
    exact ((hr.mul hr).add (hi.mul hi)).sub analyticAt_const
  have hnf : ¬∀ x, f x = 0 := by
    intro h
    have h0 := h 0
    have h1 := h (1/2)
    have h2 := h (1/4)
    have h3 := h (1/4 + 1/2)
    simp only [f, e_add, e_half, e_quarter, show e 0 = 1 by simp [e], mul_one, mul_neg,
      Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
      Complex.mul_I_re, Complex.mul_I_im] at h0 h1 h2 h3
    apply (mul_ne_zero ha (show conj b ≠ 0 by simpa using hb))
    apply Complex.ext
    · simp only [Complex.zero_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      linear_combination (h0 - h1) / 4
    · simp only [Complex.zero_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      linear_combination (h2 - h3) / 4
  filter_upwards [ae_ne_of_analytic haf hnf] with x hx h
  apply hx
  simp [f, ← Complex.sq_norm, h]


-- Dirichlet approximation gives unbounded return times with phase error at most 2π/q.
private theorem returns : ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧ ∀ n, 0 < q n ∧
    ‖e (Real.sqrt 2 * q n) - 1‖ ≤ (2 * Real.pi) / q n := by
  choose q hq hqn hdiff using fun n : ℕ ↦
    Real.exists_nat_abs_mul_sub_round_le (Real.sqrt 2) (Nat.succ_pos n)
  have hsmall : Tendsto (fun n : ℕ ↦ 1 / ((n+1 : ℕ) + 1 : ℝ)) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ ↦ ((n+1 : ℕ) + 1 : ℝ)) atTop atTop := by
      apply tendsto_atTop_mono (f := fun n : ℕ ↦ (n : ℝ)) _ tendsto_natCast_atTop_atTop
      intro n; push_cast; linarith
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp ht
  have ht (k : ℕ) : ∀ᶠ n in atTop, q n ≠ k := by
    rcases eq_or_ne k 0 with rfl | hk
    · exact .of_forall fun n ↦ (hq n).ne'
    have h := (irrational_sqrt_two.natCast_mul hk).ne_int (round ((k : ℝ) * Real.sqrt 2))
    filter_upwards [hsmall.eventually_lt_const (abs_pos.mpr (sub_ne_zero.mpr h))] with n hn heq
    exact hn.not_ge (heq ▸ hdiff n)
  refine ⟨q, tendsto_atTop.2 ?_, fun n ↦ ⟨hq n, ?_⟩⟩
  · intro k
    induction k with
    | zero => exact .of_forall fun _ ↦ Nat.zero_le _
    | succ k ih =>
      filter_upwards [ih, ht k] with n hn hn' using by omega
  · let z := (q n : ℝ) * Real.sqrt 2
    let j := round z
    have heq : e (Real.sqrt 2 * q n) = e (z - j) := by
      rw [mul_comm]
      change e z = _
      calc
        e z = e ((z - j) + j) := congrArg e (sub_add_cancel z (j : ℝ)).symm
        _ = _ := by rw [e_add, e_int, mul_one]
    have hnpos : (0 : ℝ) < q n := by exact_mod_cast hq n
    have hqd : (q n : ℝ) ≤ ((n+1 : ℕ) + 1 : ℝ) := by
      have h : (q n : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast hqn n
      linarith
    rw [heq]
    calc
      _ ≤ |2 * Real.pi * (z - j)| := by
        simpa [e, Real.fourierChar_apply, mul_comm Complex.I, Real.norm_eq_abs] using
          (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (z - j)))
      _ = 2 * Real.pi * |z - j| := by rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      _ ≤ 2 * Real.pi * (1 / q n) :=
        mul_le_mul_of_nonneg_left ((hdiff n).trans (one_div_le_one_div_of_le hnpos hqd))
          (by positivity)
      _ = _ := by ring

private theorem iterate_weight (u R : ℤ → ℝ) (hr : ∀ k, u (k + 1) = R k * u k)
    (k : ℤ) (n : ℕ) :
    u (k + n) = (∏ i ∈ Finset.range n, R (k + i)) * u k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, hr, ih, Finset.prod_range_succ]
    ring

-- Compare consecutive blocks of N factors. A relative error of exp(C/N) at each step
-- costs at most exp(C) over the entire block.
private theorem block_bound {u R : ℤ → ℝ} (hu : ∀ k, 0 ≤ u k) (hR : ∀ k, 0 ≤ R k)
    (hr : ∀ k, u (k + 1) = R k * u k) (N : ℕ) (hN : 0 < N) (C : ℝ)
    (hcomp : ∀ k : ℤ, R (-N + k) ≤ R k * Real.exp (C / N)) :
    u 0 ^ 2 ≤ Real.exp C * u N * u (-N) := by
  let A := ∏ i ∈ Finset.range N, R (i : ℤ)
  let B := ∏ i ∈ Finset.range N, R (-(N : ℤ) + i)
  have hA : u N = A * u 0 := by simpa [A] using iterate_weight u R hr 0 N
  have hB : u 0 = B * u (-N) := by simpa [B] using iterate_weight u R hr (-N) N
  have hBA : B ≤ A * Real.exp C := calc
    B ≤ ∏ i ∈ Finset.range N, (R (i : ℤ) * Real.exp (C / N)) :=
      Finset.prod_le_prod₀ (fun i _ ↦ hR _) (fun i _ ↦ hcomp _)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp [A, ← Real.exp_nat_mul, Nat.ne_of_gt hN, mul_div_cancel₀]
  calc
    u 0 ^ 2 = B * u (-(N : ℤ)) * u 0 := by rw [← hB, sq]
    _ ≤ A * Real.exp C * u (-(N : ℤ)) * u 0 := by gcongr <;> apply hu
    _ = _ := by rw [hA]; ring

private theorem orbit_zero {u R : ℤ → ℝ} (hu : ∀ k, 0 ≤ u k) (hR : ∀ k, 0 ≤ R k)
    (hr : ∀ k, u (k + 1) = R k * u k) (hd : Tendsto u cofinite (𝓝 0))
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) (hpos : ∀ n, 0 < q n) (C : ℝ)
    (hcomp : ∀ n (k : ℤ), R (-q n + k) ≤ R k * Real.exp (C / q n)) :
    u 0 = 0 := by
  have hq' : Tendsto (fun n ↦ (q n : ℤ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hq
  have h₁ := hd.comp (hq'.mono_right atTop_le_cofinite)
  have h₂ := hd.comp ((tendsto_neg_atTop_atBot.comp hq').mono_right atBot_le_cofinite)
  have hlim : Tendsto (fun n ↦ Real.exp C * u (q n) * u (-(q n : ℤ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul h₁).mul h₂
  have hsq := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
    (fun n ↦ block_bound hu hR hr (q n) (hpos n) C (hcomp n))
  nlinarith

private theorem trig_diff (a b c : ℂ) (y : ℝ) (j : ℤ) :
    ‖trig a b c (y + j) - trig a b c y‖ = ‖c‖ * ‖e (Real.sqrt 2 * j) - 1‖ := by
  have h : trig a b c (y + j) - trig a b c y =
      c * e (Real.sqrt 2 * y) * (e (Real.sqrt 2 * j) - 1) := by
    simp only [trig, mul_add, e_add, e_int, mul_one]
    ring
  rw [h, norm_mul, norm_mul, norm_e, mul_one]

private theorem gap_le (a b c : ℂ) (x : ℝ) (k : ℤ) :
    |‖a + b * e x‖ - ‖c‖| ≤ ‖trig a b c (x + k)‖ := by
  simpa [trig, e_add x k, e_int, norm_mul, norm_e, sub_neg_eq_add] using
    abs_norm_sub_norm_le (a + b * e x) (-(c * e (Real.sqrt 2 * (x + k))))

-- The gap bounds the multiplier away from zero along this entire orbit. At a return time
-- the additive phase error therefore gives a relative error for the two blocks.
private theorem separated_orbit (a b c : ℂ) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (hg : ‖a + b * e x‖ ≠ ‖c‖) (u : ℤ → ℝ) (hu : ∀ k, 0 ≤ u k)
    (hdec : Tendsto u cofinite (𝓝 0))
    (hr : ∀ k : ℤ, u (k + 1) = ‖trig a b c (x + k)‖ / D * u k) : u 0 = 0 := by
  let δ := |‖a + b * e x‖ - ‖c‖|
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hg)
  obtain ⟨q, hq, hret⟩ := returns
  let C := ‖c‖ * (2 * Real.pi) / δ
  apply orbit_zero hu (fun k ↦ div_nonneg (norm_nonneg _) hD.le) hr hdec hq
    (fun n ↦ (hret n).1) C
  intro n k
  let y := x + (-(q n : ℤ) + k : ℤ)
  have hy : y + ((q n : ℤ) : ℝ) = x + k := by dsimp [y]; push_cast; ring
  have hdiff := trig_diff a b c y (q n)
  rw [hy, Int.cast_natCast] at hdiff
  let v := ‖trig a b c (x + k)‖
  have hstep : ‖trig a b c y‖ ≤ v + ‖c‖ * (2 * Real.pi / q n) := calc
    _ ≤ ‖trig a b c y - trig a b c (x + k)‖ + v := norm_le_norm_sub_add _ _
    _ ≤ _ := by rw [norm_sub_rev, hdiff]; dsimp [v]; linarith [mul_le_mul_of_nonneg_left
                  (hret n).2 (norm_nonneg c)]
  have hN : (0 : ℝ) < q n := by exact_mod_cast (hret n).1
  have hC : 0 ≤ C / q n := by dsimp [C]; positivity
  have hscale : δ * (C / q n) = ‖c‖ * (2 * Real.pi / q n) := by
    dsimp [C]
    field_simp
  have hratio : ‖trig a b c y‖ ≤ v * Real.exp (C / q n) := calc
    _ ≤ v + δ * (C / q n) := hscale.symm ▸ hstep
    _ ≤ v + v * (C / q n) := by gcongr; exact gap_le a b c x k
    _ = v * (C / q n + 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (norm_nonneg _)
  change ‖trig a b c y‖ / D ≤ v / D * Real.exp (C / q n)
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hratio hD.le

private theorem periodic_pair (a b : ℂ) (s t : ℝ) (hst : s < t) :
    Periodic (fun x ↦ ‖a * e (s * x) + b * e (t * x)‖) (t - s)⁻¹ := by
  intro x
  have ht : t * (t - s)⁻¹ = s * (t - s)⁻¹ + 1 := by field_simp; ring
  have h1 : e (1 : ℝ) = 1 := by simpa using e_int 1
  simp only [mul_add, e_add, ht, h1, mul_one]
  rw [← mul_assoc, ← mul_assoc, ← add_mul, norm_mul, norm_e, mul_one]

private theorem lp_zero_of_norm {F : L2} (h : ∀ᵐ x, ‖F x‖ = 0) : F = 0 := by
  apply Lp.ext
  filter_upwards [h, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hz
  simpa using (norm_eq_zero.mp hx).trans hz.symm

private theorem recurrence_zero_periodic (F : L2) (P : ℝ → ℂ) (D T : ℝ)
    (hD : 0 < D) (hT : 0 < T) (hp : Periodic (fun x ↦ ‖P x‖) T)
    (hn : ∀ᵐ x, P x ≠ 0) (hr : ∀ᵐ x, ‖F (x + 1)‖ = ‖P x‖ / D * ‖F x‖) : F = 0 := by
  let weight (x : ℝ) := (ENNReal.ofReal (‖P x‖ / D)) ^ 2
  have hper : Periodic weight T := fun x ↦ by simp only [weight, hp x]
  have hfin : ∀ᵐ x, weight x ≠ 0 ∧ weight x ≠ ∞ := by
    filter_upwards [hn] with x hx
    have hpos : 0 < ‖P x‖ / D := div_pos (norm_pos_iff.mpr hx) hD
    simp [weight, hpos.not_ge]
  have hstep : ∀ᵐ x, ‖F (x + 1)‖ₑ ^ 2 = weight x * ‖F x‖ₑ ^ 2 := by
    filter_upwards [hr] with x hx
    unfold weight
    rw [← mul_pow]
    apply congrArg (fun t : ℝ≥0∞ ↦ t ^ 2)
    simpa only [ofReal_norm, ENNReal.ofReal_mul (div_nonneg (norm_nonneg _) hD.le)] using
      congrArg ENNReal.ofReal hx
  have hzero := no_periodic_weight hT ((Lp.aestronglyMeasurable F).eNorm.pow_const 2)
    (square_integral_fin F) hper hfin hstep
  apply lp_zero_of_norm
  filter_upwards [hzero] with x hx
  change ‖F x‖ₑ ^ 2 = 0 at hx
  simpa using hx

-- With a missing constant or frequency-one term the modulus is periodic. Otherwise the
-- gap estimate applies on almost every orbit.
private theorem all_coefficients (F : L2) (hF : F ≠ 0) (a b c d : ℂ)
    (hr : ∀ᵐ x, trig a b c x * F x + d * F (x + 1) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  by_cases habc : a = 0 ∧ b = 0 ∧ c = 0
  · obtain ⟨rfl, rfl, rfl⟩ := habc
    refine ⟨rfl, rfl, rfl, ?_⟩
    by_contra hd
    apply hF
    apply lp_zero_of_norm
    have hz : ∀ᵐ x : ℝ, F (x + 1) = 0 := by
      simpa [trig, hd] using hr
    filter_upwards [(measurePreserving_add_right volume (-1 : ℝ)).quasiMeasurePreserving.ae
      (p := fun x ↦ F (x + 1) = 0) hz] with x hx
    simpa using congrArg norm hx
  exfalso
  apply hF
  have hne := trig_ae_ne habc
  by_cases hd : d = 0
  · apply lp_zero_of_norm
    filter_upwards [hr, hne] with x hx hn
    simpa [hd, hn] using hx
  have hD := norm_pos_iff.mpr hd
  have hs : ∀ᵐ x, ‖F (x + 1)‖ = ‖trig a b c x‖ / ‖d‖ * ‖F x‖ := by
    filter_upwards [hr] with x hx
    have heq : d * F (x + 1) = -(trig a b c x * F x) := eq_neg_of_add_eq_zero_left
      ((add_comm _ _).trans hx)
    have hh := congrArg norm heq
    simp only [norm_mul, norm_neg] at hh
    field_simp
    linarith
  by_cases ha : a = 0
  · subst a
    have hα := Real.one_lt_sqrt_two
    apply recurrence_zero_periodic F _ ‖d‖ (Real.sqrt 2 - 1)⁻¹ hD (by positivity) _ hne hs
    simpa [trig] using periodic_pair b c 1 (Real.sqrt 2) hα
  by_cases hb : b = 0
  · subst b
    have hα : 0 < Real.sqrt 2 := by positivity
    apply recurrence_zero_periodic F _ ‖d‖ (Real.sqrt 2)⁻¹ hD (by positivity) _ hne hs
    simpa [trig, show e 0 = 1 by simp [e]] using periodic_pair a c 0 (Real.sqrt 2) hα
  apply lp_zero_of_norm
  have hshift (k : ℤ) := (measurePreserving_add_right volume (k : ℝ)).quasiMeasurePreserving.ae
    (p := fun x ↦ ‖F (x + 1)‖ = ‖trig a b c x‖ / ‖d‖ * ‖F x‖) hs
  filter_upwards [ae_all_iff.2 hshift, unequal_norm_ae a b c ha hb, orbit_decay F] with x hx hg hdec
  have h := separated_orbit a b c ‖d‖ hD x hg (fun k ↦ ‖F (x + k)‖) (fun _ ↦ norm_nonneg _)
    hdec (fun k ↦ by simpa [add_assoc] using hx k)
  simpa using h

end

/--
**A four-function case of the HRT conjecture holds.** For every function
$g : \mathbb{R} \to \mathbb{C}$ in $L^2(\mathbb{R})$ that is not zero almost everywhere, the four
functions $g(x)$, $g(x - 1)$, $g(x - \sqrt{2})$ and $e^{2\pi i x} g(x)$ are linearly independent:
whenever $c_0, c_1, c_2, c_3 \in \mathbb{C}$ satisfy
$c_0 g(x) + c_1 g(x - 1) + c_2 g(x - \sqrt{2}) + c_3 e^{2\pi i x} g(x) = 0$ for almost every
$x \in \mathbb{R}$, then $c_0 = c_1 = c_2 = c_3 = 0$.

This case was proved by Demeter (Theorem 1.4(b)); Liu (Theorem 1.1(b)) states it for the
time-frequency configuration $\{(0,0),(a,0),(b,0),(0,1)\}$ with $a = 1$ and $b = \sqrt{2}$.

Source: Ciprian Demeter, Linear independence of time frequency
translates for special configurations, Math. Res. Lett. 17 (2010) 761-779, arXiv:1006.0732,
https://arxiv.org/abs/1006.0732; Wencai Liu, Proof of the HRT conjecture for almost every (1,3)
configuration, J. Fourier Anal. Appl. (2019), arXiv:1609.08230,
https://arxiv.org/abs/1609.08230. Moved from `OpenConjectures/Analysis/FourFunctionHRT`.
-/
public theorem conjecture_holds : conjecture := by
  intro g hg hn a b c d h
  obtain ⟨F, hF, hr⟩ := transformed_relation hg hn a b c d h
  exact all_coefficients F hF a b c d hr

end MathlibExt.Analysis.FourFunctionHRTWanted
