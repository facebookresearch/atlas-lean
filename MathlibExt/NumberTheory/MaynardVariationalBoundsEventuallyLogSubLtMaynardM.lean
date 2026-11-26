/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GPYMaynardSieveReduction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Order.Fin.Tuple
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Growth of Maynard's variational quantity

Lower bounds for `MathlibExt.NumberTheory.GPYMaynard.maynardM` obtained from truncated
product profiles.

Source: J. Maynard, *Small gaps between primes*, Ann. of Math. 181 (2015), 383-413;
numbering of arXiv:1311.4600v3, Proposition 4.3(3).
-/

@[expose] public section

namespace WantedExt.NumberTheory.MaynardVariationalBounds

open MathlibExt.NumberTheory.GPYMaynard MeasureTheory Set Filter Topology

/-- Lebesgue measure on `[0, 1]`. -/
private noncomputable abbrev μ₁ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

private theorem isProbabilityMeasure_μ₁ : IsProbabilityMeasure μ₁ :=
  ⟨by simp [Real.volume_Icc]⟩

attribute [local instance] isProbabilityMeasure_μ₁

private theorem restrict_Icc_eq_pi (N : ℕ) :
    volume.restrict (Icc (0 : Fin N → ℝ) 1) = Measure.pi fun _ => μ₁ := by
  have h : Icc (0 : Fin N → ℝ) 1 = Set.univ.pi fun _ => Icc (0 : ℝ) 1 := by
    rw [← Set.pi_univ_Icc]
    rfl
  rw [h, volume_pi, Measure.restrict_pi_pi]

private theorem measurePreserving_removeNth {n : ℕ} (m : Fin (n + 1)) :
    MeasurePreserving (fun x : Fin (n + 1) → ℝ => Fin.removeNth m x)
      (Measure.pi fun _ => μ₁) (Measure.pi fun _ => μ₁) :=
  measurePreserving_snd.comp (measurePreserving_piFinSuccAbove (fun _ => μ₁) m)

private theorem integral_comp_removeNth {n : ℕ} (m : Fin (n + 1)) {K : (Fin n → ℝ) → ℝ}
    (hK : AEStronglyMeasurable K (Measure.pi fun _ => μ₁)) :
    ∫ x, K (Fin.removeNth m x) ∂(Measure.pi fun _ => μ₁) = ∫ y, K y ∂(Measure.pi fun _ => μ₁) := by
  have h := measurePreserving_removeNth m
  rw [← h.map_eq] at hK
  rw [← h.map_eq]
  exact (integral_map h.measurable.aemeasurable hK).symm

/-- Measurability of a line integral in the direction `m`. -/
private theorem stronglyMeasurable_lineIntegral {n : ℕ} (m : Fin (n + 1))
    {H : (Fin (n + 1) → ℝ) → ℝ} (hH : Measurable H) :
    StronglyMeasurable fun x : Fin (n + 1) → ℝ => ∫ t, H (Function.update x m t) ∂μ₁ :=
  StronglyMeasurable.integral_prod_right'
    (f := fun p : (Fin (n + 1) → ℝ) × ℝ => H (Function.update p.1 m p.2))
    (hH.comp measurable_update').stronglyMeasurable

/-- Fubini in the direction `m` for a bounded measurable function on the cube. -/
private theorem integral_lineIntegral {n : ℕ} (m : Fin (n + 1)) {G : (Fin (n + 1) → ℝ) → ℝ}
    (hG : Measurable G) {C : ℝ} (hC : ∀ x, |G x| ≤ C) :
    ∫ x, (∫ t, G (Function.update x m t) ∂μ₁) ∂(Measure.pi fun _ => μ₁) =
      ∫ x, G x ∂(Measure.pi fun _ => μ₁) := by
  set K : (Fin n → ℝ) → ℝ := fun y => ∫ t, G (Fin.insertNth m t y) ∂μ₁ with hK
  have hKm : StronglyMeasurable K :=
    StronglyMeasurable.integral_prod_right'
      (f := fun p : (Fin n → ℝ) × ℝ => G (Fin.insertNth m p.2 p.1))
      (hG.comp ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) m).symm.measurable.comp
        measurable_swap)).stronglyMeasurable
  have h1 : (fun x : Fin (n + 1) → ℝ => ∫ t, G (Function.update x m t) ∂μ₁) =
      fun x => K (Fin.removeNth m x) := by
    funext x
    simp only [hK, Fin.insertNth_removeNth]
  rw [h1, integral_comp_removeNth m hKm.aestronglyMeasurable]
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ₁) m
  have h2 := hmp.integral_comp'
    (fun p => G ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) m).symm p))
  simp only [MeasurableEquiv.symm_apply_apply] at h2
  rw [h2, integral_prod_symm]
  · rfl
  · refine Integrable.of_bound ((hG.comp (MeasurableEquiv.measurable _)).aestronglyMeasurable) C
      (ae_of_all _ fun p => ?_)
    simpa [Real.norm_eq_abs] using hC _

/-! ### `J_k^{(m)} ≤ I_k`, so the ratios defining `M_k` are bounded -/

/-- For `f` bounded and measurable, `(∫₀¹ f)² ≤ ∫₀¹ f²`. -/
private theorem sq_integral_le {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ t, |f t| ≤ C) :
    (∫ t, f t ∂μ₁) ^ 2 ≤ ∫ t, f t ^ 2 ∂μ₁ := by
  have hfi : Integrable f μ₁ := Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun t => by simpa [Real.norm_eq_abs] using hC t)
  have hgi : Integrable ((fun x : ℝ => x ^ 2) ∘ f) μ₁ := Integrable.of_bound
    (hf.pow_const 2).aestronglyMeasurable (C ^ 2) (ae_of_all _ fun t => by
      simp only [Function.comp, Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC t) 2)
  exact (even_two.convexOn_pow : ConvexOn ℝ univ fun x : ℝ => x ^ 2).map_integral_le
    (continuous_pow 2).continuousOn isClosed_univ (ae_of_all _ fun _ => mem_univ _) hfi hgi

private theorem intervalIntegral_eq_μ₁ (f : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..1, f t = ∫ t, f t ∂μ₁ := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]

private theorem maynardJ_eq {n : ℕ} (m : Fin (n + 1)) (F : (Fin (n + 1) → ℝ) → ℝ) :
    maynardJ (n + 1) m F =
      ∫ x, (∫ t, F (Function.update x m t) ∂μ₁) ^ 2 ∂(Measure.pi fun _ => μ₁) := by
  unfold maynardJ
  simp_rw [intervalIntegral_eq_μ₁]
  rw [restrict_Icc_eq_pi]

private theorem maynardI_eq (N : ℕ) (F : (Fin N → ℝ) → ℝ) :
    maynardI N F = ∫ x, F x ^ 2 ∂(Measure.pi fun _ => μ₁) := by
  unfold maynardI
  rw [restrict_Icc_eq_pi]

/-- **`J_k^{(m)}(F) ≤ I_k(F)`** for bounded measurable `F` (Cauchy–Schwarz in the `m`-th
coordinate, then Fubini). -/
private theorem maynardJ_le_maynardI {n : ℕ} (m : Fin (n + 1)) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : Measurable F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) :
    maynardJ (n + 1) m F ≤ maynardI (n + 1) F := by
  rw [maynardJ_eq, maynardI_eq]
  have hC2 : ∀ x, |F x ^ 2| ≤ C ^ 2 := fun x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC x) 2
  rw [← integral_lineIntegral m (hF.pow_const 2) hC2]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) ?_ (ae_of_all _ fun x => ?_)
  · refine Integrable.of_bound
      (stronglyMeasurable_lineIntegral m (hF.pow_const 2)).aestronglyMeasurable (C ^ 2)
      (ae_of_all _ fun x => ?_)
    have h := norm_integral_le_of_norm_le_const (μ := μ₁)
      (f := fun t => F (Function.update x m t) ^ 2) (C := C ^ 2)
      (ae_of_all _ fun t => by simpa [Real.norm_eq_abs] using hC2 _)
    simpa using h
  · exact sq_integral_le (hF.comp (measurable_update x)) (fun t => hC _)

private theorem maynardRatio_le {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : IsMaynardProfile (n + 1) F) : maynardRatio (n + 1) F ≤ n + 1 := by
  have hI := maynardI_pos hF
  obtain ⟨hFm, ⟨C, hC⟩, -, -, -⟩ := hF
  unfold maynardRatio
  rw [div_le_iff₀ hI]
  calc ∑ m, maynardJ (n + 1) m F ≤ ∑ _m : Fin (n + 1), maynardI (n + 1) F :=
        Finset.sum_le_sum fun m _ => maynardJ_le_maynardI m hFm hC
    _ = (n + 1) * maynardI (n + 1) F := by simp

private theorem bddAbove_maynardRatio (n : ℕ) :
    BddAbove (maynardRatio (n + 1) '' {F | IsMaynardProfile (n + 1) F}) := by
  refine ⟨n + 1, ?_⟩
  rintro _ ⟨F, hF, rfl⟩
  exact maynardRatio_le hF


private theorem pi_density (N : ℕ) {w : ℝ → ℝ} (hw0 : ∀ t, 0 ≤ w t) (hwi : Integrable w μ₁)
    [IsProbabilityMeasure (μ₁.withDensity (fun t => ENNReal.ofReal (w t)))] :
    Measure.pi (fun _ : Fin N => μ₁.withDensity (fun t => ENNReal.ofReal (w t))) =
      (Measure.pi (fun _ : Fin N => μ₁)).withDensity
        (fun x => ENNReal.ofReal (∏ i, w (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg]
    · congr 1
      funext i
      rw [withDensity_apply _ (hs i), ← ofReal_integral_eq_lintegral_ofReal
        hwi.integrableOn (ae_of_all _ hw0)]
    · intro i _
      exact integral_nonneg hw0
  · exact Integrable.fintype_prod fun _ => hwi.integrableOn
  · exact ae_of_all _ fun x => Finset.prod_nonneg fun i _ => hw0 (x i)

private theorem probability_density {w : ℝ → ℝ} (hw0 : ∀ t, 0 ≤ w t)
    (hwi : Integrable w μ₁) (hw1 : ∫ t, w t ∂μ₁ = 1) :
    IsProbabilityMeasure (μ₁.withDensity (fun t => ENNReal.ofReal (w t))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hwi (ae_of_all _ hw0), hw1, ENNReal.ofReal_one]

private theorem density_support {w : ℝ → ℝ} (hw : Measurable w) {T : ℝ}
    (hs : ∀ t, w t ≠ 0 → t ∈ Icc 0 T) :
    ∀ᵐ t ∂μ₁.withDensity (fun t => ENNReal.ofReal (w t)), t ∈ Icc 0 T := by
  have hm : Measurable (fun t => ENNReal.ofReal (w t)) := ENNReal.measurable_ofReal.comp hw
  rw [ae_withDensity_iff hm]
  exact ae_of_all _ fun t ht => hs t (fun h => ht (by simp [h]))

private theorem integral_density {w : ℝ → ℝ} (hw : Measurable w)
    (hw0 : ∀ t, 0 ≤ w t) (f : ℝ → ℝ) :
    ∫ t, f t ∂μ₁.withDensity (fun t => ENNReal.ofReal (w t)) =
      ∫ t, w t * f t ∂μ₁ := by
  have hm : Measurable (fun t => ENNReal.ofReal (w t)) := ENNReal.measurable_ofReal.comp hw
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]

private theorem simplex_mass (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hX : MemLp (id : ℝ → ℝ) 2 ν) (T : ℝ)
    (hgap : 0 < 1 - T - N * ∫ t, t ∂ν) :
    1 - N * ProbabilityTheory.variance id ν / (1 - T - N * ∫ t, t ∂ν) ^ 2 ≤
      (Measure.pi (fun _ : Fin N => ν)).real {x | ∑ i, x i ≤ 1 - T} := by
  let S : (Fin N → ℝ) → ℝ := fun x => ∑ i, x i
  have hXi (i : Fin N) : MemLp (fun x : Fin N → ℝ => x i) 2
      (Measure.pi (fun _ => ν)) := hX.comp_measurePreserving (measurePreserving_eval _ i)
  have hS : MemLp S 2 (Measure.pi (fun _ => ν)) := memLp_finsetSum _ fun i _ => hXi i
  have hmean : ∫ x, S x ∂Measure.pi (fun _ => ν) = N * ∫ t, t ∂ν := by
    rw [integral_finsetSum]
    · simp_rw [integral_eval (μ := fun _ : Fin N => ν)]
      simp
    · exact fun i _ => (hXi i).integrable (by norm_num)
  have hvar : ProbabilityTheory.variance S (Measure.pi (fun _ => ν)) =
      N * ProbabilityTheory.variance id ν := by
    simpa [S, Finset.sum_fn] using ProbabilityTheory.variance_sum_pi (ι := Fin N) (fun _ => hX)
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hS hgap
  rw [hmean, hvar] at hcheb
  have hnonneg : 0 ≤ N * ProbabilityTheory.variance id ν /
      (1 - T - N * ∫ t, t ∂ν) ^ 2 := div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (ProbabilityTheory.variance_nonneg _ _)) (sq_nonneg _)
  have hreal : (Measure.pi (fun _ : Fin N => ν)).real
      {x | 1 - T - N * ∫ t, t ∂ν ≤ |S x - N * ∫ t, t ∂ν|} ≤
        N * ProbabilityTheory.variance id ν / (1 - T - N * ∫ t, t ∂ν) ^ 2 := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb).trans_eq
      (ENNReal.toReal_ofReal hnonneg)
  have hbad : (Measure.pi (fun _ : Fin N => ν)).real {x | 1 - T < S x} ≤
      N * ProbabilityTheory.variance id ν / (1 - T - N * ∫ t, t ∂ν) ^ 2 := by
    refine (measureReal_mono ?_).trans hreal
    intro x hx
    change 1 - T < S x at hx
    exact (by linarith : 1 - T - N * ∫ t, t ∂ν ≤ S x - N * ∫ t, t ∂ν).trans
      (le_abs_self _)
  have hm : MeasurableSet {x | 1 - T < S x} := measurableSet_lt measurable_const
    (by fun_prop)
  have heq : {x : Fin N → ℝ | S x ≤ 1 - T} = {x | 1 - T < S x}ᶜ := by
    ext x
    simp
  rw [heq, measureReal_compl (measurableSet_lt measurable_const (by fun_prop)), probReal_univ]
  linarith

private noncomputable def factor (c T t : ℝ) : ℝ :=
  (Icc 0 T).indicator (fun t => 1 / (1 + c * t)) t

private theorem measurable_factor (c T : ℝ) : Measurable (factor c T) := by
  unfold factor
  exact (by fun_prop : Measurable (fun t : ℝ => 1 / (1 + c * t))).indicator measurableSet_Icc

private theorem factor_bounds {c T : ℝ} (hc : 0 < c) (t : ℝ) :
    0 ≤ factor c T t ∧ factor c T t ≤ 1 := by
  unfold factor
  by_cases ht : t ∈ Icc 0 T
  · rw [indicator_of_mem ht]
    have hct := mul_nonneg hc.le ht.1
    exact ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith)⟩
  · simp [ht]

private theorem factor_support {c T : ℝ} {t : ℝ} (ht : factor c T t ≠ 0) :
    t ∈ Icc 0 T := by
  by_contra h
  exact ht (indicator_of_notMem h _)

private theorem integral_factor_restrict {c T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    ∫ t, factor c T t ∂μ₁ = ∫ t in (0 : ℝ)..T, 1 / (1 + c * t) := by
  unfold factor μ₁
  rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict
    measurableSet_Icc, inter_eq_left.mpr (Icc_subset_Icc le_rfl hT1),
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hT0]

private noncomputable def prodProfile (N : ℕ) (g : ℝ → ℝ) (x : Fin N → ℝ) : ℝ :=
  {x : Fin N → ℝ | ∑ i, x i ≤ 1}.indicator (fun x => ∏ i, g (x i)) x

private theorem measurable_prodProfile (N : ℕ) {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (prodProfile N g) := by
  unfold prodProfile
  exact (by fun_prop : Measurable (fun x : Fin N → ℝ => ∏ i, g (x i))).indicator
    (measurableSet_le (by fun_prop) measurable_const)

private theorem prodProfile_bounds (N : ℕ) {g : ℝ → ℝ}
    (hg : ∀ t, 0 ≤ g t ∧ g t ≤ 1) (x : Fin N → ℝ) :
    0 ≤ prodProfile N g x ∧ prodProfile N g x ≤ 1 := by
  unfold prodProfile
  by_cases hx : ∑ i, x i ≤ 1
  · rw [indicator_of_mem hx]
    exact ⟨Finset.prod_nonneg fun i _ => (hg _).1,
      Finset.prod_le_one₀ (fun i _ => (hg _).1) (fun i _ => (hg _).2)⟩
  · simp [hx]

private theorem prodProfile_support (N : ℕ) {g : ℝ → ℝ} {T : ℝ}
    (hg : ∀ t, g t ≠ 0 → t ∈ Icc 0 T) {x : Fin N → ℝ} (hx : x ∉ maynardSimplex N) :
    prodProfile N g x = 0 := by
  unfold prodProfile
  by_cases hs : ∑ i, x i ≤ 1
  · rw [indicator_of_mem hs]
    by_contra hp
    apply hx
    refine ⟨fun i => (hg (x i) ?_).1, hs⟩
    intro hi
    exact hp (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  · exact indicator_of_notMem hs _

private theorem prodProfile_insertNth {n : ℕ} (m : Fin (n + 1)) (g : ℝ → ℝ)
    (t : ℝ) (y : Fin n → ℝ) :
    prodProfile (n + 1) g (Fin.insertNth m t y) =
      if t + ∑ i, y i ≤ 1 then g t * ∏ i, g (y i) else 0 := by
  unfold prodProfile
  simp only [indicator_apply, mem_ofPred_eq, Fin.sum_univ_succAbove _ m,
    Fin.prod_univ_succAbove _ m, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

private theorem integral_prodProfile_insertNth {n : ℕ} (m : Fin (n + 1)) {g : ℝ → ℝ}
    {T : ℝ} (hg : ∀ t, g t ≠ 0 → t ∈ Icc 0 T) {y : Fin n → ℝ}
    (hy : ∑ i, y i ≤ 1 - T) :
    ∫ t, prodProfile (n + 1) g (Fin.insertNth m t y) ∂μ₁ =
      (∫ t, g t ∂μ₁) * ∏ i, g (y i) := by
  have heq : ∀ t, prodProfile (n + 1) g (Fin.insertNth m t y) = g t * ∏ i, g (y i) := by
    intro t
    rw [prodProfile_insertNth]
    by_cases ht : g t = 0
    · simp [ht]
    · rw [ite_eq_left (by linarith [(hg t ht).2])]
  simp_rw [heq]
  exact integral_mul_const _ _

private theorem weighted_mass (N : ℕ) {g : ℝ → ℝ} (hg : Measurable g)
    (hg1 : ∀ t, 0 ≤ g t ∧ g t ≤ 1) {v : ℝ} (hv : 0 < v)
    (hv_eq : ∫ t, g t ^ 2 ∂μ₁ = v) (s : Set (Fin N → ℝ)) (hs : MeasurableSet s) :
    ∫ x in s, ∏ i, g (x i) ^ 2 ∂Measure.pi (fun _ => μ₁) =
      v ^ N * (Measure.pi (fun _ : Fin N =>
        μ₁.withDensity (fun t => ENNReal.ofReal (g t ^ 2 / v)))).real s := by
  have hw0 : ∀ t, 0 ≤ g t ^ 2 / v := fun t => div_nonneg (sq_nonneg _) hv.le
  have hwi : Integrable (fun t => g t ^ 2 / v) μ₁ := by
    refine Integrable.of_bound ((hg.pow_const 2).div_const v).aestronglyMeasurable (1 / v)
      (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 t)]
    gcongr
    exact pow_le_one₀ (hg1 t).1 (hg1 t).2
  have hw1 : ∫ t, g t ^ 2 / v ∂μ₁ = 1 := by
    rw [integral_div, hv_eq, div_self hv.ne']
  let := probability_density hw0 hwi hw1
  rw [pi_density N hw0 hwi, withDensity_real_apply_eq_integral]
  · simp_rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => hw0 _)]
    simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      integral_div]
    exact (mul_div_cancel₀ _ (pow_ne_zero _ hv.ne')).symm
  · exact (ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable
  · exact ae_of_all _ fun _ _ => ENNReal.ofReal_lt_top
  · exact hs.nullMeasurableSet

private theorem maynardI_prodProfile_le (N : ℕ) {g : ℝ → ℝ} (hg : Measurable g)
    (hg1 : ∀ t, 0 ≤ g t ∧ g t ≤ 1) :
    maynardI N (prodProfile N g) ≤ (∫ t, g t ^ 2 ∂μ₁) ^ N := by
  have heq : (∫ x : Fin N → ℝ, ∏ i, g (x i) ^ 2 ∂Measure.pi (fun _ => μ₁)) =
      (∫ t, g t ^ 2 ∂μ₁) ^ N := by
    simpa using integral_fintype_prod_eq_pow (ι := Fin N) (μ := μ₁) (fun t => g t ^ 2)
  rw [maynardI_eq, ← heq]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) ?_
    (ae_of_all _ fun x => ?_)
  · refine Integrable.of_bound
      (by fun_prop : Measurable (fun x : Fin N → ℝ => ∏ i, g (x i) ^ 2)).aestronglyMeasurable
      1 (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ => sq_nonneg _)]
    exact Finset.prod_le_one₀ (fun i _ => sq_nonneg _) fun i _ =>
      pow_le_one₀ (hg1 _).1 (hg1 _).2
  · dsimp only
    unfold prodProfile
    by_cases hx : ∑ i, x i ≤ 1
    · rw [indicator_of_mem hx, Finset.prod_pow]
    · rw [indicator_of_notMem hx, zero_pow (by decide)]
      exact Finset.prod_nonneg fun i _ => sq_nonneg _

private theorem factor_integral {c T : ℝ} (hc : 0 < c) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    ∫ t, factor c T t ∂μ₁ = Real.log (1 + c * T) / c := by
  rw [integral_factor_restrict hT0 hT1,
    intervalIntegral.integral_comp_add_mul (fun t : ℝ => 1 / t) hc.ne' 1]
  simp only [mul_zero, add_zero, smul_eq_mul]
  rw [integral_one_div_of_pos (by norm_num) (by positivity), div_one, inv_mul_eq_div]

private theorem factor_moment_restrict {c T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1)
    (f : ℝ → ℝ) :
    ∫ t, f t * factor c T t ^ 2 ∂μ₁ =
      ∫ t in (0 : ℝ)..T, f t * (1 / (1 + c * t)) ^ 2 := by
  have heq : (fun t => f t * factor c T t ^ 2) =
      (Icc 0 T).indicator (fun t => f t * (1 / (1 + c * t)) ^ 2) := by
    ext t
    by_cases ht : t ∈ Icc 0 T <;> simp [factor, ht]
  rw [heq, integral_indicator measurableSet_Icc]
  unfold μ₁
  rw [Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr (Icc_subset_Icc le_rfl hT1), integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hT0]

private theorem integral_inv_sq {B : ℝ} (hB : 1 ≤ B) :
    ∫ t in (1 : ℝ)..B, (1 / t) ^ 2 = 1 - 1 / B := by
  have h0 : (0 : ℝ) ∉ uIcc 1 B := by simp [uIcc_of_le hB]
  have heq : (fun t : ℝ => (1 / t) ^ 2) = fun t => t ^ (-2 : ℤ) := by
    ext t
    simp
  rw [heq, integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  norm_num
  ring

private theorem factor_sq_integral {c T : ℝ} (hc : 0 < c) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    ∫ t, factor c T t ^ 2 ∂μ₁ = (1 - 1 / (1 + c * T)) / c := by
  have h := factor_moment_restrict (c := c) hT0 hT1 (fun _ => 1)
  simp only [one_mul] at h
  rw [h, intervalIntegral.integral_comp_add_mul (fun t : ℝ => (1 / t) ^ 2) hc.ne' 1]
  simp only [mul_zero, add_zero, smul_eq_mul]
  rw [integral_inv_sq (by nlinarith), inv_mul_eq_div]

private theorem integrable_factor {c T : ℝ} (hc : 0 < c) : Integrable (factor c T) μ₁ := by
  refine Integrable.of_bound (measurable_factor c T).aestronglyMeasurable 1
    (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (factor_bounds hc t).1]
  exact (factor_bounds hc t).2

private theorem integrable_factor_sq {c T : ℝ} (hc : 0 < c) :
    Integrable (fun t => factor c T t ^ 2) μ₁ := by
  refine Integrable.of_bound ((measurable_factor c T).pow_const 2).aestronglyMeasurable 1
    (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_one₀ (factor_bounds hc t).1 (factor_bounds hc t).2

private theorem factor_first_moment {c T : ℝ} (hc : 0 < c) :
    ∫ t, t * factor c T t ^ 2 ∂μ₁ =
      ((∫ t, factor c T t ∂μ₁) - ∫ t, factor c T t ^ 2 ∂μ₁) / c := by
  have heq : ∀ t, t * factor c T t ^ 2 =
      (factor c T t - factor c T t ^ 2) / c := by
    intro t
    by_cases ht : t ∈ Icc 0 T
    · simp only [factor, indicator_of_mem ht]
      have hn : 1 + c * t ≠ 0 := (by nlinarith [ht.1] : 0 < 1 + c * t).ne'
      field_simp
      ring
    · simp [factor, ht]
  simp_rw [heq]
  rw [integral_div, integral_sub (integrable_factor hc) (integrable_factor_sq hc)]

private theorem factor_second_moment_le {c T : ℝ} (hc : 0 < c)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    ∫ t, t ^ 2 * factor c T t ^ 2 ∂μ₁ ≤ T / c ^ 2 := by
  have heq : (∫ t, (Icc 0 T).indicator (fun _ => 1 / c ^ 2) t ∂μ₁) = T / c ^ 2 := by
    rw [integral_indicator_const _ measurableSet_Icc]
    unfold μ₁
    rw [measureReal_def, Measure.restrict_apply measurableSet_Icc,
      inter_eq_left.mpr (Icc_subset_Icc le_rfl hT1), Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal hT0, smul_eq_mul, mul_one_div]
  rw [← heq]
  refine integral_mono_of_nonneg (ae_of_all _ fun t => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    ((integrable_const _).indicator measurableSet_Icc) (ae_of_all _ fun t => ?_)
  by_cases ht : t ∈ Icc 0 T
  · simp only [factor, indicator_of_mem ht]
    have hct : 0 ≤ c * t := mul_nonneg hc.le ht.1
    have hratio : t / (1 + c * t) ≤ 1 / c := by
      rw [div_le_div_iff₀ (by positivity) hc]
      linarith
    have hs := pow_le_pow_left₀ (div_nonneg ht.1 (by linarith : 0 ≤ 1 + c * t)) hratio 2
    convert hs using 1 <;> ring
  · simp [factor, ht]

private theorem maynardJ_prodProfile_ge {n : ℕ} (m : Fin (n + 1)) {g : ℝ → ℝ}
    (hg : Measurable g) (hg1 : ∀ t, 0 ≤ g t ∧ g t ≤ 1) {T : ℝ}
    (hsup : ∀ t, g t ≠ 0 → t ∈ Icc 0 T) :
    (∫ t, g t ∂μ₁) ^ 2 *
      (∫ y in {y : Fin n → ℝ | ∑ i, y i ≤ 1 - T}, ∏ i, g (y i) ^ 2
        ∂Measure.pi (fun _ => μ₁)) ≤ maynardJ (n + 1) m (prodProfile (n + 1) g) := by
  let s : Set (Fin n → ℝ) := {y | ∑ i, y i ≤ 1 - T}
  let K : (Fin n → ℝ) → ℝ := s.indicator
    (fun y => (∫ t, g t ∂μ₁) ^ 2 * ∏ i, g (y i) ^ 2)
  have hs : MeasurableSet s := measurableSet_le (by fun_prop) measurable_const
  have hK : Measurable K := (by fun_prop : Measurable
    (fun y : Fin n → ℝ => (∫ t, g t ∂μ₁) ^ 2 * ∏ i, g (y i) ^ 2)).indicator hs
  have heq : (∫ x, K (Fin.removeNth m x) ∂Measure.pi (fun _ => μ₁)) =
      (∫ t, g t ∂μ₁) ^ 2 * ∫ y in s, ∏ i, g (y i) ^ 2 ∂Measure.pi (fun _ => μ₁) := by
    rw [integral_comp_removeNth m hK.aestronglyMeasurable]
    change (∫ y, s.indicator (fun y => (∫ t, g t ∂μ₁) ^ 2 * ∏ i, g (y i) ^ 2) y
      ∂Measure.pi (fun _ => μ₁)) = _
    rw [integral_indicator hs, integral_const_mul]
  rw [maynardJ_eq, ← heq]
  have hF : Measurable (prodProfile (n + 1) g) := measurable_prodProfile _ hg
  refine integral_mono_of_nonneg (ae_of_all _ fun x => ?_) ?_ (ae_of_all _ fun x => ?_)
  · by_cases hx : Fin.removeNth m x ∈ s
    · simp only [K, indicator_of_mem hx]
      exact mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun i _ => sq_nonneg _)
    · simp [K, hx]
  · refine Integrable.of_bound ((stronglyMeasurable_lineIntegral m hF).pow 2).aestronglyMeasurable
      1 (ae_of_all _ fun x => ?_)
    have hn : ‖∫ t, prodProfile (n + 1) g (Function.update x m t) ∂μ₁‖ ≤ 1 := by
      simpa using norm_integral_le_of_norm_le_const (μ := μ₁)
        (f := fun t => prodProfile (n + 1) g (Function.update x m t)) (C := 1)
        (ae_of_all _ fun t => by
          rw [Real.norm_eq_abs, abs_of_nonneg (prodProfile_bounds _ hg1 _).1]
          exact (prodProfile_bounds _ hg1 _).2)
    simpa [Real.norm_eq_abs, abs_pow] using pow_le_one₀ (norm_nonneg _) hn (n := 2)
  · dsimp only
    change K (Fin.removeNth m x) ≤ _
    by_cases hx : Fin.removeNth m x ∈ s
    · rw [show K (Fin.removeNth m x) = (∫ t, g t ∂μ₁) ^ 2 *
          ∏ i, g (Fin.removeNth m x i) ^ 2 from indicator_of_mem hx _]
      have hline := integral_prodProfile_insertNth m hsup hx
      simp only [Fin.insertNth_removeNth] at hline
      rw [hline, mul_pow, Finset.prod_pow]
    · rw [show K (Fin.removeNth m x) = 0 from indicator_of_notMem hx _]
      exact sq_nonneg _

private theorem lt_maynardM_of_prodProfile (n : ℕ) {g : ℝ → ℝ} (hg : Measurable g)
    (hg1 : ∀ t, 0 ≤ g t ∧ g t ≤ 1) {T : ℝ}
    (hsup : ∀ t, g t ≠ 0 → t ∈ Icc 0 T) {u v p r : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hp : 0 < p) (hr : 0 ≤ r)
    (hu_eq : ∫ t, g t ∂μ₁ = u) (hv_eq : ∫ t, g t ^ 2 ∂μ₁ = v)
    (hp_eq : ∫ y in {y : Fin n → ℝ | ∑ i, y i ≤ 1 - T}, ∏ i, g (y i) ^ 2
      ∂Measure.pi (fun _ => μ₁) = v ^ n * p)
    (hbound : r * v < (n + 1) * u ^ 2 * p) : r < maynardM (n + 1) := by
  let F := prodProfile (n + 1) g
  have hFm : Measurable F := measurable_prodProfile _ hg
  have hF1 : ∀ x, |F x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (prodProfile_bounds _ hg1 x).1]
    exact (prodProfile_bounds _ hg1 x).2
  have hJ (m : Fin (n + 1)) : u ^ 2 * (v ^ n * p) ≤ maynardJ (n + 1) m F := by
    simpa [hu_eq, hp_eq] using maynardJ_prodProfile_ge m hg hg1 hsup
  have hJpos (m : Fin (n + 1)) : 0 < maynardJ (n + 1) m F :=
    lt_of_lt_of_le (by positivity) (hJ m)
  have hIpos : 0 < maynardI (n + 1) F :=
    (hJpos 0).trans_le (maynardJ_le_maynardI 0 hFm hF1)
  have hI : maynardI (n + 1) F ≤ v ^ (n + 1) := by
    simpa [hv_eq] using maynardI_prodProfile_le (n + 1) hg hg1
  have hprof : IsMaynardProfile (n + 1) F :=
    ⟨hFm, ⟨1, hF1⟩, fun x hx => prodProfile_support _ hsup hx,
      hIpos.ne', fun m => (hJpos m).ne'⟩
  have hsum : (n + 1) * (u ^ 2 * (v ^ n * p)) ≤ ∑ m, maynardJ (n + 1) m F := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun m _ => hJ m)
  have hbound' := mul_lt_mul_of_pos_right hbound (pow_pos hv n)
  have hratio : r < maynardRatio (n + 1) F := by
    unfold maynardRatio
    rw [lt_div_iff₀ hIpos]
    have hmul := mul_le_mul_of_nonneg_left hI hr
    rw [pow_succ] at hmul
    nlinarith [hbound']
  exact hratio.trans_le (le_csSup (bddAbove_maynardRatio n) ⟨F, hprof, rfl⟩)

private noncomputable abbrev factorMeasure (c T v : ℝ) : Measure ℝ :=
  μ₁.withDensity (fun t => ENNReal.ofReal (factor c T t ^ 2 / v))

private theorem factorMeasure_probability {c T v : ℝ} (hc : 0 < c) (hv : 0 < v)
    (hv_eq : ∫ t, factor c T t ^ 2 ∂μ₁ = v) : IsProbabilityMeasure (factorMeasure c T v) := by
  apply probability_density (fun t => div_nonneg (sq_nonneg _) hv.le)
    ((integrable_factor_sq hc).div_const v)
  rw [integral_div, hv_eq, div_self hv.ne']

private theorem factorMeasure_memLp {c T v : ℝ}
    [IsProbabilityMeasure (factorMeasure c T v)] :
    MemLp (id : ℝ → ℝ) 2 (factorMeasure c T v) := by
  have hm : Measurable (fun t => factor c T t ^ 2 / v) :=
    ((measurable_factor c T).pow_const 2).div_const v
  refine memLp_of_bounded (density_support (T := T) hm fun t ht => ?_) (by fun_prop) 2
  apply factor_support (c := c)
  intro h
  exact ht (by simp [h])

private theorem factorMeasure_mean {c T u v : ℝ} (hc : 0 < c) (hv : 0 < v)
    (hu_eq : ∫ t, factor c T t ∂μ₁ = u) (hv_eq : ∫ t, factor c T t ^ 2 ∂μ₁ = v) :
    ∫ t, t ∂factorMeasure c T v = (u - v) / (c * v) := by
  have hm : Measurable (fun t => factor c T t ^ 2 / v) :=
    ((measurable_factor c T).pow_const 2).div_const v
  rw [integral_density hm (fun t => div_nonneg (sq_nonneg _) hv.le)]
  simp_rw [div_mul_eq_mul_div, mul_comm (factor c T _ ^ 2)]
  rw [integral_div, factor_first_moment hc, hu_eq, hv_eq, div_div]

private theorem factorMeasure_variance_le {c T v : ℝ} (hc : 0 < c) (hv : 0 < v)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) [IsProbabilityMeasure (factorMeasure c T v)] :
    ProbabilityTheory.variance id (factorMeasure c T v) ≤ T / (c ^ 2 * v) := by
  refine (ProbabilityTheory.variance_le_expectation_sq (by fun_prop)).trans ?_
  have hm : Measurable (fun t => factor c T t ^ 2 / v) :=
    ((measurable_factor c T).pow_const 2).div_const v
  rw [integral_density hm (fun t => div_nonneg (sq_nonneg _) hv.le)]
  simp only [Pi.pow_apply, id_eq]
  simp_rw [div_mul_eq_mul_div, mul_comm (factor c T _ ^ 2)]
  rw [integral_div, ← div_div]
  exact div_le_div_of_nonneg_right (factor_second_moment_le hc hT0 hT1) hv.le

private theorem parameters (n : ℕ) {L a : ℝ} (hL : 16 ≤ L)
    (ha0 : L / 2 ≤ a) (ha1 : a ≤ L) (hk : 8 * L ^ 3 ≤ n + 1) :
    let k : ℝ := n + 1
    let b := k / L ^ 2
    let c := a * k
    let T := (b - 1) / c
    let u := 1 / k
    let v := (1 - 1 / b) / c
    0 < c ∧ 0 < T ∧ T ≤ 1 ∧ 0 < u ∧ 0 < v ∧ 0 ≤ a - 2 ∧
      1 / (2 * a) ≤ 1 - T - n * ((u - v) / (c * v)) ∧
      T / (c ^ 2 * v) = b / c ^ 2 ∧
      (a - 2) * v < k * u ^ 2 * (1 - 4 / L ^ 2) := by
  dsimp only
  let k : ℝ := n + 1
  let b := k / L ^ 2
  let c := a * k
  let T := (b - 1) / c
  let u := 1 / k
  let v := (1 - 1 / b) / c
  change 0 < c ∧ 0 < T ∧ T ≤ 1 ∧ 0 < u ∧ 0 < v ∧ 0 ≤ a - 2 ∧
    1 / (2 * a) ≤ 1 - T - n * ((u - v) / (c * v)) ∧
    T / (c ^ 2 * v) = b / c ^ 2 ∧
    (a - 2) * v < k * u ^ 2 * (1 - 4 / L ^ 2)
  have hL0 : 0 < L := by linarith
  have ha : 0 < a := by linarith
  have hk0 : 0 < k := by dsimp [k]; positivity
  have hc : 0 < c := mul_pos ha hk0
  have hb : 8 * L ≤ b := by
    dsimp [b]
    rw [le_div_iff₀ (sq_pos_of_pos hL0)]
    nlinarith [hk]
  have hb1 : 1 < b := by linarith
  have hT : 0 < T := div_pos (sub_pos.mpr hb1) hc
  have hu : 0 < u := one_div_pos.mpr hk0
  have hv : 0 < v := div_pos (sub_pos.mpr ((div_lt_one (by linarith : 0 < b)).mpr hb1)) hc
  have hTsmall : T ≤ 1 / (a * L ^ 2) := by
    dsimp [T, b, c]
    apply (div_le_div_iff₀ (mul_pos ha hk0) (mul_pos ha (sq_pos_of_pos hL0))).mpr
    dsimp [k] at hk0 ⊢
    field_simp
    nlinarith
  have hTs : T ≤ 1 := hTsmall.trans ((div_le_one (by positivity)).mpr (by nlinarith))
  have hfrac : 1 / (b - 1) ≤ 1 / (4 * a) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hLs : 1 / L ^ 2 ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hmean : k * ((u - v) / (c * v)) = 1 - 1 / a + 1 / (b - 1) := by
    dsimp [u, v, c]
    field_simp; ring
  have hm0 : 0 ≤ (u - v) / (c * v) := by
    apply nonneg_of_mul_nonneg_left ?_ hk0
    rw [mul_comm, hmean]
    have hi : 1 / a ≤ 1 := (div_le_one ha).mpr (by linarith)
    have := one_div_nonneg.mpr (sub_nonneg.mpr hb1.le)
    linarith
  have hn : (n : ℝ) ≤ k := by dsimp [k]; linarith
  have hnm := mul_le_mul_of_nonneg_right hn hm0
  rw [hmean] at hnm
  have hgap : 1 / (2 * a) ≤ 1 - T - n * ((u - v) / (c * v)) := by
    have hTs' : a * T ≤ 1 / L ^ 2 := by
      have := mul_le_mul_of_nonneg_left hTsmall ha.le
      field_simp at this ⊢
      nlinarith
    have hf' : a / (b - 1) ≤ 1 / 4 := by
      have := mul_le_mul_of_nonneg_left hfrac ha.le
      field_simp at this ⊢
      nlinarith
    have hnm' : a * (n * ((u - v) / (c * v))) ≤ a - 1 + a / (b - 1) := by
      convert mul_le_mul_of_nonneg_left hnm ha.le using 1; field_simp
    apply (div_le_iff₀ (by positivity : 0 < 2 * a)).mpr
    nlinarith only [hnm', hTs', hf', hLs]
  have hvar : T / (c ^ 2 * v) = b / c ^ 2 := by
    dsimp [T, v]
    field_simp
  have hq : k * u ^ 2 = (a * b / (b - 1)) * v := by
    dsimp [u, v, c]
    field_simp
  have hp : 0 < 1 - 4 / L ^ 2 := by
    have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) < 4)
      (by nlinarith : (4 : ℝ) ≤ L ^ 2)
    have hstrict : 4 / L ^ 2 < 1 := (div_lt_one (by positivity)).mpr (by nlinarith)
    linarith
  have hab : a ≤ a * b / (b - 1) := by
    rw [le_div_iff₀ (sub_pos.mpr hb1)]
    nlinarith
  have hsmall : a - 2 < a * (1 - 4 / L ^ 2) := by
    have hfour : 4 * a / L ^ 2 < 2 := by
      rw [div_lt_iff₀ (sq_pos_of_pos hL0)]
      nlinarith only [hL, ha1]
    calc a - 2 < a - 4 * a / L ^ 2 := sub_lt_sub_left hfour a
      _ = a * (1 - 4 / L ^ 2) := by ring
  refine ⟨hc, hT, hTs, hu, hv, by linarith, hgap, hvar, ?_⟩
  rw [hq]
  have h := hsmall.trans_le (mul_le_mul_of_nonneg_right hab hp.le)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using mul_lt_mul_of_pos_right h hv

private theorem log_sub_lt_of_parameters (n : ℕ) {L a : ℝ} (hL : 16 ≤ L)
    (ha0 : L / 2 ≤ a) (ha1 : a ≤ L) (hk : 8 * L ^ 3 ≤ n + 1)
    (hlog : Real.log ((n + 1) / L ^ 2) = a) : a - 2 < maynardM (n + 1) := by
  let k : ℝ := n + 1
  let b := k / L ^ 2
  let c := a * k
  let T := (b - 1) / c
  let u := 1 / k
  let v := (1 - 1 / b) / c
  obtain ⟨hc, hT, hT1, hu, hv, hr, hgap, hvar, hbound⟩ := parameters n hL ha0 ha1 hk
  change 0 < c at hc
  change 0 < T at hT
  change T ≤ 1 at hT1
  change 0 < u at hu
  change 0 < v at hv
  change 1 / (2 * a) ≤ 1 - T - n * ((u - v) / (c * v)) at hgap
  change T / (c ^ 2 * v) = b / c ^ 2 at hvar
  change (a - 2) * v < k * u ^ 2 * (1 - 4 / L ^ 2) at hbound
  have ha : 0 < a := by linarith
  have hL0 : 0 < L := by linarith
  have hk0 : 0 < k := by dsimp [k]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hCT : 1 + c * T = b := by dsimp [T]; field_simp; ring
  have hu_eq : ∫ t, factor c T t ∂μ₁ = u := by
    rw [factor_integral hc hT.le hT1, hCT, hlog]
    dsimp [u, c]
    field_simp
  have hv_eq : ∫ t, factor c T t ^ 2 ∂μ₁ = v := by
    rw [factor_sq_integral hc hT.le hT1, hCT]
  let ν := factorMeasure c T v
  let := factorMeasure_probability hc hv hv_eq
  have hν : MemLp (id : ℝ → ℝ) 2 ν := factorMeasure_memLp
  have hmean : ∫ t, t ∂ν = (u - v) / (c * v) := factorMeasure_mean hc hv hu_eq hv_eq
  let d := 1 - T - n * ∫ t, t ∂ν
  have hd : 1 / (2 * a) ≤ d := by simpa [d, hmean] using hgap
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hvariance : ProbabilityTheory.variance id ν ≤ b / c ^ 2 := by
    rw [← hvar]
    exact factorMeasure_variance_le hc hv hT.le hT1
  have hnum : n * ProbabilityTheory.variance id ν ≤ k * b / c ^ 2 := by
    calc n * ProbabilityTheory.variance id ν ≤ n * (b / c ^ 2) :=
        mul_le_mul_of_nonneg_left hvariance (Nat.cast_nonneg _)
      _ ≤ k * (b / c ^ 2) := mul_le_mul_of_nonneg_right (by dsimp [k]; linarith) (by positivity)
      _ = k * b / c ^ 2 := by ring
  have hden : (1 / (2 * a)) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by positivity) hd 2
  have herr : n * ProbabilityTheory.variance id ν / d ^ 2 ≤ 4 / L ^ 2 := by
    calc n * ProbabilityTheory.variance id ν / d ^ 2 ≤
        (k * b / c ^ 2) / (1 / (2 * a)) ^ 2 :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = 4 / L ^ 2 := by dsimp [b, c]; field_simp; ring
  let p := (Measure.pi (fun _ : Fin n => ν)).real {y | ∑ i, y i ≤ 1 - T}
  have hpbound : 1 - 4 / L ^ 2 ≤ p := by
    have hm := simplex_mass n ν hν T hd0
    change 1 - n * ProbabilityTheory.variance id ν / d ^ 2 ≤ p at hm
    linarith
  have hp : 0 < p := lt_of_lt_of_le (by
    have hq : 4 / L ^ 2 < 1 := (div_lt_one (sq_pos_of_pos hL0)).mpr (by nlinarith)
    linarith) hpbound
  have hp_eq : ∫ y in {y : Fin n → ℝ | ∑ i, y i ≤ 1 - T}, ∏ i, factor c T (y i) ^ 2
      ∂Measure.pi (fun _ => μ₁) = v ^ n * p :=
    weighted_mass n (measurable_factor c T) (factor_bounds hc) hv hv_eq _
      (measurableSet_le (by fun_prop) measurable_const)
  apply lt_maynardM_of_prodProfile n (measurable_factor c T) (factor_bounds hc)
    (fun _ ht => factor_support ht) hu hv hp hr hu_eq hv_eq hp_eq
  exact hbound.trans_le (mul_le_mul_of_nonneg_left hpbound (by positivity))

/-- **Growth of `M_k`.** For all sufficiently large `k`,
`M_k > log k - 2 log log k - 2` (Maynard, *Small gaps between primes*, arXiv:1311.4600v3,
Proposition 4.3(3)). -/
theorem eventually_log_sub_lt_maynardM :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      Real.log k - 2 * Real.log (Real.log k) - 2 < maynardM k := by
  have hlog : Tendsto (fun k : ℕ => Real.log k) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun k : ℕ => Real.log (Real.log k) / Real.log k) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hlog
  have hcube : Tendsto (fun k : ℕ => Real.log k ^ 3 / k) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
  apply eventually_atTop.mp
  filter_upwards [hlog.eventually (eventually_ge_atTop 16),
    hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    hcube.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    eventually_ge_atTop 1] with k hL hratio hcube hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [Nat.cast_succ] at hL hratio hcube ⊢
  let L := Real.log (n + 1)
  let a := L - 2 * Real.log L
  have hL0 : 0 < L := by change 0 < Real.log (n + 1); linarith
  have hk0 : (0 : ℝ) < n + 1 := by positivity
  have ha0 : L / 2 ≤ a := by
    change Real.log L / L < 1 / 4 at hratio
    rw [div_lt_iff₀ hL0] at hratio
    dsimp [a]
    linarith
  have ha1 : a ≤ L := by
    have hLp : 0 ≤ Real.log L := Real.log_nonneg (by change 1 ≤ Real.log (n + 1); linarith)
    dsimp [a]
    linarith
  have hk' : 8 * L ^ 3 ≤ n + 1 := by
    change L ^ 3 / (n + 1) < 1 / 8 at hcube
    rw [div_lt_iff₀ hk0] at hcube
    linarith
  have hlog' : Real.log ((n + 1) / L ^ 2) = a := by
    rw [Real.log_div (by positivity) (ne_of_gt (sq_pos_of_pos hL0)), Real.log_pow]
    rfl
  exact log_sub_lt_of_parameters n hL ha0 ha1 hk' hlog'

end WantedExt.NumberTheory.MaynardVariationalBounds
