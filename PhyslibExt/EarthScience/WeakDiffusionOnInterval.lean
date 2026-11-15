/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib

/-!
# Weak diffusion on `(0, 1)`: existence and uniqueness in H¹₀

On `Omega = (0, 1)`, with `kappa` bounded measurable and
`0 < kmin ≤ kappa ≤ kmax` almost everywhere and `f ∈ L²`, there is a unique
`u ∈ H¹₀(Omega)` satisfying `∫ kappa * u' * v' = ∫ f * v` for every
`v ∈ H¹₀(Omega)`. Homogeneous Dirichlet conditions hold in the trace /
closure sense, and there is no drift or mass term.

In one dimension H¹₀ is made concrete: a member of `WeakH10` is an
absolutely continuous function on `[0, 1]` with an L² weak derivative,
vanishing at both endpoints (the integral representation forces
`u 0 = 0`, and the zero-mean condition on the weak derivative forces
`u 1 = 0`). The proof is the explicit one-dimensional formula:
with `F x = ∫₀ˣ f` and `C = (∫ F / kappa) / (∫ 1 / kappa)`, the weak
derivative `w = (C - F) / kappa` has zero mean, `u x = ∫₀ˣ w`, and the weak
equation follows by integration by parts (the Fubini lemma
`integral_primitive_mul_eq_neg`). Uniqueness follows from the energy
identity: testing the difference of two solutions against itself gives
`∫ kappa * (w' - w)² = 0`, and `kappa ≥ kmin > 0` forces the difference of
the weak derivatives to vanish almost everywhere.

## Main results

* `WeakH10`: H¹₀(0, 1) as absolutely continuous functions with L² weak
  derivative and zero endpoints.
* `weakH10_endpoints`: both endpoints vanish.
* `integral_primitive_mul_eq_neg`: integration by parts for L² primitives.
* `weak_diffusion_exists_unique`: existence and uniqueness of the weak
  solution described above.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, ch. 6
  (weak solutions of elliptic equations, Lax-Milgram).
* H. Brezis, *Functional Analysis, Sobolev Spaces and PDEs*, Springer, 2011,
  ch. 8 (Sobolev spaces, Poincaré inequality).
-/

@[expose] public section

namespace EarthScience

open MeasureTheory

/-- H¹₀(0,1) in one dimension: absolutely continuous functions on [0,1] with
an L² weak derivative, vanishing at both endpoints. -/
structure WeakH10 where
  toFun : ℝ → ℝ
  weakDeriv : ℝ → ℝ
  weakDeriv_memLp :
    MemLp weakDeriv 2 (volume.restrict (Set.Icc 0 1))
  toFun_eq_integral :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, toFun x = ∫ t in (0 : ℝ)..x, weakDeriv t
  integral_weakDeriv_eq_zero :
    ∫ t in (0 : ℝ)..1, weakDeriv t = 0

theorem weakH10_endpoints (u : WeakH10) : u.toFun 0 = 0 ∧ u.toFun 1 = 0 := by
  constructor
  · have h0 : u.toFun 0 = ∫ t in (0 : ℝ)..(0 : ℝ), u.weakDeriv t :=
      u.toFun_eq_integral 0 ⟨le_rfl, zero_le_one⟩
    rw [h0]
    exact intervalIntegral.integral_same
  · have h1 : u.toFun 1 = ∫ t in (0 : ℝ)..(1 : ℝ), u.weakDeriv t :=
      u.toFun_eq_integral 1 ⟨zero_le_one, le_rfl⟩
    rw [h1]
    exact u.integral_weakDeriv_eq_zero

/-- L² on a finite-measure set implies L¹. -/
private theorem integrable_of_memLp_two {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    Integrable g (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have h1 : MemLp g 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hg.mono_exponent (by norm_num)
  exact memLp_one_iff_integrable.mp h1

/-- L² on `[0,1]` implies interval-integrability on every subinterval. -/
private theorem intervalIntegrable_of_memLp_two {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable g volume a b := by
  have hint : Integrable g (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    integrable_of_memLp_two hg
  have h2 : IntegrableOn g (Set.Icc (0 : ℝ) 1) volume := hint
  exact intervalIntegrable_iff.mpr (h2.mono_set (by
    intro x hx
    simp only [Set.uIoc, Set.mem_Ioc] at hx
    simp only [Set.mem_Icc] at ha hb ⊢
    obtain ⟨h1, h2⟩ := hx
    have hmin : (0 : ℝ) ≤ min a b := le_min ha.1 hb.1
    have hmax : max a b ≤ (1 : ℝ) := max_le ha.2 hb.2
    constructor <;> linarith))



/-- A bounded continuous factor times an L² function on `[0, 1]` is
interval-integrable on `[0, 1]`. -/
theorem intervalIntegrable_mul_bounded_continuous {φ g : ℝ → ℝ} {C : ℝ}
    (hφ : ContinuousOn φ (Set.Icc (0 : ℝ) 1))
    (hφbdd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |φ x| ≤ C)
    (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    IntervalIntegrable (fun x => φ x * g x) volume 0 1 := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le zero_le_one]
  have hgOn : IntegrableOn g (Set.Ioc (0 : ℝ) 1) volume := by
    rw [← Set.uIoc_of_le zero_le_one]
    exact (intervalIntegrable_of_memLp_two hg ⟨le_rfl, zero_le_one⟩
      ⟨zero_le_one, le_rfl⟩).def'
  have hφmeas : AEStronglyMeasurable φ (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (hφ.mono (Set.Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖φ x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    exact hφbdd x (Set.Ioc_subset_Icc_self hx)
  exact hgOn.bdd_mul hφmeas hbound

/-- Integration by parts for L² primitives on `[0,1]`: if `V` is the primitive
of `g` with `V 1 = 0` (i.e. `∫₀¹ g = 0`), then `∫₀¹ (∫₀ˣ f) g = -∫₀¹ f V`. -/
theorem integral_primitive_mul_eq_neg {f g V : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hV : ∀ x ∈ Set.Icc (0 : ℝ) 1, V x = ∫ t in (0 : ℝ)..x, g t)
    (hg0 : ∫ t in (0 : ℝ)..1, g t = 0) :
    ∫ x, (∫ t in (0 : ℝ)..x, f t) * g x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      = - ∫ x, f x * V x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  classical
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hμ
  have hf_int : Integrable f μ := integrable_of_memLp_two hf
  have hg_int : Integrable g μ := integrable_of_memLp_two hg
  have hμfin : IsFiniteMeasure μ := by
    rw [hμ]
    exact ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    measurableSet_le measurable_fst measurable_snd
  -- The triangle integrand.
  set F : ℝ → ℝ → ℝ := fun t x => if t ≤ x then f t * g x else 0 with hF
  have hFint : Integrable (Function.uncurry F) (μ.prod μ) := by
    have h := (hf_int.mul_prod hg_int).indicator hS
    have heq : Function.uncurry F
        = Set.indicator {p : ℝ × ℝ | p.1 ≤ p.2} (fun p => f p.1 * g p.2) := by
      funext ⟨t, x⟩
      by_cases h : t ≤ x <;> simp [hF, h,
        show ((t, x) ∈ {p : ℝ × ℝ | p.1 ≤ p.2}) ↔ t ≤ x from Iff.rfl]
    rw [heq]
    exact h
  have hswap := MeasureTheory.integral_integral_swap hFint
  -- Inner integral over `t`, for `x ∈ [0,1]`.
  have hinner_t : ∀ᵐ x ∂μ, (∫ t, F t x ∂μ)
      = g x * ∫ t in (0 : ℝ)..x, f t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards with x hx
    obtain ⟨hx0, hx1⟩ := hx
    have h1 : (∫ t, F t x ∂μ) = g x * ∫ t, (if t ≤ x then f t else 0) ∂μ := by
      have h1a : (∫ t, F t x ∂μ)
          = (∫ t, (if t ≤ x then f t else 0) ∂μ) * g x := by
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards with t
        by_cases h : t ≤ x <;> simp [hF, h]
      rw [h1a, mul_comm]
    rw [h1]
    congr 1
    -- `∫ t ∈ Icc 0 1, [t ≤ x] f t = ∫ t ∈ Icc 0 x, f t`.
    have h2 : (∫ t, (if t ≤ x then f t else 0) ∂μ)
        = ∫ t in Set.Icc (0 : ℝ) x, f t ∂volume := by
      have h3 : (∫ t, (if t ≤ x then f t else 0) ∂μ)
          = ∫ t in Set.Iic x, f t ∂μ := by
        rw [← MeasureTheory.integral_indicator measurableSet_Iic]
        apply integral_congr_ae
        filter_upwards with t
        simp [Set.indicator_apply]
      rw [h3]
      -- restrict (Icc 0 1) then (Iic x) = restrict (Icc 0 x)
      have h4 : (μ.restrict (Set.Iic x)) = volume.restrict (Set.Icc (0 : ℝ) x) := by
        rw [hμ, Measure.restrict_restrict measurableSet_Iic]
        congr 1
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
        constructor
        · rintro ⟨htx, h0, -⟩; exact ⟨h0, htx⟩
        · rintro ⟨h0, htx⟩; exact ⟨htx, h0, le_trans htx hx1⟩
      rw [← h4]
    rw [h2, intervalIntegral.integral_of_le hx0, MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- Inner integral over `x`, for `t ∈ [0,1]`.
  have hinner_x : ∀ᵐ t ∂μ, (∫ x, F t x ∂μ) = - f t * V t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h1 : (∫ x, F t x ∂μ) = f t * ∫ x, (if t ≤ x then g x else 0) ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      by_cases h : t ≤ x <;> simp [hF, h]
    rw [h1]
    have h2 : (∫ x, (if t ≤ x then g x else 0) ∂μ)
        = ∫ x in t..1, g x := by
      have h3 : (∫ x, (if t ≤ x then g x else 0) ∂μ)
          = ∫ x in Set.Ici t, g x ∂μ := by
        rw [← MeasureTheory.integral_indicator measurableSet_Ici]
        apply integral_congr_ae
        filter_upwards with x
        simp [Set.indicator_apply]
      rw [h3]
      have h4 : (μ.restrict (Set.Ici t)) = volume.restrict (Set.Icc t 1) := by
        rw [hμ, Measure.restrict_restrict measurableSet_Ici]
        congr 1
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
        constructor
        · rintro ⟨htx, -, hx1⟩; exact ⟨htx, hx1⟩
        · rintro ⟨htx, hx1⟩; exact ⟨htx, le_trans ht0 htx, hx1⟩
      rw [h4]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht1]
    rw [h2]
    have hsplit : (∫ x in (0 : ℝ)..1, g x)
        = (∫ x in (0 : ℝ)..t, g x) + ∫ x in t..1, g x := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_memLp_two hg ⟨le_rfl, zero_le_one⟩ ⟨ht0, ht1⟩)
        (intervalIntegrable_of_memLp_two hg ⟨ht0, ht1⟩ ⟨zero_le_one, le_rfl⟩)]
    have hVt : V t = ∫ x in (0 : ℝ)..t, g x := hV t ⟨ht0, ht1⟩
    rw [hg0] at hsplit
    have h3 : (∫ x in t..1, g x) = - V t := by
      rw [hVt]; linarith [hsplit]
    rw [h3, mul_neg, neg_mul]
  -- Assemble via the swap.
  have hLHS : (∫ x, ∫ t, F t x ∂μ ∂μ)
      = ∫ x, (∫ t in (0 : ℝ)..x, f t) * g x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hinner_t] with x hx
    rw [hx, mul_comm]
  have hRHS : (∫ t, ∫ x, F t x ∂μ ∂μ)
      = - ∫ x, f x * V x ∂μ := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hinner_x] with t ht
    rw [ht]
    exact neg_mul _ _
  rw [← hLHS, ← hRHS]
  exact hswap.symm

/-- The profile of an H¹₀ function is continuous on `[0,1]`. -/
private theorem continuousOn_toFun (u : WeakH10) :
    ContinuousOn u.toFun (Set.Icc (0 : ℝ) 1) := by
  have hprim : ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, u.weakDeriv t) (Set.Icc (0 : ℝ) 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := u.weakDeriv)
      (a := (0 : ℝ)) (b := 1) (by
      rw [Set.uIcc_of_le zero_le_one]
      exact integrable_of_memLp_two u.weakDeriv_memLp)
    rwa [Set.uIcc_of_le zero_le_one] at h
  exact hprim.congr (fun x hx => u.toFun_eq_integral x hx)

/-- The profile of an H¹₀ function is in L² on `[0,1]`. -/
private theorem memLp_two_toFun (u : WeakH10) :
    MemLp u.toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  obtain ⟨MF, hMF⟩ : ∃ MF, ∀ x ∈ Set.Icc (0 : ℝ) 1, |u.toFun x| ≤ MF := by
    obtain ⟨U, hU⟩ := isCompact_Icc.bddAbove_image (continuousOn_toFun u)
    obtain ⟨L, hL⟩ := isCompact_Icc.bddBelow_image (continuousOn_toFun u)
    refine ⟨max |L| |U|, fun x hx => ?_⟩
    have hmem : u.toFun x ∈ u.toFun '' Set.Icc (0 : ℝ) 1 := ⟨x, hx, rfl⟩
    have h1 : L ≤ u.toFun x := hL hmem
    have h2 : u.toFun x ≤ U := hU hmem
    rw [abs_le]
    constructor <;> linarith [neg_abs_le L, le_abs_self U, le_max_left |L| |U|,
      le_max_right |L| |U|]
  have hMF0 : 0 ≤ MF := le_trans (abs_nonneg _) (hMF 0 ⟨le_rfl, zero_le_one⟩)
  exact MemLp.of_bound ((continuousOn_toFun u).aestronglyMeasurable measurableSet_Icc) MF
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx; exact hMF x hx)

/-- `κ * a * b` is integrable when `κ` is bounded measurable and `a, b ∈ L²`. -/
private theorem integrable_kappa_mul {κ a b : ℝ → ℝ} {kmax : ℝ}
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hκ_bdd : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), |κ x| ≤ kmax)
    (ha : MemLp a 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hb : MemLp b 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    Integrable (fun x => κ x * a x * b x) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hab : Integrable (fun x => a x * b x) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have hmul : MemLp (fun x => a x * b x) 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      ha.mul hb
    exact memLp_one_iff_integrable.mp hmul
  have h := hab.bdd_mul hκ_meas hκ_bdd
  -- `bdd_mul` gives `Integrable (fun x => κ x * (a x * b x))`; reassociate.
  apply h.congr
  filter_upwards with x
  ring

theorem weak_diffusion_exists_unique
    {κ f : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (hf : MemLp f 2 (volume.restrict (Set.Icc 0 1))) :
    ∃ u : WeakH10,
      (∀ v : WeakH10,
        ∫ x in (0 : ℝ)..1, κ x * u.weakDeriv x * v.weakDeriv x
          = ∫ x in (0 : ℝ)..1, f x * v.toFun x)
      ∧ ∀ u' : WeakH10,
        (∀ v : WeakH10,
          ∫ x in (0 : ℝ)..1, κ x * u'.weakDeriv x * v.weakDeriv x
            = ∫ x in (0 : ℝ)..1, f x * v.toFun x) →
        Set.EqOn u'.toFun u.toFun (Set.Icc 0 1) := by
  classical
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hμdef
  have hμfin : IsFiniteMeasure μ := by
    rw [hμdef]
    exact ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hconv : ∀ h : ℝ → ℝ, (∫ x in (0 : ℝ)..1, h x) = ∫ x, h x ∂μ := by
    intro h
    rw [intervalIntegral.integral_of_le zero_le_one,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc, hμdef]
  have hκpos : ∀ᵐ x ∂μ, 0 < κ x := hκ.mono fun x hx => lt_of_lt_of_le hkmin hx.1
  have hμuniv : μ Set.univ = 1 := by
    rw [hμdef, Measure.restrict_apply_univ, Real.volume_Icc]
    simp
  have hkmax_pos : 0 < kmax := by
    obtain ⟨x, hx⟩ : ∃ x, kmin ≤ κ x ∧ κ x ≤ kmax := by
      by_contra hne
      have hne' : ∀ x, ¬ (kmin ≤ κ x ∧ κ x ≤ kmax) := fun x h => hne ⟨x, h⟩
      have h0 := ae_iff.mp hκ
      have huniv : {x : ℝ | ¬ (kmin ≤ κ x ∧ κ x ≤ kmax)} = Set.univ := by
        ext x; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact hne' x
      rw [huniv, hμuniv] at h0
      exact one_ne_zero h0
    exact lt_of_lt_of_le hkmin (le_trans hx.1 hx.2)
  have hκ_abs : ∀ᵐ x ∂μ, |κ x| ≤ kmax := by
    filter_upwards [hκ] with x hx
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le kmin, hx.1], hx.2⟩
  -- The reciprocal conductivity.
  have hκinv_meas : AEStronglyMeasurable (fun x => (κ x)⁻¹) μ  := by
    obtain ⟨g, hg_sm, hg_eq⟩ := hκ_meas
    have hg_inv_meas : AEStronglyMeasurable (fun x => (g x)⁻¹) μ :=
      (StronglyMeasurable.measurable hg_sm).inv.aestronglyMeasurable
    exact hg_inv_meas.congr (by
      filter_upwards [hg_eq] with x hx
      rw [← hx])
  have hκinv_le : ∀ᵐ x ∂μ, |(κ x)⁻¹| ≤ 1 / kmin := by
    filter_upwards [hκ, hκpos] with x hx hxpos
    rw [abs_of_pos (inv_pos.mpr hxpos), ← one_div]
    exact one_div_le_one_div_of_le hkmin hx.1
  have hκinv_int : Integrable (fun x => (κ x)⁻¹) μ := by
    have hmem : MemLp (fun x => (κ x)⁻¹) 1 μ := MemLp.of_bound hκinv_meas (1 / kmin) hκinv_le
    exact memLp_one_iff_integrable.mp hmem
  set D : ℝ := ∫ x, (κ x)⁻¹ ∂μ with hDdef
  have hDpos : 0 < D := by
    have hge : ∀ᵐ x ∂μ, 1 / kmax ≤ (κ x)⁻¹ := by
      filter_upwards [hκ, hκpos] with x hx hxpos
      rw [← one_div]
      exact one_div_le_one_div_of_le hxpos hx.2
    have h := integral_mono_ae (integrable_const (1 / kmax)) hκinv_int hge
    rw [integral_const] at h
    rw [Measure.real, hμuniv] at h
    simp only [ENNReal.toReal_one, smul_eq_mul, one_mul] at h
    rw [hDdef]
    exact lt_of_lt_of_le (one_div_pos.mpr hkmax_pos) h
  -- The primitive `F x = ∫₀ˣ f`, cut off outside `[0,1]`.
  set F : ℝ → ℝ := fun x => if x ∈ Set.Icc (0 : ℝ) 1 then ∫ t in (0 : ℝ)..x, f t else 0 with hFdef
  have hF_cont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    have hprim : ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, f t) (Set.Icc (0 : ℝ) 1) := by
      have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := f)
        (a := (0 : ℝ)) (b := 1) (by
        rw [Set.uIcc_of_le zero_le_one]
        exact integrable_of_memLp_two hf)
      rwa [Set.uIcc_of_le zero_le_one] at h
    exact hprim.congr (fun x hx => by rw [hFdef]; simp [hx])
  have hF_meas : AEStronglyMeasurable F μ := by
    rw [hμdef]
    exact hF_cont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨MF, hMF⟩ : ∃ MF, ∀ x ∈ Set.Icc (0 : ℝ) 1, |F x| ≤ MF := by
    obtain ⟨U, hU⟩ := isCompact_Icc.bddAbove_image hF_cont
    obtain ⟨L, hL⟩ := isCompact_Icc.bddBelow_image hF_cont
    refine ⟨max |L| |U|, fun x hx => ?_⟩
    have hmem : F x ∈ F '' Set.Icc (0 : ℝ) 1 := ⟨x, hx, rfl⟩
    have h1 : L ≤ F x := hL hmem
    have h2 : F x ≤ U := hU hmem
    rw [abs_le]
    constructor <;> linarith [neg_abs_le L, le_abs_self U, le_max_left |L| |U|,
      le_max_right |L| |U|]
  have hMF0 : 0 ≤ MF := le_trans (abs_nonneg _) (hMF 0 ⟨le_rfl, zero_le_one⟩)
  -- `A = ∫ F / κ`, `C = A / D`.
  have hFκ_int : Integrable (fun x => F x * (κ x)⁻¹) μ := by
    have hbound : ∀ᵐ x ∂μ, |F x| ≤ MF := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact hMF x hx
    have hmeas2 : AEStronglyMeasurable (fun x => F x * (κ x)⁻¹) μ :=
      hF_meas.mul hκinv_meas
    have hbound2 : ∀ᵐ x ∂μ, ‖F x * (κ x)⁻¹‖ ≤ MF * (1 / kmin) := by
      filter_upwards [hbound, hκinv_le] with x hx1 hx2
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hx1 hx2 (abs_nonneg _) hMF0
    have hmul : MemLp (fun x => F x * (κ x)⁻¹) 1 μ :=
      MemLp.of_bound hmeas2 (MF * (1 / kmin)) hbound2
    exact memLp_one_iff_integrable.mp hmul
  set A : ℝ := ∫ x, F x * (κ x)⁻¹ ∂μ with hAdef
  set C : ℝ := A / D with hCdef
  -- The weak derivative `w = (C - F) / κ`, cut off outside `[0,1]`.
  set w : ℝ → ℝ := fun x => if x ∈ Set.Icc (0 : ℝ) 1 then (C - F x) * (κ x)⁻¹ else 0 with hwdef
  have hw_memLp : MemLp w 2 μ := by
    have hbound : ∀ᵐ x ∂μ, |w x| ≤ (|C| + MF) * (1 / kmin) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc, hκinv_le] with x hx hx2
      have hwx : w x = (C - F x) * (κ x)⁻¹ := by rw [hwdef]; simp [hx]
      rw [hwx, abs_mul]
      have hCF : |C - F x| ≤ |C| + MF := by
        have h1 := abs_sub C (F x)
        have hFx := hMF x hx
        linarith [h1, abs_nonneg (F x)]
      exact mul_le_mul hCF hx2 (abs_nonneg _) (add_nonneg (abs_nonneg _) hMF0)
    have hmeas : AEStronglyMeasurable w μ := by
      have h1 : AEStronglyMeasurable (fun x => (C - F x) * (κ x)⁻¹) μ := by
        have hsub : AEStronglyMeasurable (fun x => C - F x) μ :=
          (aestronglyMeasurable_const (μ := μ) (b := C)).sub hF_meas
        exact hsub.mul hκinv_meas
      apply h1.congr
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [hwdef]; simp [hx]
    exact MemLp.of_bound hmeas ((|C| + MF) * (1 / kmin)) hbound
  -- `∫₀¹ w = 0` by the choice of `C`.
  have hw_int_zero : ∫ t in (0 : ℝ)..1, w t = 0 := by
    have hμint : ∫ x, w x ∂μ = 0 := by
      have hcongr : (∫ x, w x ∂μ) = ∫ x, (C - F x) * (κ x)⁻¹ ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        rw [hwdef]; simp [hx]
      rw [hcongr]
      have hsplit : (∫ x, (C - F x) * (κ x)⁻¹ ∂μ)
          = C * D - A := by
        have hEq : ∀ x, (C - F x) * (κ x)⁻¹ = C * (κ x)⁻¹ - F x * (κ x)⁻¹ := fun x => by ring
        rw [integral_congr_ae (Filter.Eventually.of_forall fun x => hEq x)]
        rw [integral_sub (hκinv_int.const_mul C) hFκ_int, integral_const_mul]
      rw [hsplit, hCdef, div_mul_cancel₀ A (ne_of_gt hDpos), sub_self]
    rw [hconv]
    exact hμint
  -- The solution `u`.
  set U : ℝ → ℝ := fun x => if x ∈ Set.Icc (0 : ℝ) 1 then ∫ t in (0 : ℝ)..x, w t else 0 with hUdef
  set u : WeakH10 := ⟨U, w, hw_memLp,
    fun x hx => by rw [hUdef]; simp [hx],
    hw_int_zero⟩ with hudef
  have hu_eq : ∀ v : WeakH10,
      ∫ x in (0 : ℝ)..1, κ x * w x * v.weakDeriv x
        = ∫ x in (0 : ℝ)..1, f x * v.toFun x := by
    intro v
    set g : ℝ → ℝ := v.weakDeriv with hgdef
    have hg_int : Integrable g μ := integrable_of_memLp_two v.weakDeriv_memLp
    -- Convert both sides to `μ`-integrals.
    rw [hconv, hconv]
    -- `∫ κ * w * g = ∫ (C - F) * g`.
    have hκw : (∫ x, κ x * w x * g x ∂μ) = ∫ x, (C - F x) * g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, hκpos] with x hx hxpos
      have hwx : w x = (C - F x) * (κ x)⁻¹ := by rw [hwdef]; simp [hx]
      rw [hwx]
      have hne : (κ x) ≠ 0 := ne_of_gt hxpos
      calc κ x * ((C - F x) * (κ x)⁻¹) * g x
          = (κ x * (κ x)⁻¹) * ((C - F x) * g x) := by ring
        _ = (C - F x) * g x := by rw [mul_inv_cancel₀ hne, one_mul]
    rw [hκw]
    -- `∫ (C - F) * g = C * ∫ g - ∫ F * g`, and `∫ g = 0`.
    have hFg_int : Integrable (fun x => F x * g x) μ := by
      have hbound : ∀ᵐ x ∂μ, |F x| ≤ MF := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact hMF x hx
      exact hg_int.bdd_mul hF_meas hbound
    have hCg_int : Integrable (fun x => C * g x) μ := hg_int.const_mul C
    have hsplit : (∫ x, (C - F x) * g x ∂μ) = C * (∫ x, g x ∂μ) - ∫ x, F x * g x ∂μ := by
      have hEq : ∀ x, (C - F x) * g x = C * g x - F x * g x := fun x => by ring
      rw [integral_congr_ae (Filter.Eventually.of_forall fun x => hEq x),
        integral_sub hCg_int hFg_int, integral_const_mul]
    rw [hsplit]
    have hg_zero : (∫ x, g x ∂μ) = 0 := by
      rw [← hconv]
      exact v.integral_weakDeriv_eq_zero
    rw [hg_zero, mul_zero, zero_sub]
    -- Fubini: `∫ F * g = - ∫ f * v.toFun`.
    have hFub : (∫ x, F x * g x ∂μ) = - ∫ x, f x * v.toFun x ∂μ := by
      have hstep : (∫ x, F x * g x ∂μ)
          = ∫ x, (∫ t in (0 : ℝ)..x, f t) * g x ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        have hFx : F x = ∫ t in (0 : ℝ)..x, f t := by rw [hFdef]; simp [hx]
        rw [hFx]
      rw [hstep]
      exact integral_primitive_mul_eq_neg hf v.weakDeriv_memLp v.toFun_eq_integral
        v.integral_weakDeriv_eq_zero
    rw [hFub, neg_neg]
  refine ⟨u, fun v => hu_eq v, ?_⟩
  · -- Uniqueness.
    intro u' hu'
    have htoFun : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        u'.toFun x - u.toFun x = ∫ t in (0 : ℝ)..x, (u'.weakDeriv - w) t := by
      intro x hx
      have h1 := u'.toFun_eq_integral x hx
      have h2 : u.toFun x = ∫ t in (0 : ℝ)..x, w t := by
        have hU : U x = ∫ t in (0 : ℝ)..x, w t := by rw [hUdef]; simp [hx]
        exact hU
      rw [h1, h2]
      exact (intervalIntegral.integral_sub
        (intervalIntegrable_of_memLp_two u'.weakDeriv_memLp ⟨le_rfl, zero_le_one⟩ hx)
        (intervalIntegrable_of_memLp_two hw_memLp ⟨le_rfl, zero_le_one⟩ hx)).symm
    have hInt0 : ∫ t in (0 : ℝ)..1, (u'.weakDeriv - w) t = 0 := by
      change (∫ t in (0 : ℝ)..1, (u'.weakDeriv t - w t)) = 0
      have h := intervalIntegral.integral_sub
        (intervalIntegrable_of_memLp_two u'.weakDeriv_memLp ⟨le_rfl, zero_le_one⟩
          ⟨zero_le_one, le_rfl⟩)
        (intervalIntegrable_of_memLp_two hw_memLp ⟨le_rfl, zero_le_one⟩
          ⟨zero_le_one, le_rfl⟩)
      rw [h, u'.integral_weakDeriv_eq_zero, hw_int_zero, sub_self]
    set d : WeakH10 := ⟨fun x => u'.toFun x - u.toFun x, (u'.weakDeriv - w),
      u'.weakDeriv_memLp.sub hw_memLp, htoFun, hInt0⟩ with hddef
    have h1μ : (∫ x, κ x * u'.weakDeriv x * (u'.weakDeriv - w) x ∂μ)
        = ∫ x, f x * d.toFun x ∂μ := by
      rw [← hconv, ← hconv]
      exact hu' d
    have h2μ : (∫ x, κ x * w x * (u'.weakDeriv - w) x ∂μ) = ∫ x, f x * d.toFun x ∂μ := by
      rw [← hconv, ← hconv]
      exact hu_eq d
    have henergy : (∫ x, κ x * (u'.weakDeriv - w) x * (u'.weakDeriv - w) x ∂μ) = 0 := by
      have hsub : (∫ x, κ x * u'.weakDeriv x * (u'.weakDeriv - w) x ∂μ)
          - (∫ x, κ x * w x * (u'.weakDeriv - w) x ∂μ) = 0 := by
        rw [h1μ, h2μ, sub_self]
      have hdiff : (∫ x, κ x * u'.weakDeriv x * (u'.weakDeriv - w) x ∂μ)
          - (∫ x, κ x * w x * (u'.weakDeriv - w) x ∂μ)
          = ∫ x, κ x * (u'.weakDeriv - w) x * (u'.weakDeriv - w) x ∂μ := by
        rw [← integral_sub
          (integrable_kappa_mul hκ_meas hκ_abs u'.weakDeriv_memLp
            (u'.weakDeriv_memLp.sub hw_memLp))
          (integrable_kappa_mul hκ_meas hκ_abs hw_memLp
            (u'.weakDeriv_memLp.sub hw_memLp))]
        apply integral_congr_ae
        filter_upwards with x
        simp only [Pi.sub_apply]
        ring
      rw [hdiff] at hsub
      exact hsub
    have hgd_sq_int : Integrable (fun x => (u'.weakDeriv - w) x * (u'.weakDeriv - w) x) μ := by
      have hmul : MemLp (fun x => (u'.weakDeriv - w) x * (u'.weakDeriv - w) x) 1 μ :=
        (u'.weakDeriv_memLp.sub hw_memLp).mul (u'.weakDeriv_memLp.sub hw_memLp)
      exact memLp_one_iff_integrable.mp hmul
    have hgd_ae : (u'.weakDeriv - w) =ᵐ[μ] 0 := by
      have hnonneg : (0 : ℝ → ℝ) ≤ᵐ[μ] (fun x => (u'.weakDeriv - w) x * (u'.weakDeriv - w) x) := by
        filter_upwards with x
        exact mul_self_nonneg _
      have hsq0 : (∫ x, (u'.weakDeriv - w) x * (u'.weakDeriv - w) x ∂μ) = 0 := by
        have hmono : kmin * (∫ x, (u'.weakDeriv - w) x * (u'.weakDeriv - w) x ∂μ)
            ≤ ∫ x, κ x * (u'.weakDeriv - w) x * (u'.weakDeriv - w) x ∂μ := by
          rw [← integral_const_mul]
          apply integral_mono_ae
          · exact hgd_sq_int.const_mul kmin
          · exact integrable_kappa_mul hκ_meas hκ_abs (u'.weakDeriv_memLp.sub hw_memLp)
              (u'.weakDeriv_memLp.sub hw_memLp)
          · filter_upwards [hκ] with x hx
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right hx.1 (mul_self_nonneg _)
        rw [henergy] at hmono
        have hnn : 0 ≤ ∫ x, (u'.weakDeriv - w) x * (u'.weakDeriv - w) x ∂μ :=
          integral_nonneg fun x => mul_self_nonneg _
        have hkm : kmin * (∫ x, (u'.weakDeriv - w) x * (u'.weakDeriv - w) x ∂μ) = 0 :=
          le_antisymm (by linarith) (mul_nonneg (le_of_lt hkmin) hnn)
        exact (mul_eq_zero.mp hkm).resolve_left (ne_of_gt hkmin)
      have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hgd_sq_int).mp hsq0
      filter_upwards [hzero] with x hx
      exact mul_self_eq_zero.mp hx
    intro x hx
    have hdiff : u'.toFun x - u.toFun x = ∫ t in (0 : ℝ)..x, (u'.weakDeriv - w) t := htoFun x hx
    have hint0 : (∫ t in (0 : ℝ)..x, (u'.weakDeriv - w) t) = 0 := by
      have hgd_vol : ∀ᵐ t ∂volume, t ∈ Set.Icc (0 : ℝ) 1 → (u'.weakDeriv - w) t = 0 := by
        have h2 : ∀ᵐ x ∂μ, (u'.weakDeriv - w) x = 0 := hgd_ae
        rw [hμdef, ae_restrict_iff' measurableSet_Icc] at h2
        exact h2
      have h2 : (∫ t in (0 : ℝ)..x, (u'.weakDeriv - w) t) = ∫ t in (0 : ℝ)..x, (0 : ℝ → ℝ) t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hgd_vol] with t ht
        intro htI
        exact ht (by
          simp only [Set.uIoc, Set.mem_Ioc] at htI
          obtain ⟨h1, h2⟩ := htI
          have hmin : (0 : ℝ) ≤ min 0 x := le_min le_rfl hx.1
          have hmax : max 0 x ≤ (1 : ℝ) := max_le zero_le_one hx.2
          exact ⟨by linarith, by linarith⟩)
      rw [h2]
      simp
    rw [hint0, sub_eq_zero] at hdiff
    exact hdiff

end EarthScience
