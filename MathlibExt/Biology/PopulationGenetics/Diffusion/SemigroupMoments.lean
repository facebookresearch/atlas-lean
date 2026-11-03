/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.Semigroup
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Moment bounds for the neutral Wright–Fisher semigroup

This file develops time differentiation for the existing polynomial semigroup and proves the
second- and fourth-centered-moment estimates used in path-space constructions.

## References

* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
  (1986), Chapter 10 (neutral Wright–Fisher generators and moment estimates).
-/

@[expose] public section

open Filter Topology Polynomial
open scoped unitInterval

namespace MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup

private theorem tendsto_wfSemigroup_slope_zero_right (p : ℝ[X]) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto
      (fun s : ℝ => s⁻¹ •
        (wfSemigroup (t + s) (p.toContinuousMapOn I) -
          wfSemigroup t (p.toContinuousMapOn I)))
      (𝓝[>] 0)
      (𝓝 (wfSemigroup t ((polyGenerator p).toContinuousMapOn I))) := by
  have h := ((wfSemigroup t).continuous.continuousAt.tendsto).comp
    (tendsto_wfSemigroup_sub_div p)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [wfSemigroup_add ht hs.le]
  simp only [mul_apply_eq_comp, Function.comp_apply, map_smul, map_sub]

private theorem tendsto_wfSemigroup_generator_neg (p : ℝ[X]) :
    Tendsto
      ((fun u : ℝ => u⁻¹ •
        (wfSemigroup u (p.toContinuousMapOn I) - p.toContinuousMapOn I)) ∘
          fun s : ℝ => -s)
      (𝓝[<] 0) (𝓝 ((polyGenerator p).toContinuousMapOn I)) :=
  (tendsto_wfSemigroup_sub_div p).comp (by
    simpa using (tendsto_neg_nhdsLT (a := (0 : ℝ))))

private theorem tendsto_wfSemigroup_neg (f : C(I, ℝ)) :
    Tendsto ((fun u : ℝ => wfSemigroup u f) ∘ fun s : ℝ => -s)
      (𝓝[<] 0) (𝓝 f) := by
  have h := (tendsto_wfSemigroup_nhdsGE_zero f).mono_left
    (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
  exact h.comp (by
    simpa using (tendsto_neg_nhdsLT (a := (0 : ℝ))))

private theorem wfSemigroup_slope_zero_left_norm_le (p : ℝ[X]) {t s : ℝ}
    (hs : s < 0) (hts : 0 ≤ t + s) :
    ‖s⁻¹ •
        (wfSemigroup (t + s) (p.toContinuousMapOn I) -
          wfSemigroup t (p.toContinuousMapOn I)) -
      wfSemigroup t ((polyGenerator p).toContinuousMapOn I)‖ ≤
    ‖(-s)⁻¹ •
        (wfSemigroup (-s) (p.toContinuousMapOn I) - p.toContinuousMapOn I) -
      wfSemigroup (-s) ((polyGenerator p).toContinuousMapOn I)‖ := by
  have hneg : 0 ≤ -s := neg_nonneg.mpr hs.le
  have hadd := wfSemigroup_add hts hneg
  rw [show t + s + -s = t by ring] at hadd
  rw [hadd]
  simp only [mul_apply_eq_comp]
  rw [← map_sub, ← map_smul, ← map_sub]
  rw [inv_neg, neg_smul, ← smul_neg, neg_sub]
  exact ((wfSemigroup (t + s)).le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_wfSemigroup_le (t + s)))

private theorem tendsto_wfSemigroup_slope_zero_left (p : ℝ[X]) {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun s : ℝ => s⁻¹ •
        (wfSemigroup (t + s) (p.toContinuousMapOn I) -
          wfSemigroup t (p.toContinuousMapOn I)))
      (𝓝[<] 0)
      (𝓝 (wfSemigroup t ((polyGenerator p).toContinuousMapOn I))) := by
  let a := (polyGenerator p).toContinuousMapOn I
  let q := (fun u : ℝ => u⁻¹ •
    (wfSemigroup u (p.toContinuousMapOn I) - p.toContinuousMapOn I)) ∘ fun s : ℝ => -s
  let r := (fun u : ℝ => wfSemigroup u a) ∘ fun s : ℝ => -s
  have hq : Tendsto q (𝓝[<] 0) (𝓝 a) := by
    simpa only [q, a] using tendsto_wfSemigroup_generator_neg p
  have hr : Tendsto r (𝓝[<] 0) (𝓝 a) := by
    simpa only [r] using tendsto_wfSemigroup_neg a
  have hdiff : Tendsto (fun s => q s - r s) (𝓝[<] 0) (𝓝 0) := by
    simpa only [sub_self] using hq.sub hr
  have hsmall : ∀ᶠ s : ℝ in 𝓝[<] 0, 0 ≤ t + s := by
    filter_upwards [
      (eventually_gt_nhds (neg_lt_zero.mpr ht)).filter_mono inf_le_left] with s hs
    linarith
  have hle : ∀ᶠ s : ℝ in 𝓝[<] 0,
      ‖s⁻¹ •
          (wfSemigroup (t + s) (p.toContinuousMapOn I) -
            wfSemigroup t (p.toContinuousMapOn I)) - wfSemigroup t a‖ ≤
        ‖q s - r s‖ := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hts
    exact wfSemigroup_slope_zero_left_norm_le p hs hts
  have hzero := squeeze_zero_norm' hle (by simpa using hdiff.norm)
  simpa only [sub_add_cancel, zero_add] using
    hzero.add_const (wfSemigroup t a)

/-- **Polynomial semigroup dynamics.** At every positive time, differentiating the existing
Wright–Fisher semigroup on a polynomial equals applying the semigroup to its generator. -/
theorem hasDerivAt_wfSemigroup_toContinuousMapOn (p : ℝ[X]) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => wfSemigroup s (p.toContinuousMapOn I))
      (wfSemigroup t ((polyGenerator p).toContinuousMapOn I)) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero, ← Set.Iio_union_Ioi (a := (0 : ℝ)),
    nhdsWithin_union]
  exact (tendsto_wfSemigroup_slope_zero_left p ht).sup
    (tendsto_wfSemigroup_slope_zero_right p ht.le)

/-- Scalar form of polynomial semigroup dynamics, evaluated at a state in `[0, 1]`. -/
private theorem hasDerivAt_wfSemigroup_eval (p : ℝ[X]) (x : I) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => wfSemigroup s (p.toContinuousMapOn I) x)
      (wfSemigroup t ((polyGenerator p).toContinuousMapOn I) x) t := by
  have h := ((ContinuousMap.evalCLM ℝ x).hasFDerivAt.comp t
    (hasDerivAt_wfSemigroup_toContinuousMapOn p ht).hasFDerivAt).hasDerivAt
  convert h using 1
  · funext s
    rfl
  · rw [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply_one, ContinuousMap.evalCLM_apply]

/-- Positivity makes the Wright–Fisher semigroup monotone on continuous functions. -/
private theorem wfSemigroup_mono (t : ℝ) {f g : C(I, ℝ)} (hfg : f ≤ g) :
    wfSemigroup t f ≤ wfSemigroup t g := by
  have hsub : 0 ≤ g - f := ContinuousMap.le_def.2 fun x => by
    simpa only [ContinuousMap.zero_apply, ContinuousMap.sub_apply] using
      sub_nonneg.mpr (ContinuousMap.le_def.1 hfg x)
  have h := wfSemigroup_nonneg t hsub
  refine ContinuousMap.le_def.2 fun x => ?_
  have hx := ContinuousMap.le_def.1 h x
  simp only [map_sub, ContinuousMap.zero_apply, ContinuousMap.sub_apply] at hx
  exact sub_nonneg.mp hx

private theorem polyGenerator_centered_sq (x : ℝ) :
    polyGenerator ((X - C x) ^ 2) = X * (1 - X) := by
  have hd : derivative (derivative ((X - C x) ^ 2)) = C (2 : ℝ) := by
    simp [Polynomial.derivative_pow]
  rw [polyGenerator, hd]
  have hc : C (1 / 2 : ℝ) * C 2 = (1 : ℝ[X]) := by
    rw [← C_mul]
    norm_num
  calc
    C (1 / 2 : ℝ) * X * (1 - X) * C 2 =
        (C (1 / 2 : ℝ) * C 2) * (X * (1 - X)) := by ring
    _ = X * (1 - X) := by rw [hc, one_mul]

private theorem polyGenerator_centered_fourth (x : ℝ) :
    polyGenerator ((X - C x) ^ 4) =
      C (6 : ℝ) * X * (1 - X) * (X - C x) ^ 2 := by
  have hc43 : C (4 : ℝ) * C 3 = C 12 := by
    rw [← C_mul]
    norm_num
  have hd : derivative (derivative ((X - C x) ^ 4)) =
      C (12 : ℝ) * (X - C x) ^ 2 := by
    simp only [derivative_pow, Nat.cast_ofNat, Nat.add_one_sub_one, derivative_sub,
      derivative_X, derivative_C, sub_zero, mul_one, derivative_mul, zero_mul, zero_add]
    rw [← mul_assoc, hc43]
  rw [polyGenerator, hd]
  have hc : C (1 / 2 : ℝ) * C 12 = C 6 := by
    rw [← C_mul]
    norm_num
  calc
    C (1 / 2 : ℝ) * X * (1 - X) * (C 12 * (X - C x) ^ 2) =
        (C (1 / 2 : ℝ) * C 12) * X * (1 - X) * (X - C x) ^ 2 := by ring
    _ = C 6 * X * (1 - X) * (X - C x) ^ 2 := by rw [hc]

/-- The polynomial semigroup, evaluated at a state, is continuous for nonnegative time. -/
private theorem continuousOn_wfSemigroup_eval (p : ℝ[X]) (x : I) :
    ContinuousOn (fun t : ℝ => wfSemigroup t (p.toContinuousMapOn I) x) (Set.Ici 0) := by
  intro t ht
  rcases ht.eq_or_lt with rfl | ht
  · have h := ((continuous_eval_const x).tendsto _).comp
      (tendsto_wfSemigroup_nhdsGE_zero (p.toContinuousMapOn I))
    rw [Metric.continuousWithinAt_iff']
    intro ε hε
    have he := Metric.tendsto_nhds.1 h ε hε
    filter_upwards [he] with s hs
    simpa only [Function.comp_apply, wfSemigroup_zero, one_apply_eq_self] using hs
  · exact (hasDerivAt_wfSemigroup_eval p x ht).continuousAt.continuousWithinAt

private theorem wfSemigroup_X_mul_one_sub_X_le (t : ℝ) (x : I) :
    wfSemigroup t ((X * (1 - X) : ℝ[X]).toContinuousMapOn I) x ≤ 1 / 4 := by
  have hp : (X * (1 - X) : ℝ[X]).toContinuousMapOn I ≤
      (C (1 / 4 : ℝ)).toContinuousMapOn I := ContinuousMap.le_def.2 fun y => by
    rcases y.property with ⟨hy0, hy1⟩
    simp only [toContinuousMapOn_apply, toContinuousMap_apply, eval_mul, eval_X, eval_sub,
      eval_one, eval_C]
    nlinarith [sq_nonneg ((y : ℝ) - 1 / 2)]
  calc
    wfSemigroup t ((X * (1 - X) : ℝ[X]).toContinuousMapOn I) x ≤
        wfSemigroup t ((C (1 / 4 : ℝ)).toContinuousMapOn I) x :=
      ContinuousMap.le_def.1 (wfSemigroup_mono t hp) x
    _ = 1 / 4 := by
      have hc : (C (1 / 4 : ℝ)).toContinuousMapOn I =
          (1 / 4 : ℝ) • (1 : C(I, ℝ)) := by
        ext y
        simp
      rw [hc, map_smul, wfSemigroup_apply_one]
      simp

/-- The centered second moment grows at most linearly: `T_t[(y-x)²](x) ≤ t/4`. -/
theorem wfSemigroup_second_increment_le {t : ℝ} (ht : 0 ≤ t) (x : I) :
    wfSemigroup t (((X - C (x : ℝ)) ^ 2 : ℝ[X]).toContinuousMapOn I) x ≤
      (1 / 4 : ℝ) * t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  · let p : ℝ[X] := (X - C (x : ℝ)) ^ 2
    let r : ℝ → ℝ := fun s => wfSemigroup s (p.toContinuousMapOn I) x
    have hcont : ContinuousOn r (Set.Icc 0 t) :=
      (continuousOn_wfSemigroup_eval p x).mono Set.Icc_subset_Ici_self
    have hdiff : DifferentiableOn ℝ r (interior (Set.Icc 0 t)) := by
      rw [interior_Icc]
      intro s hs
      exact (hasDerivAt_wfSemigroup_eval p x hs.1).differentiableAt.differentiableWithinAt
    have hderiv : ∀ s ∈ interior (Set.Icc 0 t), deriv r s ≤ (1 / 4 : ℝ) := by
      rw [interior_Icc]
      intro s hs
      rw [(hasDerivAt_wfSemigroup_eval p x hs.1).deriv]
      change wfSemigroup s ((polyGenerator ((X - C (x : ℝ)) ^ 2)).toContinuousMapOn I) x ≤ _
      rw [polyGenerator_centered_sq]
      exact wfSemigroup_X_mul_one_sub_X_le s x
    have h := Convex.image_sub_le_mul_sub_of_deriv_le
      (convex_Icc (𝕜 := ℝ) 0 t) hcont hdiff hderiv
      0 (Set.left_mem_Icc.mpr ht.le) t (Set.right_mem_Icc.mpr ht.le) ht.le
    dsimp only [r, p] at h
    simpa using h

private theorem centered_generator_pointwise_le (x y : ℝ) :
    6 * y * (1 - y) * (y - x) ^ 2 ≤ (3 / 2 : ℝ) * (y - x) ^ 2 := by
  have hy : y * (1 - y) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (y - 1 / 2)]
  have hz : 0 ≤ (y - x) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hy hz
  calc
    6 * y * (1 - y) * (y - x) ^ 2 = 6 * (y * (1 - y) * (y - x) ^ 2) := by ring
    _ ≤ 6 * ((1 / 4 : ℝ) * (y - x) ^ 2) :=
      mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ = (3 / 2 : ℝ) * (y - x) ^ 2 := by ring

private theorem centered_generator_map_le (x : I) :
    (polyGenerator ((X - C (x : ℝ)) ^ 4)).toContinuousMapOn I ≤
      (3 / 2 : ℝ) • (((X - C (x : ℝ)) ^ 2 : ℝ[X]).toContinuousMapOn I) := by
  rw [polyGenerator_centered_fourth]
  refine ContinuousMap.le_def.2 fun y => ?_
  simpa only [toContinuousMapOn_apply, toContinuousMap_apply, eval_mul, eval_C, eval_X,
    eval_sub, eval_one, eval_pow, ContinuousMap.smul_apply, smul_eq_mul] using
    centered_generator_pointwise_le (x : ℝ) (y : ℝ)

private theorem wfSemigroup_generator_fourth_le_second (t : ℝ) (x : I) :
    wfSemigroup t
        ((polyGenerator ((X - C (x : ℝ)) ^ 4)).toContinuousMapOn I) x ≤
      (3 / 2 : ℝ) *
        wfSemigroup t (((X - C (x : ℝ)) ^ 2 : ℝ[X]).toContinuousMapOn I) x := by
  have h := wfSemigroup_mono t (centered_generator_map_le x)
  have hx := ContinuousMap.le_def.1 h x
  simpa only [map_smul, ContinuousMap.smul_apply, smul_eq_mul] using hx

private theorem hasDerivAt_fourth_adjusted (x : I) {s : ℝ} (hs : 0 < s) :
    HasDerivAt
      (fun u : ℝ =>
        wfSemigroup u (((X - C (x : ℝ)) ^ 4 : ℝ[X]).toContinuousMapOn I) x -
          (3 / 16 : ℝ) * u ^ 2)
      (wfSemigroup s
          ((polyGenerator ((X - C (x : ℝ)) ^ 4)).toContinuousMapOn I) x -
        (3 / 8 : ℝ) * s) s := by
  have hquad := (hasDerivAt_pow 2 s).const_mul (3 / 16 : ℝ)
  convert (hasDerivAt_wfSemigroup_eval ((X - C (x : ℝ)) ^ 4) x hs).sub hquad using 1
  ring

/-- The fourth centered increment of the neutral Wright–Fisher semigroup satisfies the uniform
Kolmogorov bound `T_t[(y-x)⁴](x) ≤ (3/16)t²`. -/
theorem wfSemigroup_fourth_increment_le {t : ℝ} (ht : 0 ≤ t) (x : I) :
    wfSemigroup t (((X - C (x : ℝ)) ^ 4 : ℝ[X]).toContinuousMapOn I) x ≤
      (3 / 16 : ℝ) * t ^ 2 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  · let p : ℝ[X] := (X - C (x : ℝ)) ^ 4
    let g : ℝ → ℝ := fun s =>
      wfSemigroup s (p.toContinuousMapOn I) x - (3 / 16 : ℝ) * s ^ 2
    have hcont : ContinuousOn g (Set.Icc 0 t) := by
      apply ContinuousOn.sub
      · exact (continuousOn_wfSemigroup_eval p x).mono Set.Icc_subset_Ici_self
      · fun_prop
    have hdiff : DifferentiableOn ℝ g (interior (Set.Icc 0 t)) := by
      rw [interior_Icc]
      intro s hs
      exact (hasDerivAt_fourth_adjusted x hs.1).differentiableAt.differentiableWithinAt
    have hderiv : ∀ s ∈ interior (Set.Icc 0 t), deriv g s ≤ 0 := by
      rw [interior_Icc]
      intro s hs
      rw [(hasDerivAt_fourth_adjusted x hs.1).deriv]
      have h4 := wfSemigroup_generator_fourth_le_second s x
      have h2 := wfSemigroup_second_increment_le hs.1.le x
      linarith
    have hanti := antitoneOn_of_deriv_nonpos (convex_Icc (𝕜 := ℝ) 0 t)
      hcont hdiff hderiv
    have h := hanti (Set.left_mem_Icc.mpr ht.le) (Set.right_mem_Icc.mpr ht.le) ht.le
    dsimp only [g, p] at h
    simpa using h

end MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup
