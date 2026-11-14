/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Taylor's theorem for analytic functions with the Cauchy integral remainder

If `f` is analytic on an open set `Ω` containing `a`, then for every `n`
`f z = ∑ k < n, f⁽ᵏ⁾(a) / k! * (z - a) ^ k + fₙ z * (z - a) ^ n` on `Ω` with `fₙ` analytic on
`Ω`, and `fₙ z = (2πi)⁻¹ ∮_{|ζ - a| = r} f ζ / ((ζ - a) ^ n * (ζ - z)) dζ` whenever the closed
disc of radius `r` about `a` lies in `Ω` and `z` lies inside the circle
(`Complex.exists_taylor_remainder_circleIntegral`).

The remainder is the `n`-fold divided difference `(swap dslope a)^[n] f`. The expansion follows
by induction from `sub_smul_dslope`, analyticity of the remainder from `differentiableOn_dslope`,
and the coefficients from the power series of `f` at `a` (`fslope`). On the circle the integrand
splits into the Cauchy kernel of `fₙ`, which integrates to `2πi fₙ z` by Cauchy's integral
formula, and terms `(ζ - z)⁻¹ (ζ - a) ^ m` with `m < 0`, whose integrals vanish after expanding
`(ζ - z)⁻¹` as a geometric series.

Mathlib has the Taylor series of a function differentiable on a ball
(`Complex.hasSum_taylorSeries_on_ball`) and the vanishing-coefficient case of the
divided-difference expansion (`pow_sub_smul_iterate_dslope_of_zero`), but not the finite
expansion with an analytic remainder, nor the integral formula for that remainder.

Rubric-guided revision of v1 ComplexVariables target 11 (`taylor_complex` in
`v1/Atlas/ComplexVariables/code/TaylorComplex.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`), Theorem 1 of the remarks on Lecture 10. The archived
statement dropped the theorem's "Moreover" clause, the Cauchy integral representation of `fₙ`;
it is now the third conjunct, for the same witness `fₙ`. The archived project definition
`complexTaylorPoly` is replaced by the inline sum. The source assumes a region; connectedness is
not needed, so `Ω` is only assumed open. The archived formalization and its original
license/provenance remain in `v1/` (the original license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open Function Metric
open scoped Nat Real

namespace Complex

/-- Expanding `f` by `n` successive divided differences at `a`. -/
private theorem sum_iterate_dslope_add (f : ℂ → ℂ) (a z : ℂ) (n : ℕ) :
    f z = ∑ k ∈ Finset.range n, (swap dslope a)^[k] f a * (z - a) ^ k +
      (swap dslope a)^[n] f z * (z - a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, iterate_succ_apply']
    set g := (swap dslope a)^[n] f
    have key : (z - a) * dslope g a z = g z - g a := sub_smul_dslope g a z
    rw [ih]
    change _ = _ + g a * (z - a) ^ n + dslope g a z * (z - a) ^ (n + 1)
    linear_combination -(z - a) ^ n * key

/-- The divided differences of a function differentiable on a neighbourhood `Ω` of `a` are
differentiable on `Ω`. -/
private theorem differentiableOn_iterate_dslope {f : ℂ → ℂ} {Ω : Set ℂ} {a : ℂ}
    (hΩ : IsOpen Ω) (ha : a ∈ Ω) (hf : DifferentiableOn ℂ f Ω) (n : ℕ) :
    DifferentiableOn ℂ ((swap dslope a)^[n] f) Ω := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [iterate_succ_apply']
    exact (differentiableOn_dslope (hΩ.mem_nhds ha)).2 ih

/-- At the base point, the `k`-th divided difference of an analytic function is its `k`-th Taylor
coefficient. -/
private theorem iterate_dslope_self {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (k : ℕ) :
    (swap dslope a)^[k] f a = iteratedDeriv k f a / k ! := by
  obtain ⟨p, hp⟩ := hf
  have hcoeff : (swap dslope a)^[k] f a = p.coeff k :=
    calc (swap dslope a)^[k] f a = (FormalMultilinearSeries.fslope^[k] p).coeff 0 :=
          ((hp.has_fpower_series_iterate_dslope_fslope k).coeff_zero 1).symm
      _ = p.coeff k := by rw [FormalMultilinearSeries.coeff_iterate_fslope, zero_add]
  obtain ⟨r, hpr⟩ := hp
  have hfac := hpr.factorial_smul 1 k
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul,
    nsmul_eq_mul] at hfac
  rw [hcoeff, ← hfac]
  exact (mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 k.factorial_ne_zero)).symm

/-- For `z` inside the circle `|ζ - a| = r` and a negative power `m`,
`∮ (ζ - z)⁻¹ (ζ - a) ^ m dζ = 0`. -/
private theorem circleIntegral_sub_inv_mul_sub_zpow_of_neg {a z : ℂ} {r : ℝ}
    (hz : z ∈ ball a r) {m : ℤ} (hm : m < 0) :
    ∮ ζ in C(a, r), (ζ - z)⁻¹ * (ζ - a) ^ m = 0 := by
  have hr : 0 < r := pos_of_mem_ball hz
  have hint : CircleIntegrable (fun ζ ↦ (ζ - a) ^ m) a r :=
    ContinuousOn.circleIntegrable hr.le <| (continuousOn_id.sub continuousOn_const).zpow₀ m
      fun ζ hζ ↦ Or.inl (sub_ne_zero.2 (ne_of_mem_sphere hζ hr.ne'))
  have hsum := hasSum_two_pi_I_cauchyPowerSeries_integral hint (mem_ball_iff_norm.1 hz)
  simp only [add_sub_cancel, smul_eq_mul] at hsum
  refine hsum.unique ?_
  convert hasSum_zero with j
  calc ∮ ζ in C(a, r), ((z - a) / (ζ - a)) ^ j * ((ζ - a)⁻¹ * (ζ - a) ^ m)
      = ∮ ζ in C(a, r), (z - a) ^ j * (ζ - a) ^ (m - j - 1) := by
        refine circleIntegral.integral_congr hr.le fun ζ hζ ↦ ?_
        have hζ : ζ - a ≠ 0 := sub_ne_zero.2 (ne_of_mem_sphere hζ hr.ne')
        simp only [zpow_sub₀ hζ, zpow_natCast, zpow_one, div_pow]
        field_simp
    _ = 0 := by
        rw [circleIntegral.integral_const_mul,
          circleIntegral.integral_sub_zpow_of_ne (show m - j - 1 ≠ -1 by omega), mul_zero]

/-- **Taylor's theorem** for analytic functions, with the Cauchy integral form of the remainder.

If `f` is analytic on an open set `Ω` containing `a`, then for every `n` there is a function `fₙ`,
analytic on `Ω`, such that
`f z = ∑ k < n, f⁽ᵏ⁾(a) / k! * (z - a) ^ k + fₙ z * (z - a) ^ n` for `z ∈ Ω`, and, whenever the
closed disc of radius `r` about `a` lies in `Ω`, for every `z` inside the circle `C(a, r)`
`fₙ z = (2πi)⁻¹ ∮_{C(a, r)} f ζ / ((ζ - a) ^ n * (ζ - z)) dζ`.
The source states this for a region (open and connected); connectedness is not needed. -/
public theorem exists_taylor_remainder_circleIntegral {f : ℂ → ℂ} {Ω : Set ℂ} {a : ℂ}
    (hΩ : IsOpen Ω) (ha : a ∈ Ω) (hf : AnalyticOnNhd ℂ f Ω) (n : ℕ) :
    ∃ fₙ : ℂ → ℂ, AnalyticOnNhd ℂ fₙ Ω ∧
      (∀ z ∈ Ω, f z = ∑ k ∈ Finset.range n, iteratedDeriv k f a / k ! * (z - a) ^ k +
        fₙ z * (z - a) ^ n) ∧
      ∀ r : ℝ, closedBall a r ⊆ Ω → ∀ z ∈ ball a r,
        fₙ z = (2 * π * I)⁻¹ * ∮ ζ in C(a, r), f ζ / ((ζ - a) ^ n * (ζ - z)) := by
  set g := (swap dslope a)^[n] f
  have hg : DifferentiableOn ℂ g Ω := differentiableOn_iterate_dslope hΩ ha hf.differentiableOn n
  have hexp (z : ℂ) : f z = ∑ k ∈ Finset.range n, iteratedDeriv k f a / k ! * (z - a) ^ k +
      g z * (z - a) ^ n := by
    simpa only [iterate_dslope_self (hf a ha)] using sum_iterate_dslope_add f a z n
  refine ⟨g, hg.analyticOnNhd hΩ, fun z _ ↦ hexp z, fun r hr z hz ↦ ?_⟩
  have hr0 : 0 < r := pos_of_mem_ball hz
  have hζa : ∀ ζ ∈ sphere a r, ζ - a ≠ 0 := fun ζ hζ ↦ sub_ne_zero.2 (ne_of_mem_sphere hζ hr0.ne')
  have hζz : ∀ ζ ∈ sphere a r, ζ - z ≠ 0 := by
    rintro ζ hζ h
    rw [sub_eq_zero] at h
    subst h
    exact (mem_ball.1 hz).ne (mem_sphere.1 hζ)
  have hinv : ContinuousOn (fun ζ ↦ (ζ - z)⁻¹) (sphere a r) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hζz
  -- On the circle, `f ζ / ((ζ - a) ^ n (ζ - z))` splits into multiples of
  -- `(ζ - z)⁻¹ (ζ - a) ^ (k - n)` with `k < n` and the Cauchy kernel of `g`.
  have hsplit : Set.EqOn (fun ζ ↦ f ζ / ((ζ - a) ^ n * (ζ - z)))
      (fun ζ ↦ ∑ k ∈ Finset.range n,
        iteratedDeriv k f a / k ! * ((ζ - z)⁻¹ * (ζ - a) ^ ((k : ℤ) - n)) + (ζ - z)⁻¹ * g ζ)
      (sphere a r) := by
    intro ζ hζ
    have h₁ := hζa ζ hζ
    have h₂ := hζz ζ hζ
    dsimp only
    rw [hexp ζ, add_div, Finset.sum_div]
    congr 1
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [mul_div_assoc, zpow_sub₀ h₁, zpow_natCast, zpow_natCast]
      congr 1
      field_simp
    · field_simp
  have hterm (k : ℕ) : ContinuousOn
      (fun ζ ↦ iteratedDeriv k f a / k ! * ((ζ - z)⁻¹ * (ζ - a) ^ ((k : ℤ) - n))) (sphere a r) :=
    continuousOn_const.mul (hinv.mul ((continuousOn_id.sub continuousOn_const).zpow₀ _
      fun ζ hζ ↦ Or.inl (hζa ζ hζ)))
  have hcauchy : ∮ ζ in C(a, r), (ζ - z)⁻¹ * g ζ = 2 * π * I * g z := by
    simpa only [smul_eq_mul] using (hg.mono hr).circleIntegral_sub_inv_smul hz
  have hzero : ∀ k ∈ Finset.range n,
      iteratedDeriv k f a / k ! * ∮ ζ in C(a, r), (ζ - z)⁻¹ * (ζ - a) ^ ((k : ℤ) - n) = 0 := by
    intro k hk
    have hkn := Finset.mem_range.1 hk
    rw [circleIntegral_sub_inv_mul_sub_zpow_of_neg hz (show (k : ℤ) - n < 0 by omega), mul_zero]
  have hkernel : CircleIntegrable (fun ζ ↦ (ζ - z)⁻¹ * g ζ) a r :=
    (hinv.mul (hg.continuousOn.mono (sphere_subset_closedBall.trans hr))).circleIntegrable hr0.le
  rw [circleIntegral.integral_congr hr0.le hsplit, circleIntegral.integral_add
    ((continuousOn_finsetSum (Finset.range n) fun k _ ↦ hterm k).circleIntegrable hr0.le) hkernel,
    hcauchy, circleIntegral.integral_fun_sum fun k _ ↦ (hterm k).circleIntegrable hr0.le]
  simp only [circleIntegral.integral_const_mul]
  rw [Finset.sum_eq_zero hzero, zero_add, inv_mul_cancel_left₀ two_pi_I_ne_zero]

end Complex
