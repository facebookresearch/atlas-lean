/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Chebyshev series of Lipschitz functions

The Chebyshev coefficients of a Lipschitz function on `[-1, 1]` are absolutely summable,
and the resulting Chebyshev series recovers the function on that interval.
The proof applies Parseval's identity to the difference quotients of the even periodic
function `θ ↦ f (cos θ)`. The module also defines the Chebyshev projection, the Chebyshev
interpolant, and the Bernstein ellipse.
-/

@[expose] public section

open AddCircle Filter MeasureTheory Polynomial Real Topology

namespace MathlibExt.Analysis.Approximation.ChebyshevInterpolationWanted

/-- The open Bernstein ellipse `E_ρ = {z : |z - 1| + |z + 1| < ρ + ρ⁻¹}` with foci `±1`. -/
def bernsteinEllipse (ρ : ℝ) : Set ℂ :=
  {z | ‖z - 1‖ + ‖z + 1‖ < ρ + ρ⁻¹}

/-- The `k`-th Chebyshev coefficient `a_k = (c_k/π) ∫_0^π f(cos θ) cos(k θ) dθ` of
`f : ℝ → ℂ` on `[-1, 1]`, with `c_0 = 1` and `c_k = 2` for `k ≥ 1` (ATAP Chapter 3). -/
noncomputable def chebCoeff (f : ℝ → ℂ) (k : ℕ) : ℂ :=
  (((if k = 0 then 1 else 2) / π : ℝ) : ℂ) *
    ∫ θ in (0 : ℝ)..π, f (cos θ) * (cos (k * θ) : ℂ)

/-- The Chebyshev projection `f_n(x) = ∑_{k ≤ n} a_k T_k(x)`, evaluated at `x`. -/
noncomputable def chebProj (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), chebCoeff f k * (((Chebyshev.T ℝ k).eval x : ℝ) : ℂ)

/-- The Chebyshev interpolant: the complex polynomial of degree `≤ n` interpolating `f` at the
Chebyshev points `x_j = cos(j π / n)`, `0 ≤ j ≤ n`. -/
noncomputable def chebInterp (f : ℝ → ℂ) (n : ℕ) : ℂ[X] :=
  Lagrange.interpolate (Finset.univ : Finset (Fin (n + 1)))
    (fun j => ((Chebyshev.node n j : ℝ) : ℂ)) (fun j => f (Chebyshev.node n j))

local instance twoPiPositive : Fact (0 < 2 * π) := ⟨by positivity⟩

private theorem fourier_two_pi (n : ℤ) (t : ℝ) :
    fourier n (t : AddCircle (2 * π)) = Complex.exp ((n : ℂ) * t * Complex.I) := by
  rw [fourier_coe_apply, Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr pi_ne_zero]

private theorem fourierCoeff_translate (g : AddCircle (2 * π) → ℂ)
    (n : ℤ) (a : AddCircle (2 * π)) :
    fourierCoeff (fun x => g (x + a)) n = fourier n a * fourierCoeff g n := by
  simp only [fourierCoeff, smul_eq_mul, ← integral_const_mul]
  rw [← integral_add_right_eq_self
    (fun x => fourier n a * (fourier (-n) x * g x)) a]
  congr 1
  funext x
  have h_add (i : ℤ) (x y : AddCircle (2 * π)) :
      fourier i (x + y) = fourier i x * fourier i y := by
    rw [fourier_apply, smul_add, toCircle_add, Circle.coe_mul, ← fourier_apply, ← fourier_apply]
  have h_cancel : fourier n a * fourier (-n) a = 1 := by
    rw [← fourier_add, add_neg_cancel, fourier_zero]
  rw [h_add]
  calc
    _ = (fourier n a * fourier (-n) a) * (fourier (-n) x * g (x + a)) := by
      rw [h_cancel, one_mul]
    _ = _ := by ring

private theorem fourierCoeff_differenceQuotient (g : C(AddCircle (2 * π), ℂ))
    (t : ℝ) (n : ℤ) :
    fourierCoeff (fun x => t⁻¹ • (g (x + (t : AddCircle (2 * π))) - g x)) n =
      (t⁻¹ • (fourier n (t : AddCircle (2 * π)) - 1)) * fourierCoeff g n := by
  have hsub :
      fourierCoeff (fun x => g (x + (t : AddCircle (2 * π))) - g x) n =
        fourierCoeff (fun x => g (x + (t : AddCircle (2 * π)))) n - fourierCoeff g n := by
    simp only [fourierCoeff, smul_sub]
    apply integral_sub
    all_goals
      exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
        (HasCompactSupport.of_compactSpace _)
  simp only [Complex.real_smul]
  change fourierCoeff ((↑t⁻¹ : ℂ) • (fun x => g (x + (t : AddCircle (2 * π))) - g x)) n = _
  rw [fourierCoeff.const_smul, hsub, fourierCoeff_translate, smul_eq_mul]
  ring

private theorem tendsto_fourier_differenceQuotient (n : ℤ) :
    Tendsto (fun t : ℝ => t⁻¹ • (fourier n (t : AddCircle (2 * π)) - 1))
      (𝓝[≠] 0) (𝓝 ((n : ℂ) * Complex.I)) := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp ((n : ℂ) * z * Complex.I))
      ((n : ℂ) * Complex.I) 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).const_mul (n : ℂ)).mul_const Complex.I).cexp
  simpa only [zero_add, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, fourier_two_pi]
    using h.comp_ofReal.tendsto_slope_zero

private theorem summable_weighted_fourierCoeff {g : C(AddCircle (2 * π), ℂ)} {K : NNReal}
    (hg : ∀ x (t : ℝ), ‖g (x + (t : AddCircle (2 * π))) - g x‖ ≤ (K : ℝ) * |t|) :
    Summable (fun n : ℤ => (‖(n : ℂ) * Complex.I * fourierCoeff g n‖ ^ 2 : ℝ)) := by
  -- Take the limit for each finite set of frequencies under the same Parseval bound.
  apply summable_of_sum_le (c := (K : ℝ) ^ 2) (fun n => sq_nonneg _)
  intro s
  let q (t : ℝ) : C(AddCircle (2 * π), ℂ) :=
    ⟨fun x => t⁻¹ • (g (x + (t : AddCircle (2 * π))) - g x), by fun_prop⟩
  have hlim (n : ℤ) :
      Tendsto (fun t : ℝ => ‖fourierCoeff (q t) n‖ ^ 2)
        (𝓝[≠] 0) (𝓝 (‖(n : ℂ) * Complex.I * fourierCoeff g n‖ ^ 2)) := by
    simpa only [q, ContinuousMap.coe_mk, fourierCoeff_differenceQuotient] using
      ((tendsto_fourier_differenceQuotient n).mul_const (fourierCoeff g n)).norm.pow 2
  refine le_of_tendsto (tendsto_finsetSum s fun n _ => hlim n) ?_
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := {0}ᶜ)] with t ht
  have ht0 : t ≠ 0 := ht
  have hbound (x : AddCircle (2 * π)) : ‖q t x‖ ≤ (K : ℝ) := by
    calc
      ‖q t x‖ = |t|⁻¹ * ‖g (x + (t : AddCircle (2 * π))) - g x‖ := by
        simp [q, Real.norm_eq_abs]
      _ ≤ |t|⁻¹ * ((K : ℝ) * |t|) := by gcongr; exact hg x t
      _ = K := by field_simp [abs_ne_zero.mpr ht0]
  let q₂ := ContinuousMap.toLp 2 haarAddCircle ℂ (q t)
  have hsum := hasSum_sq_fourierCoeff q₂
  simp_rw [q₂, fourierCoeff_toLp] at hsum
  refine (hsum.summable.sum_le_tsum s (fun n _ => sq_nonneg _)).trans ?_
  rw [hsum.tsum_eq]
  have h_integral :
      (∫ x, ‖q₂ x‖ ^ 2 ∂haarAddCircle) = ∫ x, ‖q t x‖ ^ 2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℂ) (q t)] with x hx
    rw [show q₂ x = q t x from hx]
  have hconst : (∫ _ : AddCircle (2 * π), (K : ℝ) ^ 2 ∂haarAddCircle) = (K : ℝ) ^ 2 := by
    simp
  rw [h_integral, ← hconst]
  exact integral_mono
    (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
    (integrable_const _) (fun x => pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2)


private theorem summable_norm_fourierCoeff {g : C(AddCircle (2 * π), ℂ)} {K : NNReal}
    (hg : ∀ x (t : ℝ), ‖g (x + (t : AddCircle (2 * π))) - g x‖ ≤ (K : ℝ) * |t|) :
    Summable (fun n : ℤ => ‖fourierCoeff g n‖) := by
  have hWeight := summable_weighted_fourierCoeff hg
  have hInv : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hZero : Summable (fun n : ℤ => if n = 0 then ‖fourierCoeff g 0‖ else 0) :=
    summable_of_hasFiniteSupport <| (Set.finite_singleton (0 : ℤ)).subset <| by
      intro n hn
      by_contra hne
      exact hn (ite_eq_right hne)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ ((hWeight.add hInv).add hZero)
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hproduct :
        ‖(n : ℂ) * Complex.I * fourierCoeff g n‖ * |(n : ℝ)|⁻¹ = ‖fourierCoeff g n‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast]
      field_simp [abs_ne_zero.mpr hnR]
    have hinv : (|(n : ℝ)|⁻¹) ^ 2 = 1 / (n : ℝ) ^ 2 := by rw [inv_pow, sq_abs, one_div]
    have hAM := two_mul_le_add_pow_two ‖(n : ℂ) * Complex.I * fourierCoeff g n‖ |(n : ℝ)|⁻¹
    rw [mul_assoc, hproduct, hinv] at hAM
    simp only [hn, ite_false, add_zero]
    linarith [norm_nonneg (fourierCoeff g n)]

private theorem fourierCoeff_eq_cos_integral {f : ℝ → ℂ} {g : C(AddCircle (2 * π), ℂ)}
    (hg : ∀ t : ℝ, g (t : AddCircle (2 * π)) = f (cos t)) (n : ℤ) :
    fourierCoeff g n = (1 / π : ℝ) • ∫ t in (0 : ℝ)..π, f (cos t) * (cos (n * t) : ℂ) := by
  have hcont : Continuous (fun t : ℝ => f (cos t)) := by
    simp_rw [← hg]
    exact g.continuous.comp (AddCircle.continuous_mk' _)
  let F (t : ℝ) : ℂ := Complex.exp ((-n : ℤ) * (t : ℂ) * Complex.I) * f (cos t)
  have hF : Continuous F := by
    apply Continuous.mul (by fun_prop) hcont
  rw [fourierCoeff_eq_intervalIntegral _ _ (-π), show -π + 2 * π = π by ring]
  simp_rw [hg, fourier_two_pi, smul_eq_mul]
  change (1 / (2 * π) : ℝ) • (∫ t in -π..π, F t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (-π) 0) (hF.intervalIntegrable 0 π)]
  rw [← show (∫ t in (0 : ℝ)..π, F (-t)) = ∫ t in -π..(0 : ℝ), F t by
    simpa only [neg_zero] using intervalIntegral.integral_comp_neg F (a := 0) (b := π)]
  have hFneg : Continuous (fun t => F (-t)) := by fun_prop
  rw [← intervalIntegral.integral_add (hFneg.intervalIntegrable 0 π) (hF.intervalIntegrable 0 π)]
  have hpair (t : ℝ) : F (-t) + F t = (2 : ℂ) * (f (cos t) * (cos (n * t) : ℂ)) := by
    rw [Complex.ofReal_cos, mul_left_comm, Complex.ofReal_mul, Complex.ofReal_intCast,
      Complex.two_cos, mul_add]
    have h₁ : -(n : ℂ) * -(t : ℂ) * Complex.I = (n : ℂ) * t * Complex.I := by ring
    have h₂ : -(n : ℂ) * (t : ℂ) * Complex.I = -((n : ℂ) * t) * Complex.I := by ring
    simp only [F, cos_neg, Int.cast_neg, Complex.ofReal_neg, h₁, h₂]
    ring
  simp_rw [hpair, intervalIntegral.integral_const_mul, Complex.real_smul]
  push_cast
  field_simp

private theorem chebCoeff_eq_fourierCoeff {f : ℝ → ℂ} {g : C(AddCircle (2 * π), ℂ)}
    (hg : ∀ t : ℝ, g (t : AddCircle (2 * π)) = f (cos t)) (k : ℕ) :
    chebCoeff f k = (if k = 0 then 1 else 2 : ℂ) * fourierCoeff g k := by
  rw [chebCoeff, fourierCoeff_eq_cos_integral hg, Complex.real_smul]
  push_cast
  split_ifs <;> push_cast <;> ring

/-- **Chebyshev series of Lipschitz functions** (ATAP Theorem 3.1): if `f` is Lipschitz on
`[-1, 1]`, its Chebyshev coefficients are absolutely summable and `f(x) = ∑ a_k T_k(x)` for every
`x ∈ [-1, 1]` (so the series converges absolutely and uniformly). -/
theorem hasSum_chebCoeff_of_lipschitz {f : ℝ → ℂ} {K : NNReal}
    (hf : LipschitzOnWith K f (Set.Icc (-1) 1)) :
    Summable (fun k => ‖chebCoeff f k‖) ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        HasSum (fun k => chebCoeff f k * (((Chebyshev.T ℝ k).eval x : ℝ) : ℂ)) (f x) := by
  have hLip : LipschitzWith K (fun t => f (cos t)) := by
    intro t u
    have hcos : edist (cos t) (cos u) ≤ edist t u := by
      simpa only [ENNReal.coe_one, one_mul] using Real.lipschitzWith_cos t u
    refine (hf (cos_mem_Icc t) (cos_mem_Icc u)).trans ?_
    gcongr
  have hper : Function.Periodic (fun t => f (cos t)) (2 * π) :=
    fun t => congrArg f (Real.cos_periodic t)
  let g : C(AddCircle (2 * π), ℂ) := ⟨hper.lift, by
    apply (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
    simpa only [Function.comp_def, hper.lift_coe] using hLip.continuous⟩
  have hg (t : ℝ) : g (t : AddCircle (2 * π)) = f (cos t) := hper.lift_coe t
  have hnorm : Summable (fun n : ℤ => ‖fourierCoeff g n‖) := by
    apply summable_norm_fourierCoeff (K := K)
    intro x t
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [← AddCircle.coe_add, hg, hg]
    simpa only [add_sub_cancel_left, Real.norm_eq_abs] using hLip.norm_sub_le (u + t) u
  constructor
  · have hnat := hnorm.comp_injective (i := fun k : ℕ => (k : ℤ)) Nat.cast_injective
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ (hnat.mul_left 2)
    intro k
    rw [chebCoeff_eq_fourierCoeff hg, norm_mul]
    dsimp only [Function.comp_apply]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    split_ifs <;> norm_num
  intro x hx
  obtain ⟨θ, _, rfl⟩ := Real.surjOn_cos hx
  let F (n : ℤ) := fourierCoeff g n * fourier n (θ : AddCircle (2 * π))
  let A (k : ℕ) := chebCoeff f k * (((Chebyshev.T ℝ k).eval (cos θ) : ℝ) : ℂ)
  have hF : HasSum F (f (cos θ)) := by
    simpa only [F, smul_eq_mul, hg] using
      has_pointwise_sum_fourier_series_of_summable hnorm.of_norm (θ : AddCircle (2 * π))
  have hnat : Summable (fun k : ℕ => F k) :=
    hF.summable.comp_injective Nat.cast_injective
  have hpos := (summable_nat_add_iff 1).mpr hnat
  have hneg : Summable (fun k : ℕ => F (-((k : ℤ) + 1))) :=
    hF.summable.comp_injective (i := fun k : ℕ => -((k : ℤ) + 1)) (by
      intro i j h
      exact Nat.cast_injective (add_right_cancel (neg_injective h)))
  -- Pair opposite frequencies, counting the mode at zero just once.
  have hzero : A 0 = F 0 := by
    simp [A, F, chebCoeff_eq_fourierCoeff hg]
  have hpair (k : ℕ) (hk : k ≠ 0) : A k = F k + F (-(k : ℤ)) := by
    have hnegCoeff : fourierCoeff g (-(k : ℤ)) = fourierCoeff g k := by
      rw [fourierCoeff_eq_cos_integral hg, fourierCoeff_eq_cos_integral hg]
      simp only [Int.cast_neg, neg_mul, cos_neg]
    simp only [A, F, chebCoeff_eq_fourierCoeff hg, ite_eq_right hk, hnegCoeff,
      Chebyshev.T_real_cos, fourier_two_pi, Int.cast_neg, Int.cast_natCast,
      Complex.ofReal_cos, Complex.ofReal_mul, Complex.ofReal_natCast]
    rw [mul_comm (2 : ℂ) (fourierCoeff g k), mul_assoc, Complex.two_cos, mul_add]
    simp only [neg_mul]
  change HasSum A (f (cos θ))
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.range_one, Finset.sum_singleton, hzero]
  have htail := hpos.hasSum.add hneg.hasSum
  have htotal : ((∑' k : ℕ, F ((k + 1 : ℕ) : ℤ)) +
      ∑' k : ℕ, F (-((k : ℤ) + 1))) = f (cos θ) - F 0 := by
    apply eq_sub_of_add_eq
    rw [add_comm _ (F 0), ← add_assoc]
    have hnat' := hnat.tsum_eq_zero_add
    simp only [Nat.cast_zero] at hnat'
    rw [← hnat', ← tsum_of_nat_of_neg_add_one hnat hneg, hF.tsum_eq]
  rw [← htotal]
  refine htail.congr_fun fun k => ?_
  simpa only [Nat.cast_add, Nat.cast_one] using hpair (k + 1) (by omega)

end MathlibExt.Analysis.Approximation.ChebyshevInterpolationWanted
