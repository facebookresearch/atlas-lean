/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.EntireOrder
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Hadamard factorization of entire functions of order at most one

An entire function `f` of order of growth at most `1` with `f 0 ≠ 0` and zeros `z₁, z₂, …`,
listed with multiplicity, factors as
`f s = exp (A + B s) ∏ₙ (1 - s / zₙ) exp (s / zₙ)`.
The product converges absolutely because `∑ ‖zₙ‖⁻² < ∞`
(`Complex.HasGrowthOrderLE.summable_norm_rpow_neg`).

The proof divides `f` by the canonical product `P`, takes an entire logarithm `H` of the
zero-free quotient, bounds `Re H` from above by `O(‖s‖ ^ (1 + ε))` using a lower bound for `P` on
circles that keep away from the zeros, and concludes with a Borel–Carathéodory argument that `H`
is affine.

## Main statements

* `Complex.exists_differentiable_eq_cexp_of_ne_zero`: a zero-free entire function is `exp ∘ h`
  for an entire `h`.
* `Complex.iteratedDeriv_eq_zero_of_re_le_rpow`: if `Re h z ≤ A + D ‖z‖ ^ s`, then the Taylor
  coefficients of the entire function `h` at `0` vanish beyond `s`.
* `Complex.eq_sum_range_of_iteratedDeriv_eq_zero`: an entire function whose Taylor coefficients
  vanish beyond `N` is a polynomial of degree at most `N`.
* `Complex.exists_eq_mul_of_re_le_rpow_one_add`: an entire `h` with `h 0 = 0` and
  `Re h z ≤ C_ε ‖z‖ ^ (1 + ε)` at infinity, for every `ε > 0`, is linear.
* `Complex.card_sigma_fin_analyticOrderAt`: the zeros of an entire function that is not
  identically zero, listed with multiplicity, are indexed by `Σ w, Fin (analyticOrderAt f w).toNat`.
* `Complex.exists_eq_exp_mul_tprod_of_hasGrowthOrderLE_one`: **Hadamard's factorization
  theorem** for entire functions of order at most `1`.
* `Complex.exists_eq_exp_mul_tprod_sigma_of_hasGrowthOrderLE_one`: the same, with the zeros
  indexed by `Σ w, Fin (analyticOrderAt f w).toNat`.
-/

@[expose] public section

open Filter Asymptotics Bornology Metric Topology

namespace Complex

/-! ### Entire functions with constrained real part -/

/-- **An entire logarithm.** A zero-free entire `f` is `exp ∘ h` for an entire `h` with
`h 0 = log (f 0)`: `h` is the primitive of `f' / f`. -/
theorem exists_differentiable_eq_cexp_of_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : ∀ z, f z ≠ 0) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ h 0 = Complex.log (f 0) ∧
      ∀ z, f z = Complex.exp (h z) := by
  have hφ : Differentiable ℂ (fun z => deriv f z / f z) := hf.deriv.div hf hf0
  obtain ⟨h, hh0, hhd⟩ := hφ.isExactOn_univ.with_val_at 0 (Complex.log (f 0))
  have hdiff : Differentiable ℂ h := fun z => (hhd z (Set.mem_univ z)).differentiableAt
  refine ⟨h, hdiff, hh0, ?_⟩
  have hd : ∀ z, HasDerivAt (fun z => f z * Complex.exp (-h z)) 0 z := by
    intro z
    have h2 : HasDerivAt (fun w => -h w) (-(deriv f z / f z)) z :=
      (hhd z (Set.mem_univ z)).neg
    have h1 : HasDerivAt (fun w => f w * Complex.exp (-h w))
        (deriv f z * Complex.exp (-h z) + f z * (Complex.exp (-h z) * -(deriv f z / f z))) z :=
      (hf z).hasDerivAt.mul h2.cexp
    convert h1 using 1
    field_simp [hf0 z]
    ring
  have hc : ∀ z, f z * Complex.exp (-h z) = 1 := by
    intro z
    have := is_const_of_deriv_eq_zero (fun z => (hd z).differentiableAt)
      (fun z => (hd z).deriv) z 0
    rw [this, hh0, Complex.exp_neg, Complex.exp_log (hf0 0), mul_inv_cancel₀ (hf0 0)]
  intro z
  have := hc z
  rw [Complex.exp_neg] at this
  field_simp at this
  exact this

/-- **Polynomial growth of the real part kills the high Taylor coefficients.** If `h` is
entire and `Re h z ≤ A + D ‖z‖ ^ s` with `s > 0`, `D ≥ 0`, then `h⁽ⁿ⁾ 0 = 0` for every
`n > s`. The proof bounds `‖h - h 0‖` on circles by the Borel–Carathéodory theorem and applies
the Cauchy estimates. -/
theorem iteratedDeriv_eq_zero_of_re_le_rpow {h : ℂ → ℂ} (hdiff : Differentiable ℂ h)
    {A D s : ℝ} (hs0 : 0 < s) (hD : 0 ≤ D) (hA : ∀ z, (h z).re ≤ A + D * ‖z‖ ^ s)
    {n : ℕ} (hsn : s < n) : iteratedDeriv n h 0 = 0 := by
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  set B := |A| + |(h 0).re| + 1 with hB
  have hBpos : 0 < B := by positivity
  have hbound : ∀ r ≥ (1 : ℝ), ‖iteratedDeriv n h 0‖ ≤
      n.factorial * (2 * (B + D * 2 ^ s) * r ^ (-((n : ℝ) - s))) := by
    intro r hr
    have hr0 : 0 < r := by linarith
    rw [← iteratedDeriv_const_add hnpos (-h 0)]
    have hd' : Differentiable ℂ (fun w => -h 0 + h w) := (differentiable_const _).add hdiff
    have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0)
      (C := 2 * (B + D * (2 * r) ^ s)) n hr0 hd'.diffContOnCl (fun z hz => ?_)
    · have e : r ^ (-((n : ℝ) - s)) = r ^ s / r ^ n := by
        rw [show -((n : ℝ) - s) = s - n by ring, Real.rpow_sub hr0, Real.rpow_natCast]
      have h2 : (2 * r) ^ s = 2 ^ s * r ^ s := Real.mul_rpow (by norm_num) hr0.le
      have h1 : 1 ≤ r ^ s := Real.one_le_rpow hr hs0.le
      have hrn : 0 < r ^ n := by positivity
      have h22 : 0 < (2 : ℝ) ^ s := by positivity
      refine hC.trans ?_
      calc (n.factorial : ℝ) * (2 * (B + D * (2 * r) ^ s)) / r ^ n
          = n.factorial * (2 * (B + D * (2 * r) ^ s)) * (r ^ n)⁻¹ := div_eq_mul_inv _ _
        _ ≤ n.factorial * (2 * (B + D * 2 ^ s) * r ^ s) * (r ^ n)⁻¹ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
            (by positivity)
          rw [h2]
          nlinarith [mul_nonneg hD h22.le]
        _ = n.factorial * (2 * (B + D * 2 ^ s) * r ^ (-((n : ℝ) - s))) := by
          rw [e]
          ring
    · rw [mem_sphere_zero_iff_norm] at hz
      rw [show -h 0 + h z = h z - h 0 by ring]
      have hBC := Complex.borelCaratheodory_zero (f := fun w => h w - h 0) (R := 2 * r)
        (M := B + D * (2 * r) ^ s) (by positivity) (hdiff.sub_const _).differentiableOn
        (fun w hw => ?_) (by positivity) (by rw [mem_ball_zero_iff]; linarith) (by simp)
      · rw [hz, show 2 * r - r = r by ring, mul_div_assoc, div_self hr0.ne', mul_one] at hBC
        exact hBC
      · have hw' : ‖w‖ < 2 * r := mem_ball_zero_iff.mp hw
        have := hA w
        have : ‖w‖ ^ s ≤ (2 * r) ^ s := Real.rpow_le_rpow (norm_nonneg _) hw'.le hs0.le
        have : D * ‖w‖ ^ s ≤ D * (2 * r) ^ s := by gcongr
        simp only [Set.mem_ofPred_eq, Complex.sub_re]
        linarith [neg_abs_le (h 0).re, le_abs_self A]
  have hlim : Tendsto
      (fun r : ℝ => (n.factorial : ℝ) * (2 * (B + D * 2 ^ s) * r ^ (-((n : ℝ) - s))))
      atTop (𝓝 ((n.factorial : ℝ) * (2 * (B + D * 2 ^ s) * 0))) :=
    ((tendsto_rpow_neg_atTop (by linarith)).const_mul _).const_mul _
  have := ge_of_tendsto hlim (eventually_atTop.mpr ⟨1, hbound⟩)
  simp only [mul_zero] at this
  exact norm_le_zero_iff.mp this

/-- An entire function whose Taylor coefficients at `0` vanish beyond `N` is its degree-`N`
Taylor polynomial. -/
theorem eq_sum_range_of_iteratedDeriv_eq_zero {h : ℂ → ℂ} (hdiff : Differentiable ℂ h)
    {N : ℕ} (hzero : ∀ n, N < n → iteratedDeriv n h 0 = 0) (z : ℂ) :
    h z = ∑ n ∈ Finset.range (N + 1), (n.factorial : ℂ)⁻¹ * iteratedDeriv n h 0 * z ^ n := by
  have hs := Complex.hasSum_taylorSeries_of_entire hdiff 0 z
  have hs2 : HasSum (fun n => ((n.factorial : ℂ))⁻¹ • (z - 0) ^ n • iteratedDeriv n h 0)
      (∑ n ∈ Finset.range (N + 1), ((n.factorial : ℂ))⁻¹ • (z - 0) ^ n • iteratedDeriv n h 0) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => ?_)
  · rw [hs.unique hs2]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [smul_eq_mul, sub_zero]
    ring
  · have h1 : N < n := by simpa using hn
    simp [hzero n h1]

/-- **An entire function whose real part grows at most like `‖z‖ ^ (1 + ε)` is affine.** An
entire `h` with `h 0 = 0` whose real part is bounded *above* by `C_ε ‖z‖ ^ (1 + ε)` at infinity,
for every `ε > 0`, is linear: `h z = B z`. The bound is one-sided, which is what is needed to pass
from `‖exp (h z)‖ ≪ exp (‖z‖ ^ (1 + ε))` to the shape of `h`. -/
theorem exists_eq_mul_of_re_le_rpow_one_add {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (h0 : h 0 = 0)
    (hre : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
      ∀ᶠ z in cocompact ℂ, (h z).re ≤ C * ‖z‖ ^ (1 + ε)) :
    ∃ B : ℂ, ∀ z, h z = B * z := by
  -- Step 1: `Re h ≤ A + D ‖z‖ ^ s` everywhere, with `s = 3 / 2`.
  set s : ℝ := 3 / 2 with hs
  obtain ⟨C, hC⟩ := hre (1 / 2) (by norm_num)
  have hRe : ∃ A > (0 : ℝ), ∀ z, (h z).re ≤ A + |C| * ‖z‖ ^ s := by
    rw [← Metric.cobounded_eq_cocompact] at hC
    obtain ⟨R0, -, hR0⟩ :=
      (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.mp hC
    obtain ⟨C0, hC0⟩ := (isCompact_closedBall (0 : ℂ) R0).exists_bound_of_continuousOn
      hh.continuous.continuousOn
    refine ⟨|C0| + 1, by positivity, fun z => ?_⟩
    have hpow : 0 ≤ ‖z‖ ^ s := Real.rpow_nonneg (norm_nonneg z) s
    have hCa : 0 ≤ |C| * ‖z‖ ^ s := by positivity
    by_cases hz : z ∈ closedBall (0 : ℂ) R0
    · have := hC0 z hz
      have := Complex.re_le_norm (h z)
      have := le_abs_self C0
      linarith
    · have h1 := hR0 hz
      rw [show (1 : ℝ) + 1 / 2 = s by norm_num [hs]] at h1
      have : C * ‖z‖ ^ s ≤ |C| * ‖z‖ ^ s := by gcongr; exact le_abs_self C
      have := abs_nonneg C0
      linarith
  obtain ⟨A, hA, hA'⟩ := hRe
  set D := |C| + 1 with hD
  have hDpos : 0 < D := by positivity
  have hA'' : ∀ z, (h z).re ≤ A + D * ‖z‖ ^ s := by
    intro z
    have := hA' z
    have : |C| * ‖z‖ ^ s ≤ D * ‖z‖ ^ s := by
      have := Real.rpow_nonneg (norm_nonneg z) s
      nlinarith
    linarith
  -- Step 2: the Taylor coefficients of `h` at `0` vanish from order 2 on.
  have hzero : ∀ n : ℕ, 1 < n → iteratedDeriv n h 0 = 0 := by
    intro n hn
    refine iteratedDeriv_eq_zero_of_re_le_rpow hh (by norm_num [hs]) hDpos.le hA'' ?_
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [hs]; linarith
  -- Step 3: `h` is its degree-one Taylor polynomial.
  refine ⟨iteratedDeriv 1 h 0, fun z => ?_⟩
  rw [eq_sum_range_of_iteratedDeriv_eq_zero hh hzero z]
  simp [Finset.sum_range_succ, h0]

/-! ### Enumerating the zeros of an entire function -/

section ZeroEnumeration

variable {f : ℂ → ℂ}

/-- An entire function that is not identically zero vanishes to finite order everywhere. -/
theorem analyticOrderAt_ne_top_of_differentiable (hd : Differentiable ℂ f) {w₀ : ℂ}
    (h₀ : f w₀ ≠ 0) (w : ℂ) : analyticOrderAt f w ≠ ⊤ := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun x _ => hd.analyticAt x
  exact ha.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ w₀) (Set.mem_univ w) (by
      rw [Ne, analyticOrderAt_eq_top]
      intro h
      exact h₀ h.self_of_nhds)

/-- For an entire `f` that is not identically zero, `Sigma.fst` on
`Σ w, Fin (analyticOrderAt f w).toNat` lists the zeros of `f` with multiplicity: its fibre over
`w` has `analyticOrderAt f w` elements. -/
theorem card_sigma_fin_analyticOrderAt (hd : Differentiable ℂ f) {w₀ : ℂ} (h₀ : f w₀ ≠ 0)
    (w : ℂ) :
    ENat.card {n : (Σ w : ℂ, Fin (analyticOrderAt f w).toNat) // n.1 = w} =
      analyticOrderAt f w := by
  rw [ENat.card_congr (Equiv.sigmaSubtype w), ENat.card_eq_coe_fintype_card,
    Fintype.card_fin]
  exact ENat.natCast_toNat (analyticOrderAt_ne_top_of_differentiable hd h₀ w)

/-- Every point of the enumeration `Σ w, Fin (analyticOrderAt f w).toNat` is a zero of `f`. -/
theorem apply_fst_eq_zero_of_sigma_fin_analyticOrderAt
    (n : Σ w : ℂ, Fin (analyticOrderAt f w).toNat) : f n.1 = 0 := by
  by_contra h
  have h0 : (analyticOrderAt f n.1).toNat = 0 := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr h)]; rfl
  exact absurd n.2.isLt (by omega)

end ZeroEnumeration

/-! ### Hadamard's factorization theorem -/

/-- **Hadamard's factorization theorem for entire functions of order at most `1`.** Let `f` be
entire of order of growth at most `1` with `f 0 ≠ 0`, and let `z : ι → ℂ` list the zeros of `f`
with multiplicity, i.e. the fibre of `z` over each `w` has `analyticOrderAt f w` elements. Then
there are constants `A, B` with
`f s = exp (A + B s) ∏ₙ (1 - s / zₙ) exp (s / zₙ)` for all `s`.

The index type is arbitrary (`ι = ℕ` is the classical indexing, and a finite `ι` covers functions
with finitely many zeros). The product is an unconditional `tprod`, which converges because
`∑ ‖zₙ‖⁻² < ∞`, so the zeros need not be ordered. Evaluating at `0` gives `exp A = f 0`, which is
why `f 0 ≠ 0` is assumed; it also makes every `zₙ` nonzero. -/
theorem exists_eq_exp_mul_tprod_of_hasGrowthOrderLE_one {ι : Type*} {f : ℂ → ℂ} {z : ι → ℂ}
    (hf : Differentiable ℂ f) (h1 : HasGrowthOrderLE f 1) (hf0 : f 0 ≠ 0)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt f w) :
    ∃ A B : ℂ, ∀ s, f s =
      Complex.exp (A + B * s) * ∏' n, (1 - s / z n) * Complex.exp (s / z n) := by
  classical
  -- generic facts about `log (1 - w) + w`
  have hℓ : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ‖Complex.log (1 - w) + w‖ ≤ ‖w‖ ^ 2 := by
    intro w hw
    have h := Complex.norm_log_one_add_sub_self_le (z := -w) (by rw [norm_neg]; linarith)
    rw [norm_neg, ← sub_eq_add_neg, sub_neg_eq_add] at h
    refine h.trans ?_
    have h1 : (1 - ‖w‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h2 : 0 ≤ ‖w‖ ^ 2 := by positivity
    nlinarith
  have hexpℓ : ∀ w : ℂ, ‖w‖ < 1 →
      Complex.exp (Complex.log (1 - w) + w) = (1 - w) * Complex.exp w := by
    intro w hw
    rw [Complex.exp_add, Complex.exp_log]
    intro h0
    have : w = 1 := by linear_combination -h0
    rw [this, norm_one] at hw
    exact lt_irrefl _ hw
  have hslit : ∀ w : ℂ, ‖w‖ < 1 → 1 - w ∈ Complex.slitPlane := by
    intro w hw
    have : w.re < 1 := lt_of_le_of_lt (Complex.re_le_norm w) hw
    exact Or.inl (by simp; linarith)
  -- generic real inequalities
  have hrp2 : ∀ d R x : ℝ, 0 ≤ d → d ≤ 1 → 0 < R → 0 < x → x ≤ 2 * R →
      R / x ≤ 2 * (R ^ (1 + d) * x ^ (-(1 + d))) := by
    intro d R x hd0 hd1 hR hx hxR
    have e : R ^ (1 + d) * x ^ (-(1 + d)) = (R / x) * (R / x) ^ d := by
      rw [Real.rpow_neg hx.le, ← div_eq_mul_inv, ← Real.div_rpow hR.le hx.le,
        Real.rpow_add (by positivity), Real.rpow_one]
    have h1 : (1 / 2 : ℝ) ≤ R / x := by rw [div_le_div_iff₀ (by norm_num) hx]; linarith
    have h2 : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ d :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hd1
    have h3 : (1 / 2 : ℝ) ^ d ≤ (R / x) ^ d := Real.rpow_le_rpow (by norm_num) h1 hd0
    rw [Real.rpow_one] at h2
    rw [e]
    have : 0 < R / x := by positivity
    nlinarith
  have hrp3 : ∀ d R x : ℝ, 0 ≤ d → d ≤ 1 → 0 < R → R ≤ x →
      R ^ 2 * (x ^ 2)⁻¹ ≤ R ^ (1 + d) * x ^ (-(1 + d)) := by
    intro d R x hd0 hd1 hR hRx
    have hx : 0 < x := by linarith
    rw [Real.rpow_neg hx.le, ← div_eq_mul_inv, ← div_eq_mul_inv, ← div_pow,
      ← Real.div_rpow hR.le hx.le]
    have h1 : R / x ≤ 1 := by rw [div_le_one hx]; exact hRx
    have := Real.rpow_le_rpow_of_exponent_ge (by positivity) h1 (show 1 + d ≤ (2 : ℕ) by
      push_cast; linarith)
    rwa [Real.rpow_natCast] at this
  have hgen : ∀ K a θ ρ N : ℝ, 0 ≤ K → 0 ≤ a → 0 < θ → 1 ≤ ρ → 0 ≤ N →
      N ≤ K * (4 * ρ) ^ a →
      N * Real.log (8 * (N + 1)) ≤
        K * 4 ^ a * ((8 * (K * 4 ^ a + 1)) ^ θ / θ) * ρ ^ (a * (1 + θ)) := by
    intro K a θ ρ N hK ha hθ hρ hN0 hN
    have hρa : 1 ≤ ρ ^ a := Real.one_le_rpow hρ ha
    have h4 : (4 * ρ) ^ a = 4 ^ a * ρ ^ a := Real.mul_rpow (by norm_num) (by linarith)
    have hK4 : 0 ≤ K * 4 ^ a := by positivity
    have hN' : N ≤ K * 4 ^ a * ρ ^ a := by rw [h4] at hN; linarith
    have h8 : 8 * (N + 1) ≤ 8 * (K * 4 ^ a + 1) * ρ ^ a := by nlinarith
    have hlog := Real.log_le_rpow_div (x := 8 * (N + 1)) (by positivity) hθ
    have hpow : (8 * (N + 1)) ^ θ ≤ (8 * (K * 4 ^ a + 1)) ^ θ * ρ ^ (a * θ) := by
      calc (8 * (N + 1)) ^ θ ≤ (8 * (K * 4 ^ a + 1) * ρ ^ a) ^ θ :=
            Real.rpow_le_rpow (by positivity) h8 hθ.le
        _ = _ := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by linarith)]
    have hsplit : ρ ^ (a * (1 + θ)) = ρ ^ a * ρ ^ (a * θ) := by
      rw [show a * (1 + θ) = a + a * θ by ring, Real.rpow_add (by linarith)]
    have hlog0 : 0 ≤ Real.log (8 * (N + 1)) := Real.log_nonneg (by linarith)
    calc N * Real.log (8 * (N + 1))
        ≤ (K * 4 ^ a * ρ ^ a) * ((8 * (K * 4 ^ a + 1)) ^ θ * ρ ^ (a * θ) / θ) :=
          mul_le_mul hN' (hlog.trans (div_le_div_of_nonneg_right hpow hθ.le)) hlog0
            (by positivity)
      _ = _ := by rw [hsplit]; ring
  -- basic facts about `f` and its zeros
  have h00 : analyticOrderAt f 0 = 0 := (hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hf0
  have hz0 : ∀ n, z n ≠ 0 := by
    intro n h
    have : IsEmpty {m // z m = 0} := (ENat.card_eq_zero_iff_empty _).mp (by rw [hz 0, h00])
    exact this.false ⟨n, h⟩
  have hzpos : ∀ n, 0 < ‖z n‖ := fun n => norm_pos_iff.mpr (hz0 n)
  have hsum2 : Summable fun n => (‖z n‖ ^ 2)⁻¹ := by
    refine (h1.summable_norm_rpow_neg hf zero_le_one hf0 hz one_pos).congr fun n => ?_
    rw [show (-(1 : ℝ) - 1) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg _),
      Real.rpow_natCast]
  have hfinite : ∀ T : ℝ, {n | ‖z n‖ ≤ T}.Finite := by
    intro T
    have hc : 0 < ((max T 1) ^ 2)⁻¹ := by positivity
    have hev := hsum2.tendsto_cofinite_zero.eventually (gt_mem_nhds hc)
    rw [Filter.eventually_cofinite] at hev
    refine hev.subset fun n hn => ?_
    simp only [Set.mem_ofPred_eq, not_lt] at hn ⊢
    have h1 : ‖z n‖ ≤ max T 1 := le_trans hn (le_max_left _ _)
    have h2 : ‖z n‖ ^ 2 ≤ (max T 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    exact inv_anti₀ (by positivity [hzpos n]) h2
  obtain ⟨S, hS⟩ : ∃ S : ℝ → Finset ι, ∀ T n, n ∈ S T ↔ ‖z n‖ ≤ T :=
    ⟨fun T => (hfinite T).toFinset, fun T n => by simp⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℂ → ℂ, ∀ s, P s = ∏' n, (1 - s / z n) * Complex.exp (s / z n) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ → ℂ → ℂ, ∀ R s,
      L R s = ∑' n : ((S (2 * R) : Set ι)ᶜ : Set ι), (Complex.log (1 - s / z n) + s / z n) :=
    ⟨_, fun _ _ => rfl⟩
  -- the tail factors are small
  have hbd : ∀ R : ℝ, 0 < R → ∀ s : ℂ, ‖s‖ ≤ R → ∀ n, n ∉ S (2 * R) →
      ‖s / z n‖ ≤ 1 / 2 ∧
        ‖Complex.log (1 - s / z n) + s / z n‖ ≤ ‖s‖ ^ 2 * (‖z n‖ ^ 2)⁻¹ := by
    intro R hR s hs n hn
    rw [hS] at hn
    push Not at hn
    have h1 : ‖s / z n‖ ≤ 1 / 2 := by
      rw [norm_div, div_le_iff₀ (hzpos n)]; linarith
    refine ⟨h1, (hℓ _ h1).trans (le_of_eq ?_)⟩
    rw [norm_div, div_pow, div_eq_mul_inv]
  have hsummL : ∀ R : ℝ, 0 < R → ∀ s : ℂ, ‖s‖ ≤ R →
      Summable fun n : ((S (2 * R) : Set ι)ᶜ : Set ι) =>
        Complex.log (1 - s / z n) + s / z n := fun R hR s hs =>
    Summable.of_norm_bounded ((hsum2.subtype _).mul_left (‖s‖ ^ 2))
      fun n => (hbd R hR s hs n n.2).2
  have hrep : ∀ R : ℝ, 0 < R → ∀ s : ℂ, ‖s‖ ≤ R →
      P s = (∏ n ∈ S (2 * R), (1 - s / z n) * Complex.exp (s / z n)) *
        Complex.exp (L R s) := by
    intro R hR s hs
    rw [hPdef, hL]
    refine HasProd.tprod_eq ?_
    refine HasProd.mul_compl (s := (S (2 * R) : Set ι)) (Finset.hasProd _ _) ?_
    have := (hsummL R hR s hs).hasSum.cexp
    convert this using 1
    funext n
    simp only [Function.comp]
    rw [hexpℓ _ (by linarith [(hbd R hR s hs n n.2).1])]
  have hLdiff : ∀ R : ℝ, 0 < R → DifferentiableOn ℂ (L R) (Metric.ball 0 R) := by
    intro R hR
    have e : L R = fun s => ∑' n : ((S (2 * R) : Set ι)ᶜ : Set ι),
        (Complex.log (1 - s / z n) + s / z n) := funext (hL R)
    rw [e]
    refine Complex.differentiableOn_tsum_of_summable_norm ((hsum2.subtype _).mul_left (R ^ 2))
      (fun n => ?_) Metric.isOpen_ball (fun n s hs => ?_)
    · intro s hs
      have hs' : ‖s‖ ≤ R := (mem_ball_zero_iff.mp hs).le
      have : ‖s / z n‖ < 1 := by linarith [(hbd R hR s hs' n n.2).1]
      have hd : DifferentiableAt ℂ (fun s : ℂ => 1 - s / z n) s := by fun_prop
      exact ((hd.clog (hslit _ this)).add
        (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s / z n) s)).differentiableWithinAt
    · have hs' : ‖s‖ ≤ R := (mem_ball_zero_iff.mp hs).le
      refine (hbd R hR s hs' n n.2).2.trans ?_
      simp only [Function.comp]
      gcongr
  -- `P` vanishes at `w` to the same order as `f`
  have hPfac : ∀ w : ℂ, ∃ k : ℕ, analyticOrderAt f w = k ∧ ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧
      g w ≠ 0 ∧ ∀ᶠ s in 𝓝 w, P s = (s - w) ^ k * g s := by
    intro w
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ‖w‖ + 1 := ⟨_, rfl⟩
    have hR0 : 0 < R := by rw [hRdef]; positivity
    have hwR : w ∈ Metric.ball (0 : ℂ) R := by rw [mem_ball_zero_iff, hRdef]; linarith
    obtain ⟨T, hT⟩ : ∃ T : Finset ι, T = (S (2 * R)).filter (fun n => z n = w) := ⟨_, rfl⟩
    refine ⟨T.card, ?_, ?_⟩
    · rw [← hz w]
      have : {n | z n = w} = (T : Set ι) := by
        ext n
        simp only [Set.mem_ofPred_eq, hT, Finset.coe_filter, hS]
        constructor
        · intro h
          refine ⟨?_, h⟩
          rw [h, hRdef]
          linarith [norm_nonneg w]
        · exact fun h => h.2
      rw [← Set.encard_coe_eq_coe_finsetCard, ← this]
      rfl
    · refine ⟨fun s => (∏ n ∈ T, (-(z n)⁻¹)) *
        (∏ n ∈ (S (2 * R)).filter (fun n => ¬ z n = w), (1 - s / z n)) *
        (∏ n ∈ S (2 * R), Complex.exp (s / z n)) * Complex.exp (L R s), ?_, ?_, ?_⟩
      · have hd : DifferentiableOn ℂ (fun s => (∏ n ∈ T, (-(z n)⁻¹)) *
            (∏ n ∈ (S (2 * R)).filter (fun n => ¬ z n = w), (1 - s / z n)) *
            (∏ n ∈ S (2 * R), Complex.exp (s / z n)) * Complex.exp (L R s))
            (Metric.ball 0 R) := by
          refine DifferentiableOn.mul ?_ (hLdiff R hR0).cexp
          fun_prop
        exact hd.analyticAt (Metric.isOpen_ball.mem_nhds hwR)
      · refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) (Complex.exp_ne_zero _)
        · exact Finset.prod_ne_zero_iff.mpr fun n _ => neg_ne_zero.mpr (inv_ne_zero (hz0 n))
        · refine Finset.prod_ne_zero_iff.mpr fun n hn => ?_
          have hne : z n ≠ w := (Finset.mem_filter.mp hn).2
          intro h
          apply hne
          have := hz0 n
          field_simp at h
          linear_combination h
        · exact Finset.prod_ne_zero_iff.mpr fun n _ => Complex.exp_ne_zero _
      · filter_upwards [Metric.isOpen_ball.mem_nhds hwR] with s hs
        rw [hrep R hR0 s (mem_ball_zero_iff.mp hs).le, Finset.prod_mul_distrib,
          ← Finset.prod_filter_mul_prod_filter_not (S (2 * R)) (fun n => z n = w), ← hT]
        have hTp : ∏ n ∈ T, (1 - s / z n) = (s - w) ^ T.card * ∏ n ∈ T, (-(z n)⁻¹) := by
          rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun n hn => ?_
          have hzw : z n = w := by rw [hT] at hn; exact (Finset.mem_filter.mp hn).2
          have := hz0 n
          rw [← hzw]
          field_simp
          ring
        rw [hTp]
        ring
  -- the quotient `F = f / P`, with its removable singularities filled in
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ,
      ∀ s, F s = (nhdsWithin s {s}ᶜ).limUnder (fun t => f t / P t) := ⟨_, fun _ => rfl⟩
  have hFloc : ∀ w, ∃ q : ℂ → ℂ, AnalyticAt ℂ q w ∧ q w ≠ 0 ∧
      ∀ᶠ s in 𝓝 w, F s = q s ∧ f s = q s * P s := by
    intro w
    obtain ⟨k, hk, gP, hgPa, hgPw, hPev⟩ := hPfac w
    obtain ⟨gf, hgfa, hgfw, hfev⟩ := (hf.analyticAt w).analyticOrderAt_eq_natCast.mp hk
    refine ⟨fun s => gf s / gP s, hgfa.div hgPa hgPw, div_ne_zero hgfw hgPw, ?_⟩
    have hev : ∀ᶠ s in 𝓝 w, (f s = (s - w) ^ k • gf s ∧ P s = (s - w) ^ k * gP s) ∧
        gP s ≠ 0 ∧ ContinuousAt (fun s => gf s / gP s) s := by
      filter_upwards [hfev, hPev, hgPa.continuousAt.eventually_ne hgPw,
        (hgfa.div hgPa hgPw).eventually_analyticAt] with s h1 h2 h3 h4
      exact ⟨⟨h1, h2⟩, h3, h4.continuousAt⟩
    obtain ⟨t, ht, hto, hwt⟩ := _root_.eventually_nhds_iff.mp hev
    filter_upwards [hto.mem_nhds hwt] with s hs
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := ht s hs
    refine ⟨?_, ?_⟩
    · rw [hFdef]
      apply Filter.Tendsto.limUnder_eq
      have hmem : t \ {w} ∈ nhdsWithin s {s}ᶜ := by
        by_cases hsw : s = w
        · rw [hsw]
          exact sdiff_mem_nhdsWithin_compl (hto.mem_nhds hwt) {w}
        · exact mem_nhdsWithin_of_mem_nhds
            ((hto.sdiff isClosed_singleton).mem_nhds ⟨hs, hsw⟩)
      refine (h4.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [hmem] with u hu
      obtain ⟨⟨h1', h2'⟩, h3', -⟩ := ht u hu.1
      have hne : (u - w) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hu.2)
      rw [h1', h2', smul_eq_mul]
      field_simp
    · rw [h1, h2, smul_eq_mul]
      field_simp
  have hFan : ∀ w, AnalyticAt ℂ F w := fun w => by
    obtain ⟨q, hq, -, hev⟩ := hFloc w
    exact hq.congr (hev.mono fun s hs => hs.1.symm)
  have hFne : ∀ w, F w ≠ 0 := fun w => by
    obtain ⟨q, -, hqw, hev⟩ := hFloc w
    rw [hev.self_of_nhds.1]
    exact hqw
  have hfFP : ∀ w, f w = F w * P w := fun w => by
    obtain ⟨q, -, -, hev⟩ := hFloc w
    rw [hev.self_of_nhds.1]
    exact hev.self_of_nhds.2
  have hFd : Differentiable ℂ F := fun w => (hFan w).differentiableAt
  -- an entire logarithm `H` of `F`
  obtain ⟨H, hdiff, hH0, hFexp⟩ := exists_differentiable_eq_cexp_of_ne_zero hFd hFne
  have hgrowth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
      ∀ᶠ s in cocompact ℂ, (H s - H 0).re ≤ C * ‖s‖ ^ (1 + ε) := by
    intro ε hε
    clear hPfac hFloc hFan hH0 hLdiff hexpℓ hslit h00 hfinite hFdef hℓ hsum2 hPdef hdiff
    obtain ⟨e, he⟩ : ∃ e : ℝ, e = min ε 1 := ⟨_, rfl⟩
    have he0 : 0 < e := by rw [he]; exact lt_min hε one_pos
    have he1 : e ≤ 1 := by rw [he]; exact min_le_right _ _
    have heε : e ≤ ε := by rw [he]; exact min_le_left _ _
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 + e / 3 := ⟨_, rfl⟩
    have ha1 : 1 ≤ a := by rw [ha]; linarith
    have ha2 : a ≤ 2 := by rw [ha]; linarith
    have hsuma : Summable fun n => ‖z n‖ ^ (-a) := by
      have := h1.summable_norm_rpow_neg hf zero_le_one hf0 hz (ε := e / 3) (by positivity)
      refine this.congr fun n => ?_
      rw [ha]; ring_nf
    obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∑' n, ‖z n‖ ^ (-a) := ⟨_, rfl⟩
    have hK0 : 0 ≤ K := by rw [hK]; exact tsum_nonneg fun n => by positivity
    have hSK : ∀ T : Finset ι, ∑ n ∈ T, ‖z n‖ ^ (-a) ≤ K := fun T => by
      rw [hK]; exact hsuma.sum_le_tsum _ (fun _ _ => by positivity)
    -- a lower bound for `P` on circles that keep away from the zeros
    have hPlow : ∀ R η : ℝ, 0 < R → 0 < η → (∀ n ∈ S (2 * R), η ≤ |‖z n‖ - R|) →
        ∀ ζ : ℂ, ‖ζ‖ = R →
        (η / (2 * R)) ^ (S (2 * R)).card * Real.exp (-(3 * K * R ^ a)) ≤ ‖P ζ‖ := by
      intro R η hR hη hgap ζ hζ
      rw [hrep R hR ζ hζ.le, norm_mul, Complex.norm_exp, norm_prod]
      have hfac : ∀ n ∈ S (2 * R), η / (2 * R) * Real.exp (-(2 * (R ^ a * ‖z n‖ ^ (-a)))) ≤
          ‖(1 - ζ / z n) * Complex.exp (ζ / z n)‖ := by
        intro n hn
        have hx := hzpos n
        have hxR : ‖z n‖ ≤ 2 * R := (hS _ n).mp hn
        rw [norm_mul, Complex.norm_exp]
        have h1 : η / (2 * R) ≤ ‖1 - ζ / z n‖ := by
          rw [show (1 : ℂ) - ζ / z n = (z n - ζ) / z n by field_simp [hz0 n], norm_div]
          have : η ≤ ‖z n - ζ‖ :=
            (hgap n hn).trans (by rw [← hζ]; exact abs_norm_sub_norm_le _ _)
          calc η / (2 * R) ≤ η / ‖z n‖ := div_le_div_of_nonneg_left hη.le hx hxR
            _ ≤ ‖z n - ζ‖ / ‖z n‖ := div_le_div_of_nonneg_right this hx.le
        have h2 : -(2 * (R ^ a * ‖z n‖ ^ (-a))) ≤ (ζ / z n).re := by
          have h3 := hrp2 (e / 3) R ‖z n‖ (by positivity) (by linarith) hR hx hxR
          rw [← ha] at h3
          have h4 : -‖ζ / z n‖ ≤ (ζ / z n).re := by
            have := Complex.abs_re_le_norm (ζ / z n)
            linarith [neg_abs_le (ζ / z n).re]
          rw [norm_div, hζ] at h4
          linarith
        exact mul_le_mul h1 (Real.exp_le_exp.mpr h2) (by positivity) (norm_nonneg _)
      have hprod := Finset.prod_le_prod₀ (fun n _ => by positivity) hfac
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum] at hprod
      have hsumS : -(2 * K * R ^ a) ≤ ∑ n ∈ S (2 * R), -(2 * (R ^ a * ‖z n‖ ^ (-a))) := by
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have := mul_le_mul_of_nonneg_left (hSK (S (2 * R)))
          (by positivity : (0 : ℝ) ≤ 2 * R ^ a)
        linarith only [this]
      have hLre : -(K * R ^ a) ≤ (L R ζ).re := by
        have hb : ‖L R ζ‖ ≤ K * R ^ a := by
          rw [hL]
          refine (norm_tsum_le_tsum_norm (hsummL R hR ζ hζ.le).norm).trans ?_
          have hg : Summable fun n : ((S (2 * R) : Set ι)ᶜ : Set ι) =>
              R ^ a * ‖z n‖ ^ (-a) := (hsuma.subtype _).mul_left _
          refine (Summable.tsum_le_tsum (fun n => ?_) (hsummL R hR ζ hζ.le).norm hg).trans ?_
          · have hn' : ¬ ‖z n‖ ≤ 2 * R := fun h => n.2 ((hS _ _).mpr h)
            refine (hbd R hR ζ hζ.le n n.2).2.trans ?_
            rw [hζ]
            have := hrp3 (e / 3) R ‖z n‖ (by positivity) (by linarith) hR
              (by push Not at hn'; linarith)
            rwa [← ha] at this
          · rw [tsum_mul_left, mul_comm K]
            have : ∑' n : ((S (2 * R) : Set ι)ᶜ : Set ι), ‖z n‖ ^ (-a) ≤ K := by
              rw [hK]; exact Summable.tsum_subtype_le _ _ (fun n => by positivity) hsuma
            exact mul_le_mul_of_nonneg_left this (by positivity)
        have := Complex.abs_re_le_norm (L R ζ)
        linarith [neg_abs_le (L R ζ).re]
      calc (η / (2 * R)) ^ (S (2 * R)).card * Real.exp (-(3 * K * R ^ a))
          ≤ ((η / (2 * R)) ^ (S (2 * R)).card *
              Real.exp (∑ n ∈ S (2 * R), -(2 * (R ^ a * ‖z n‖ ^ (-a))))) *
              Real.exp (L R ζ).re := by
            have hexp : Real.exp (-(3 * K * R ^ a)) ≤
                Real.exp (∑ n ∈ S (2 * R), -(2 * (R ^ a * ‖z n‖ ^ (-a)))) *
                  Real.exp (L R ζ).re := by
              rw [← Real.exp_add]
              exact Real.exp_le_exp.mpr (by linarith)
            rw [mul_assoc ((η / (2 * R)) ^ (S (2 * R)).card)]
            exact mul_le_mul_of_nonneg_left hexp (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
    -- choosing a radius in `[r, 2r]` away from the zeros (pigeonhole)
    have hgood : ∀ r : ℝ, 0 < r → ∃ R : ℝ, r ≤ R ∧ R ≤ 2 * r ∧
        ∀ n ∈ S (4 * r), r / (2 * (((S (4 * r)).card : ℝ) + 1)) ≤ |‖z n‖ - R| := by
      intro r hr
      obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (S (4 * r)).card := ⟨_, rfl⟩
      rw [← hN]
      obtain ⟨η, hη⟩ : ∃ η : ℝ, η = r / (2 * ((N : ℝ) + 1)) := ⟨_, rfl⟩
      rw [← hη]
      have hη0 : 0 < η := by rw [hη]; positivity
      have hNη : ((N : ℝ) + 1) * (2 * η) = r := by rw [hη]; field_simp
      by_contra hcon
      push Not at hcon
      have hbad : ∀ j ∈ Finset.range (N + 1),
          ∃ n ∈ S (4 * r), |‖z n‖ - (r + j * (2 * η))| < η := by
        intro j hj
        have hj' : (j : ℝ) ≤ N := by
          exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hjj : (j : ℝ) * (2 * η) ≤ N * (2 * η) := by gcongr
        apply hcon
        · have : 0 ≤ (j : ℝ) * (2 * η) := by positivity
          linarith
        · linarith
      have : Nonempty ι := ⟨(hbad 0 (by simp)).choose⟩
      choose! g hg1 hg2 using hbad
      have hinj : Set.InjOn g (Finset.range (N + 1) : Set ℕ) := by
        intro j hj j' hj' hjj
        have a1 := hg2 j hj
        have a2 := hg2 j' hj'
        rw [hjj] at a1
        rw [abs_lt] at a1 a2
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have : (j : ℝ) + 1 ≤ j' := by exact_mod_cast h
          have : ((j : ℝ) + 1) * (2 * η) ≤ j' * (2 * η) := by gcongr
          linarith
        · have : (j' : ℝ) + 1 ≤ j := by exact_mod_cast h
          have : ((j' : ℝ) + 1) * (2 * η) ≤ j * (2 * η) := by gcongr
          linarith
      have := Finset.card_le_card_of_injOn g (fun j hj => hg1 j hj) hinj
      rw [Finset.card_range, ← hN] at this
      omega
    obtain ⟨c, hc⟩ := (h1 (e / 3) (by positivity)).bound
    obtain ⟨R0, -, hR0⟩ :=
      (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.mp hc
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = e / 3 := ⟨_, rfl⟩
    have hθ0 : 0 < θ := by rw [hθ]; positivity
    obtain ⟨G, hG⟩ : ∃ G : ℝ, G = K * 4 ^ a * ((8 * (K * 4 ^ a + 1)) ^ θ / θ) := ⟨_, rfl⟩
    have hG0 : 0 ≤ G := by rw [hG]; positivity
    refine ⟨(|Real.log (2 * max c 1)| + |(H 0).re| + 4 + 12 * K + G) * 2 ^ (1 + ε), ?_⟩
    rw [← Metric.cobounded_eq_cocompact]
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop (max 1 (R0 + 1))] with s hs
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ‖s‖ := ⟨_, rfl⟩
    rw [← hρ] at hs ⊢
    have hρ1 : 1 ≤ ρ := le_trans (le_max_left _ _) hs
    have hρR0 : R0 + 1 ≤ ρ := le_trans (le_max_right _ _) hs
    have hρ0 : 0 < ρ := by linarith
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 2 * ρ := ⟨_, rfl⟩
    have hr1 : 1 ≤ r := by linarith
    obtain ⟨R, hrR, hR2, hgap⟩ := hgood r (by linarith)
    have hR0' : 0 < R := by linarith
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (S (4 * r)).card := ⟨_, rfl⟩
    rw [← hN] at hgap
    obtain ⟨η, hη⟩ : ∃ η : ℝ, η = r / (2 * ((N : ℝ) + 1)) := ⟨_, rfl⟩
    rw [← hη] at hgap
    have hη0 : 0 < η := by rw [hη]; positivity
    have hNη : 8 * ((N : ℝ) + 1) * η = 4 * r := by rw [hη]; field_simp; ring
    have hsub : S (2 * R) ⊆ S (4 * r) := fun n hn =>
      (hS _ n).mpr (le_trans ((hS _ n).mp hn) (by linarith))
    have hN'N : (S (2 * R)).card ≤ N := hN ▸ Finset.card_le_card hsub
    have hgap' : ∀ n ∈ S (2 * R), η ≤ |‖z n‖ - R| := fun n hn => hgap n (hsub hn)
    have hNK : (N : ℝ) ≤ K * (4 * r) ^ a := by
      have h4 : 0 < (4 * r) ^ a := by positivity
      have hterm : ∀ n ∈ S (4 * r), ((4 * r) ^ a)⁻¹ ≤ ‖z n‖ ^ (-a) := by
        intro n hn
        rw [← Real.rpow_neg (by positivity)]
        exact Real.rpow_le_rpow_of_nonpos (hzpos n) ((hS _ n).mp hn) (by linarith)
      have := (Finset.card_nsmul_le_sum _ _ _ hterm).trans (hSK _)
      rw [nsmul_eq_mul, ← hN, mul_inv_le_iff₀ h4] at this
      exact this
    obtain ⟨Lb, hLb⟩ : ∃ Lb : ℝ,
        Lb = (η / (2 * R)) ^ (S (2 * R)).card * Real.exp (-(3 * K * R ^ a)) := ⟨_, rfl⟩
    have hLb0 : 0 < Lb := by rw [hLb]; positivity
    have hc1 : 0 < max c 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max c 1 * Real.exp (R ^ a) / Lb := ⟨_, rfl⟩
    have hM0 : 0 ≤ M := by rw [hM]; positivity
    have hcirc : ∀ ζ ∈ Metric.sphere (0 : ℂ) R, ‖F ζ‖ ≤ M := by
      intro ζ hζ
      rw [mem_sphere_zero_iff_norm] at hζ
      have hPζ : Lb ≤ ‖P ζ‖ := hLb ▸ hPlow R η hR0' hη0 hgap' ζ hζ
      have hfζ : ‖f ζ‖ ≤ max c 1 * Real.exp (R ^ a) := by
        have := hR0 (show ζ ∈ (Metric.closedBall (0 : ℂ) R0)ᶜ by
          rw [Set.mem_compl_iff, mem_closedBall_zero_iff]; linarith)
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, hζ] at this
        rw [ha]
        refine this.trans ?_
        gcongr
        exact le_max_left _ _
      rw [hM, le_div_iff₀ hLb0]
      calc ‖F ζ‖ * Lb ≤ ‖F ζ‖ * ‖P ζ‖ := by gcongr
        _ = ‖f ζ‖ := by rw [hfFP, norm_mul]
        _ ≤ _ := hfζ
    -- the Cauchy estimates turn the circle bound into a bound at `s`
    have hFs : ‖F s‖ ≤ 2 * max c 1 * Real.exp (R ^ a) / Lb := by
      have hts := Complex.hasSum_taylorSeries_of_entire hFd 0 s
      have hgeom : HasSum (fun n : ℕ => M * (1 / 2 : ℝ) ^ n) (M * (1 - 1 / 2)⁻¹) :=
        (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left M
      have hρR : ρ / R ≤ 1 / 2 := by rw [div_le_iff₀ hR0']; linarith
      have := hts.norm_le_of_bounded hgeom (fun n => ?_)
      · have e : M * (1 - 1 / 2 : ℝ)⁻¹ = 2 * max c 1 * Real.exp (R ^ a) / Lb := by
          rw [hM]; ring
        linarith
      · have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) n hR0'
          hFd.diffContOnCl hcirc
        rw [norm_smul, norm_smul, norm_inv, sub_zero, norm_pow, ← hρ, Complex.norm_natCast]
        have hf' : (0 : ℝ) < n.factorial := by positivity
        calc (n.factorial : ℝ)⁻¹ * (ρ ^ n * ‖iteratedDeriv n F 0‖)
            ≤ (n.factorial : ℝ)⁻¹ * (ρ ^ n * (n.factorial * M / R ^ n)) := by gcongr
          _ = M * (ρ / R) ^ n := by rw [div_pow]; field_simp
          _ ≤ M * (1 / 2) ^ n := by gcongr
    have hReH : (H s).re = Real.log ‖F s‖ := by rw [hFexp, Complex.norm_exp, Real.log_exp]
    have hlogF : Real.log ‖F s‖ ≤ Real.log (2 * max c 1) + R ^ a -
        (S (2 * R)).card * Real.log (η / (2 * R)) + 3 * K * R ^ a := by
      have hF0 : 0 < ‖F s‖ := norm_pos_iff.mpr (hFne s)
      refine (Real.log_le_log hF0 hFs).trans (le_of_eq ?_)
      have hη2 : 0 < η / (2 * R) := by positivity
      rw [hLb, Real.log_div (by positivity) (by positivity),
        Real.log_mul (x := 2 * max c 1) (by positivity) (by positivity),
        Real.log_mul (x := (η / (2 * R)) ^ (S (2 * R)).card) (by positivity) (by positivity),
        Real.log_exp, Real.log_pow, Real.log_exp]
      ring
    have hlogη : -Real.log (8 * ((N : ℝ) + 1)) ≤ Real.log (η / (2 * R)) := by
      rw [← Real.log_inv]
      apply Real.log_le_log (by positivity)
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hlog8 : 0 ≤ Real.log (8 * ((N : ℝ) + 1)) :=
      Real.log_nonneg (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
    have hNlog : -((S (2 * R)).card * Real.log (η / (2 * R))) ≤
        N * Real.log (8 * ((N : ℝ) + 1)) := by
      have hcN : ((S (2 * R)).card : ℝ) ≤ N := by exact_mod_cast hN'N
      calc -((S (2 * R)).card * Real.log (η / (2 * R)))
          = ((S (2 * R)).card : ℝ) * (-Real.log (η / (2 * R))) := by ring
        _ ≤ ((S (2 * R)).card : ℝ) * Real.log (8 * ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
        _ ≤ N * Real.log (8 * ((N : ℝ) + 1)) := mul_le_mul_of_nonneg_right hcN hlog8
    have hX1 : 1 ≤ r ^ (1 + ε) := Real.one_le_rpow hr1 (by linarith)
    have hra : r ^ a ≤ r ^ (1 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (by rw [ha]; linarith)
    have hrθ : r ^ (a * (1 + θ)) ≤ r ^ (1 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (by
        have hee : e * e ≤ e := mul_le_of_le_one_left he0.le he1
        rw [ha, hθ]; nlinarith only [hee, heε])
    have hRa : R ^ a ≤ 4 * r ^ (1 + ε) := by
      have h2a : (2 : ℝ) ^ a ≤ 4 := by
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha2
        norm_num at this
        exact this
      calc R ^ a ≤ (2 * r) ^ a := Real.rpow_le_rpow hR0'.le hR2 (by linarith)
        _ = 2 ^ a * r ^ a := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ 4 * r ^ (1 + ε) := mul_le_mul h2a hra (by positivity) (by norm_num)
    have hGb : (N : ℝ) * Real.log (8 * ((N : ℝ) + 1)) ≤ G * r ^ (1 + ε) :=
      (hG ▸ hgen K a θ r N hK0 (by linarith) hθ0 hr1 (Nat.cast_nonneg _) hNK).trans
        (mul_le_mul_of_nonneg_left hrθ hG0)
    have hKR : 3 * K * R ^ a ≤ 3 * K * (4 * r ^ (1 + ε)) :=
      mul_le_mul_of_nonneg_left hRa (by positivity)
    have e1 : |Real.log (2 * max c 1)| ≤ |Real.log (2 * max c 1)| * r ^ (1 + ε) :=
      le_mul_of_one_le_right (abs_nonneg _) hX1
    have e2 : |(H 0).re| ≤ |(H 0).re| * r ^ (1 + ε) :=
      le_mul_of_one_le_right (abs_nonneg _) hX1
    have hrε : r ^ (1 + ε) = 2 ^ (1 + ε) * ρ ^ (1 + ε) := by
      rw [hr, Real.mul_rpow (by norm_num) hρ0.le]
    have hmain : Real.log ‖F s‖ - (H 0).re ≤
        |Real.log (2 * max c 1)| * r ^ (1 + ε) + |(H 0).re| * r ^ (1 + ε) +
          4 * r ^ (1 + ε) + 3 * K * (4 * r ^ (1 + ε)) + G * r ^ (1 + ε) := by
      linarith [le_abs_self (Real.log (2 * max c 1)), neg_abs_le (H 0).re]
    rw [Complex.sub_re, hReH]
    refine hmain.trans (le_of_eq ?_)
    rw [hrε]
    ring
  obtain ⟨B, hB⟩ := exists_eq_mul_of_re_le_rpow_one_add (h := fun s => H s - H 0)
    (hdiff.sub_const _) (by simp) hgrowth
  refine ⟨H 0, B, fun s => ?_⟩
  have hBs : H s - H 0 = B * s := hB s
  rw [hfFP s, hFexp s, hPdef s, show H s = H 0 + B * s by linear_combination hBs]

/-- **Hadamard's factorization theorem for entire functions of order at most `1`**, with the
zeros indexed canonically: each zero `w` of `f` appears `analyticOrderAt f w` times, as the points
of `Σ w, Fin (analyticOrderAt f w).toNat`. -/
theorem exists_eq_exp_mul_tprod_sigma_of_hasGrowthOrderLE_one {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h1 : HasGrowthOrderLE f 1) (hf0 : f 0 ≠ 0) :
    ∃ A B : ℂ, ∀ s, f s = Complex.exp (A + B * s) *
      ∏' n : (Σ w : ℂ, Fin (analyticOrderAt f w).toNat),
        (1 - s / n.1) * Complex.exp (s / n.1) :=
  exists_eq_exp_mul_tprod_of_hasGrowthOrderLE_one hf h1 hf0
    (card_sigma_fin_analyticOrderAt hf hf0)

end Complex
