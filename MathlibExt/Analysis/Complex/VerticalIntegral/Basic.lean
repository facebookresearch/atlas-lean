/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Principal-value integrals along a vertical line

For `c : ℝ` and `f : ℂ → E`, the line integral `(1 / (2πi)) ∫_{c - i∞}^{c + i∞} f(s) ds`
is, after the substitution `s = c + it`, the real integral `(1 / (2π)) ∫ f(c + it) dt`.
In analytic number theory (Perron's formula, Riesz means, explicit formulas) such integrals
often converge only as **Cauchy principal values**: as limits of the symmetric truncations
`(1 / (2π)) ∫_{-R}^{R} f(c + it) dt` as `R → ∞`. Mathlib's `Complex.VerticalIntegrable` and
`mellinInv` only cover the absolutely convergent case.

This file defines the principal value and its convergence predicate, in the relation that
`tsum` and `HasSum` have, and develops the basic API.

## Main definitions

* `Complex.HasVerticalIntegral c f v`: `t ↦ f (c + t * I)` is integrable on every bounded
  interval, and the symmetric truncations `(1 / (2π)) • ∫ t in -R..R, f (c + t * I)` tend to `v`
  as `R → ∞`.
* `Complex.verticalIntegral c f`: the limit of the symmetric truncations (junk if it does not
  exist).

## Main statements

* `Complex.HasVerticalIntegral.verticalIntegral_eq`, `Complex.HasVerticalIntegral.unique`.
* `Complex.VerticalIntegrable.hasVerticalIntegral`: an absolutely convergent line integral is
  its own principal value; `Complex.hasVerticalIntegral_mellinInv` is the case of `mellinInv`.
* `Complex.HasVerticalIntegral.intervalIntegrable`: the integrand is integrable on every
  bounded segment of the line.
* Linearity (`add`, `sub`, `neg`, `const_smul`, `const_mul`, `finset_sum`), congruence on the
  line (`congr_line`) and translation of the abscissa (`comp_sub_ofReal`).
* `Complex.HasVerticalIntegral.norm_sub_le_of_norm_le_div_sq`: if `‖f(c + it)‖ ≤ A / t²` for
  `|t| ≥ 1`, truncating at height `T ≥ 1` costs at most `A / (π T)`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Real Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Symmetric truncations of an integrable function converge to its integral. -/
theorem MeasureTheory.Integrable.tendsto_intervalIntegral_neg_self {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F} (hf : Integrable f) :
    Tendsto (fun R : ℝ => ∫ t in (-R)..R, f t) atTop (𝓝 (∫ t, f t)) :=
  intervalIntegral_tendsto_integral hf tendsto_neg_atTop_atBot tendsto_id

namespace Complex

/-- `HasVerticalIntegral c f v` says that the principal-value line integral
`(1 / (2πi)) ∫_{c - i∞}^{c + i∞} f(s) ds` converges to `v`: `t ↦ f (c + t * I)` is integrable on
every segment `[-R, R]`, and the symmetric truncations `(1 / (2π)) • ∫ t in -R..R, f (c + t * I)`
tend to `v` as `R → ∞`.

The local integrability rules out junk values: without it, an integrand that is integrable on no
segment (such as `|im s|⁻¹`) would have every truncation equal to `0`.

This is weaker than absolute convergence (`Complex.VerticalIntegrable`), and is the natural
notion for Perron-type integrals such as `∫_(c) x ^ s / s ds`. -/
def HasVerticalIntegral (c : ℝ) (f : ℂ → E) (v : E) : Prop :=
  (∀ R : ℝ, IntervalIntegrable (fun t : ℝ => f (c + t * I)) volume (-R) R) ∧
    Tendsto (fun R : ℝ => (1 / (2 * π)) • ∫ t in (-R)..R, f (c + t * I)) atTop (𝓝 v)

/-- The principal-value line integral `(1 / (2πi)) ∫_{c - i∞}^{c + i∞} f(s) ds`, i.e. the limit
of `(1 / (2π)) • ∫ t in -R..R, f (c + t * I)` as `R → ∞`. If the limit does not exist, the value
is junk; use `Complex.HasVerticalIntegral` to assert convergence. -/
noncomputable def verticalIntegral (c : ℝ) (f : ℂ → E) : E :=
  limUnder atTop fun R : ℝ => (1 / (2 * π)) • ∫ t in (-R)..R, f (c + t * I)

variable {c : ℝ} {f g : ℂ → E} {v w : E}

/-- The zero function has principal value zero. -/
theorem hasVerticalIntegral_zero : HasVerticalIntegral c (fun _ => (0 : E)) 0 :=
  ⟨fun _ => intervalIntegrable_const, by simp⟩

/-- A principal value from a continuous integrand on the line: only the convergence of the
symmetric truncations needs checking. -/
theorem hasVerticalIntegral_of_continuous (hf : Continuous fun t : ℝ => f (c + t * I))
    (h : Tendsto (fun R : ℝ => (1 / (2 * π)) • ∫ t in (-R)..R, f (c + t * I)) atTop (𝓝 v)) :
    HasVerticalIntegral c f v :=
  ⟨fun _ => hf.intervalIntegrable _ _, h⟩

namespace HasVerticalIntegral

/-- The symmetric truncations converge to the principal value. -/
theorem tendsto (h : HasVerticalIntegral c f v) :
    Tendsto (fun R : ℝ => (1 / (2 * π)) • ∫ t in (-R)..R, f (c + t * I)) atTop (𝓝 v) :=
  h.2

/-- The integrand of a principal value is integrable on every bounded segment of the line. -/
theorem intervalIntegrable (h : HasVerticalIntegral c f v) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => f (c + t * I)) volume a b := by
  refine (h.1 (max |a| |b|)).mono_set (uIcc_subset_uIcc ?_ ?_) <;>
    rw [mem_uIcc] <;> left <;> constructor <;>
    linarith [neg_abs_le a, le_abs_self a, neg_abs_le b, le_abs_self b,
      le_max_left |a| |b|, le_max_right |a| |b|]

/-- A convergent principal value is the value of `Complex.verticalIntegral`. -/
theorem verticalIntegral_eq (h : HasVerticalIntegral c f v) : verticalIntegral c f = v :=
  h.2.limUnder_eq

/-- The principal value is unique. -/
theorem unique (hv : HasVerticalIntegral c f v) (hw : HasVerticalIntegral c f w) : v = w :=
  tendsto_nhds_unique hv.2 hw.2

/-- Only the values on the line `re s = c` matter. -/
theorem congr_line (hf : HasVerticalIntegral c f v)
    (hfg : ∀ t : ℝ, f (c + t * I) = g (c + t * I)) : HasVerticalIntegral c g v := by
  have e : (fun t : ℝ => g (c + t * I)) = fun t : ℝ => f (c + t * I) :=
    funext fun t => (hfg t).symm
  exact ⟨fun R => e ▸ hf.1 R, by simpa only [e] using hf.2⟩

/-- Scalar multiples of a principal value. -/
theorem const_smul (h : HasVerticalIntegral c f v) (a : ℂ) :
    HasVerticalIntegral c (fun s => a • f s) (a • v) := by
  refine ⟨fun R => (h.1 R).smul a, (h.2.const_smul a).congr fun R => ?_⟩
  rw [intervalIntegral.integral_smul, smul_comm]

/-- Scalar multiples of a scalar principal value. -/
theorem const_mul {f : ℂ → ℂ} {v : ℂ} (h : HasVerticalIntegral c f v) (a : ℂ) :
    HasVerticalIntegral c (fun s => a * f s) (a * v) :=
  h.const_smul a

theorem neg (h : HasVerticalIntegral c f v) : HasVerticalIntegral c (fun s => -f s) (-v) := by
  simpa using h.const_smul (-1)

/-- Principal values add. -/
theorem add (hf : HasVerticalIntegral c f v) (hg : HasVerticalIntegral c g w) :
    HasVerticalIntegral c (fun s => f s + g s) (v + w) := by
  refine ⟨fun R => (hf.1 R).add (hg.1 R), (hf.2.add hg.2).congr fun R => ?_⟩
  rw [intervalIntegral.integral_add (hf.1 R) (hg.1 R), smul_add]

/-- Principal values subtract. -/
theorem sub (hf : HasVerticalIntegral c f v) (hg : HasVerticalIntegral c g w) :
    HasVerticalIntegral c (fun s => f s - g s) (v - w) := by
  refine ⟨fun R => (hf.1 R).sub (hg.1 R), (hf.2.sub hg.2).congr fun R => ?_⟩
  rw [intervalIntegral.integral_sub (hf.1 R) (hg.1 R), smul_sub]

/-- Finite sums of principal values. -/
theorem finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → E} {v : ι → E}
    (hf : ∀ i ∈ s, HasVerticalIntegral c (f i) (v i)) :
    HasVerticalIntegral c (fun z => ∑ i ∈ s, f i z) (∑ i ∈ s, v i) := by
  refine ⟨fun R => by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum s fun i hi => (hf i hi).1 R,
    (tendsto_finsetSum s fun i hi => (hf i hi).2).congr fun R => ?_⟩
  rw [intervalIntegral.integral_finsetSum fun i hi => (hf i hi).1 R, Finset.smul_sum]

/-- Translating the abscissa: a principal value on `re s = c - a` is one on `re s = c` for the
translated integrand. -/
theorem comp_sub_ofReal {a : ℝ} (h : HasVerticalIntegral (c - a) f v) :
    HasVerticalIntegral c (fun s => f (s - a)) v := by
  have e : (fun t : ℝ => f (c + t * I - a)) = fun t : ℝ => f ((c - a : ℝ) + t * I) := by
    funext t
    congr 1
    push_cast
    ring
  exact ⟨fun R => e ▸ h.1 R, by simpa only [e] using h.2⟩

end HasVerticalIntegral

/-- If the principal value exists, it is `Complex.verticalIntegral c f`. -/
theorem hasVerticalIntegral_verticalIntegral (h : ∃ v, HasVerticalIntegral c f v) :
    HasVerticalIntegral c f (verticalIntegral c f) := by
  obtain ⟨v, hv⟩ := h
  rwa [hv.verticalIntegral_eq]

/-- **An absolutely convergent line integral is its own principal value.** If `t ↦ f (c + t * I)`
agrees with an integrable `F`, the principal value is `(1 / (2π)) • ∫ F`. -/
theorem hasVerticalIntegral_of_integrable {F : ℝ → E} (hF : Integrable F)
    (hfF : ∀ t : ℝ, f (c + t * I) = F t) :
    HasVerticalIntegral c f ((1 / (2 * π)) • ∫ t, F t) := by
  have e : (fun t : ℝ => f (c + t * I)) = F := funext hfF
  refine ⟨fun R => e ▸ hF.intervalIntegrable, ?_⟩
  simpa only [e] using hF.tendsto_intervalIntegral_neg_self.const_smul (1 / (2 * π))

/-- **An absolutely convergent line integral is its own principal value.** -/
theorem VerticalIntegrable.hasVerticalIntegral (hf : VerticalIntegrable f c) :
    HasVerticalIntegral c f ((1 / (2 * π)) • ∫ t : ℝ, f (c + t * I)) :=
  hasVerticalIntegral_of_integrable hf fun _ => rfl

/-- The inverse Mellin transform is a principal-value line integral. -/
theorem hasVerticalIntegral_mellinInv {f : ℂ → E} {x : ℝ}
    (hf : VerticalIntegrable (fun s => (x : ℂ) ^ (-s) • f s) c) :
    HasVerticalIntegral c (fun s => (x : ℂ) ^ (-s) • f s) (mellinInv c f x) :=
  hf.hasVerticalIntegral

/-- `∫_a^b t⁻² dt = a⁻¹ - b⁻¹` on an interval avoiding the origin. -/
private theorem integral_inv_sq_of_one_le_abs {a b : ℝ} (h : ∀ t ∈ uIcc a b, 1 ≤ |t|) :
    ∫ t in a..b, (t ^ 2)⁻¹ = a⁻¹ - b⁻¹ := by
  have hne : ∀ t ∈ uIcc a b, t ≠ 0 := fun t ht h0 => by
    have := h t ht
    rw [h0, abs_zero] at this
    linarith
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun u : ℝ => -u⁻¹) (t ^ 2)⁻¹ t := fun t ht => by
    have h := (hasDerivAt_inv (hne t ht)).neg
    rw [neg_neg] at h
    exact h
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (uIcc a b) :=
    (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (hne t ht)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  ring

/-- **Truncating a principal value.** If `HasVerticalIntegral c f v` and
`‖f (c + t * I)‖ ≤ A / t ^ 2` for `|t| ≥ 1`, then for `T ≥ 1` the truncation at height `T` is
within `A / (π T)` of `v`. -/
theorem HasVerticalIntegral.norm_sub_le_of_norm_le_div_sq {A T : ℝ}
    (hf : HasVerticalIntegral c f v)
    (hA : ∀ t : ℝ, 1 ≤ |t| → ‖f (c + t * I)‖ ≤ A / t ^ 2) (hT : 1 ≤ T) :
    ‖v - (1 / (2 * π)) • ∫ t in (-T)..T, f (c + t * I)‖ ≤ A / (π * T) := by
  set F : ℝ → E := fun t : ℝ => f (c + t * I) with hFdef
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hA0 : 0 ≤ A := by
    have h1 := hA 1 (by norm_num)
    exact le_trans (norm_nonneg _) (by simpa using h1)
  -- the closed form of `∫ A / t ^ 2` on an interval missing `(-1, 1)`
  have tail : ∀ a b : ℝ, (∀ t ∈ uIcc a b, 1 ≤ |t|) →
      (∫ t in a..b, A / t ^ 2) = A * (a⁻¹ - b⁻¹) := by
    intro a b h
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_sq_of_one_le_abs h]
  -- the truncations at heights `R ≥ T` and `T` differ by at most `A / (π T)`
  have key : ∀ R : ℝ, T ≤ R →
      ‖(1 / (2 * π)) • (∫ t in (-R)..R, F t) - (1 / (2 * π)) • ∫ t in (-T)..T, F t‖ ≤
        A / (π * T) := by
    intro R hR
    have hsub : ∀ a b : ℝ, -R ≤ a → a ≤ b → b ≤ R → IntervalIntegrable F volume a b := by
      intro a b h1 h2 h3
      exact (hf.1 R).mono_set (uIcc_subset_uIcc (mem_uIcc.2 (Or.inl ⟨h1, by linarith⟩))
        (mem_uIcc.2 (Or.inl ⟨by linarith, h3⟩)))
    have e1 := intervalIntegral.integral_add_adjacent_intervals
      (hsub (-R) (-T) le_rfl (by linarith) (by linarith))
      (hsub (-T) T (by linarith) (by linarith) hR)
    have e2 := intervalIntegral.integral_add_adjacent_intervals
      (hsub (-R) T le_rfl (by linarith) hR) (hsub T R (by linarith) hR le_rfl)
    have hsplit : (∫ t in (-R)..R, F t) - (∫ t in (-T)..T, F t) =
        (∫ t in (-R)..(-T), F t) + ∫ t in T..R, F t := by
      rw [← e2, ← e1]; abel
    -- the two tail pieces
    have hbound : ∀ a b : ℝ, a ≤ b → (∀ t ∈ uIcc a b, 1 ≤ |t|) → -R ≤ a → b ≤ R →
        ‖∫ t in a..b, F t‖ ≤ A * (a⁻¹ - b⁻¹) := by
      intro a b hab hge h1 h2
      have hne : ∀ t ∈ uIcc a b, t ≠ 0 := fun t ht h0 => by
        have := hge t ht
        rw [h0, abs_zero] at this
        linarith
      have hcont : ContinuousOn (fun t : ℝ => A / t ^ 2) (uIcc a b) :=
        continuousOn_const.div (continuousOn_pow 2) fun t ht => pow_ne_zero 2 (hne t ht)
      calc ‖∫ t in a..b, F t‖ ≤ ∫ t in a..b, ‖F t‖ :=
            intervalIntegral.norm_integral_le_integral_norm hab
        _ ≤ ∫ t in a..b, A / t ^ 2 := by
            refine intervalIntegral.integral_mono_on hab (hsub a b h1 hab h2).norm
              hcont.intervalIntegrable fun t ht => ?_
            exact hA t (hge t (uIcc_of_le hab ▸ ht))
        _ = A * (a⁻¹ - b⁻¹) := tail a b hge
    have hb1 : ‖∫ t in T..R, F t‖ ≤ A * (T⁻¹ - R⁻¹) := by
      refine hbound T R hR (fun t ht => ?_) (by linarith) le_rfl
      rw [uIcc_of_le hR] at ht
      exact le_abs.mpr (Or.inl (by linarith [ht.1]))
    have hb2 : ‖∫ t in (-R)..(-T), F t‖ ≤ A * (T⁻¹ - R⁻¹) := by
      have h := hbound (-R) (-T) (by linarith) (fun t ht => ?_) le_rfl (by linarith)
      · rwa [inv_neg, inv_neg, neg_sub_neg] at h
      · rw [uIcc_of_le (by linarith)] at ht
        exact le_abs.mpr (Or.inr (by linarith [ht.2]))
    rw [← smul_sub, hsplit, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
    have hnorm : ‖(∫ t in (-R)..(-T), F t) + ∫ t in T..R, F t‖ ≤ 2 * (A * (T⁻¹ - R⁻¹)) :=
      (norm_add_le _ _).trans (by linarith)
    have hRinv : 0 ≤ A * R⁻¹ := mul_nonneg hA0 (inv_nonneg.mpr (hT0.trans_le hR).le)
    calc 1 / (2 * π) * ‖(∫ t in (-R)..(-T), F t) + ∫ t in T..R, F t‖
        ≤ 1 / (2 * π) * (2 * (A * (T⁻¹ - R⁻¹))) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = A / (π * T) - π⁻¹ * (A * R⁻¹) := by field_simp
      _ ≤ A / (π * T) := sub_le_self _ (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) hRinv)
  -- pass to the limit `R → ∞`
  have hlim : Tendsto (fun R : ℝ => ‖(1 / (2 * π)) • (∫ t in (-R)..R, F t) -
      (1 / (2 * π)) • ∫ t in (-T)..T, F t‖) atTop
      (𝓝 ‖v - (1 / (2 * π)) • ∫ t in (-T)..T, F t‖) :=
    (hf.2.sub_const _).norm
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨T, key⟩)

end Complex
