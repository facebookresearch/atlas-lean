/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Chebyshev
public import MathlibExt.Analysis.SpecialFunctions.Log.IntegralDerivative
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.PrimeCounting.AxlerEffectivePrimeEstimates

/-!
# Axler's bound for the Mertens remainder

Expand the logarithm at each prime and interchange the resulting series using a
summable squared reciprocal of the prime and a geometric factor in the exponent. Axler's
bound for each prime-power tail then gives a strict bound for the full remainder.
-/

namespace MetaMathlibExt

private theorem hasSum_log_tail {r : ℝ} (hr : |r| < 1) :
    HasSum (fun m : ℕ ↦ r ^ (m + 2) / ((m : ℝ) + 2)) (-Real.log (1 - r) - r) := by
  have h := (hasSum_nat_add_iff' 1).2 (Real.hasSum_pow_div_log_of_abs_lt_one hr)
  simpa [Finset.sum_range_one, Nat.cast_add, add_assoc, one_add_one_eq_two] using h

private theorem hasSum_mertens_coefficients {x : ℝ} (hx : 1 < x) :
    HasSum (fun m : ℕ ↦ x⁻¹ ^ (m + 1) / ((m : ℝ) + 2) + x⁻¹ ^ (m + 1) / ((m : ℝ) + 1))
      ((x + 1) * Real.log (x / (x - 1)) - 1) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hr : |x⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr hxpos)]
    exact inv_lt_one_of_one_lt₀ hx
  have hfirst : HasSum (fun m : ℕ ↦ x⁻¹ ^ (m + 1) / ((m : ℝ) + 2))
      (x * (-Real.log (1 - x⁻¹) - x⁻¹)) := by
    have hterm (m : ℕ) : x * (x⁻¹ ^ (m + 2) / ((m : ℝ) + 2)) =
        x⁻¹ ^ (m + 1) / ((m : ℝ) + 2) := by
      rw [show m + 2 = (m + 1) + 1 by rfl, pow_succ', ← mul_div_assoc, ← mul_assoc,
        mul_inv_cancel₀ hxpos.ne', one_mul]
    simpa only [hterm] using (hasSum_log_tail hr).mul_left x
  have hlog : -Real.log (1 - x⁻¹) = Real.log (x / (x - 1)) := by
    rw [← Real.log_inv]
    congr 1
    have hden : x - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hx)
    have heq : 1 - x⁻¹ = (x - 1) / x := by field_simp
    rw [heq, inv_div]
  convert hfirst.add (Real.hasSum_pow_div_log_of_abs_lt_one hr) using 1
  rw [hlog, mul_sub, mul_inv_cancel₀ hxpos.ne']
  ring

private noncomputable def primePowerTerm (x : ℝ) (p m : ℕ) : ℝ :=
  (if p.Prime ∧ x < p then 1 / (p : ℝ) ^ (m + 2) else 0) / ((m : ℝ) + 2)

private theorem primePowerTerm_nonneg (x : ℝ) (p m : ℕ) : 0 ≤ primePowerTerm x p m := by
  unfold primePowerTerm
  split_ifs <;> positivity

-- A product majorant makes the change of order independent of the inner sums.
private theorem summable_primePowerTerm {x : ℝ} (hx : 1 < x) :
    Summable (Function.uncurry (primePowerTerm x)) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hgeo := summable_geometric_of_lt_one (inv_nonneg.mpr hxpos.le) (inv_lt_one_of_one_lt₀ hx)
  have hsq := Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ))
  refine (hsq.mul_of_nonneg hgeo (fun p ↦ by positivity) (fun m ↦ by positivity)).of_nonneg_of_le
    (fun z ↦ primePowerTerm_nonneg x z.1 z.2) ?_
  rintro ⟨p, m⟩
  change primePowerTerm x p m ≤ (1 / (p : ℝ) ^ 2) * x⁻¹ ^ m
  by_cases hp : p.Prime ∧ x < p
  · have hp0 := hxpos.trans hp.2
    have hinv : (p : ℝ)⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hp0 hxpos).2 hp.2.le
    rw [primePowerTerm, ite_eq_left hp]
    have hm : (1 : ℝ) ≤ (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    calc
      _ ≤ 1 / (p : ℝ) ^ (m + 2) := div_le_self (by positivity) hm
      _ = (1 / (p : ℝ) ^ 2) * (p : ℝ)⁻¹ ^ m := by
        simp [one_div, ← inv_pow, pow_add, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv m) (by positivity)
  · simp only [primePowerTerm, ite_eq_right hp, zero_div]
    positivity

private theorem tsum_primePowerTerm {x : ℝ} (hx : 1 < x) (p : ℕ) :
    (∑' m, primePowerTerm x p m) =
      -(if p.Prime ∧ x < p then Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) else 0) := by
  by_cases hp : p.Prime ∧ x < p
  · have hp₁ := hx.trans hp.2
    have hp₀ := zero_lt_one.trans hp₁
    have hr : |(p : ℝ)⁻¹| < 1 := by
      rw [abs_of_pos (inv_pos.mpr hp₀)]
      exact inv_lt_one_of_one_lt₀ hp₁
    have ht := (hasSum_log_tail hr).tsum_eq
    simpa [primePowerTerm, hp, one_div, inv_pow, neg_add_rev, sub_eq_add_neg, add_comm] using ht
  · simp [primePowerTerm, hp]

/-- **The Mertens remainder from a Chebyshev bound.** Let $k \ge 1$ be an integer and let
$\eta > 0$ and $x_0 > 1$ be reals such that $|\vartheta(y) - y| < \eta y / \log^k y$ for every
real $y \ge x_0$, where $\vartheta(y) = \sum_{p \le y} \log p$ is Chebyshev's function. For
real $x$ let $S(x) = \sum_{p > x} \big(\log(1 - 1/p) + 1/p\big)$, the sum over the primes
$p > x$. Then for every real $x \ge x_0$,
$$
\Big|S(x) - \sum_{m \ge 1} \frac{\operatorname{li}(x^{-m})}{m+1}\Big| <
\frac{\eta}{\log^{k+1} x} \Big((x+1) \log\frac{x}{x-1} - 1\Big),
$$
where $\operatorname{li}$ is the logarithmic integral.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 8 (`integers-2024-A34-prop-8`); `S(x)` as in
the paper's equation (56). -/
public theorem abs_mertensRemainder_sub_tsum_logarithmicIntegral_lt (k : ℕ) (hk : 0 < k)
    (η x₀ : ℝ) (hη : 0 < η) (hx₀ : 1 < x₀)
    (hθ : ∀ y : ℝ, x₀ ≤ y → |Chebyshev.theta y - y| < η * y / Real.log y ^ k)
    (x : ℝ) (hx : x₀ ≤ x) :
    |(∑' p : ℕ, if p.Prime ∧ x < p then Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) else 0) -
        ∑' m : ℕ, Real.logarithmicIntegralReal (x ^ (-((m : ℝ) + 1))) / ((m : ℝ) + 2)| <
      η / Real.log x ^ (k + 1) * ((x + 1) * Real.log (x / (x - 1)) - 1) := by
  have hx₁ := hx₀.trans_le hx
  have hxpos := zero_lt_one.trans hx₁
  have hlog := Real.log_pos hx₁
  let P (m : ℕ) : ℝ := ∑' p, primePowerTerm x p m
  let L (m : ℕ) : ℝ := Real.logarithmicIntegralReal (x ^ (-((m : ℝ) + 1))) / ((m : ℝ) + 2)
  let B (m : ℕ) : ℝ := η / Real.log x ^ (k + 1) *
    (x⁻¹ ^ (m + 1) / ((m : ℝ) + 2) + x⁻¹ ^ (m + 1) / ((m : ℝ) + 1))
  have hP : Summable P := (summable_primePowerTerm hx₁).prod_symm.prod
  have hS : (∑' p : ℕ,
      if p.Prime ∧ x < p then Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) else 0) =
      -(∑' m, P m) := by
    change _ = -(∑' m, ∑' p, primePowerTerm x p m)
    rw [(summable_primePowerTerm hx₁).tsum_comm, ← tsum_neg]
    apply tsum_congr
    intro p
    rw [tsum_primePowerTerm hx₁, neg_neg]
  have hB := (hasSum_mertens_coefficients hx₁).mul_left (η / Real.log x ^ (k + 1))
  have hbound (m : ℕ) : |L m + P m| < B m := by
    have h := abs_logarithmicIntegral_add_tsum_inv_prime_pow_lt k hk η x₀ hη hx₀ hθ (m + 2)
      (by omega) x hx
    have hexp : (1 : ℝ) - ((m + 2 : ℕ) : ℝ) = -((m : ℝ) + 1) := by push_cast; ring
    have h₁ : 0 < (m : ℝ) + 1 := by positivity
    have h₂ : 0 < (m : ℝ) + 2 := by positivity
    rw [hexp, show m + 2 - 1 = m + 1 by rfl] at h
    push_cast at h
    rw [show (m : ℝ) + 2 - 1 = (m : ℝ) + 1 by ring] at h
    have hP' : P m = (∑' p : ℕ, if p.Prime ∧ x < p then 1 / (p : ℝ) ^ (m + 2) else 0) /
        ((m : ℝ) + 2) := by
      exact tsum_div_const
    calc
      |L m + P m| = |Real.logarithmicIntegralReal (x ^ (-((m : ℝ) + 1))) +
          ∑' p : ℕ, if p.Prime ∧ x < p then 1 / (p : ℝ) ^ (m + 2) else 0| /
          ((m : ℝ) + 2) := by
        dsimp only [L]
        rw [hP', ← add_div, abs_div, abs_of_pos h₂]
      _ < _ := (div_lt_div_iff_of_pos_right h₂).2 h
      _ = B m := by
        dsimp [B]
        rw [inv_pow]
        field_simp
  have habs : Summable (fun m ↦ |L m + P m|) :=
    hB.summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) (fun m ↦ (hbound m).le)
  have herr : Summable (fun m ↦ L m + P m) := .of_norm (by simpa [Real.norm_eq_abs] using habs)
  have hL : Summable L := (herr.sub hP).congr fun m ↦ add_sub_cancel_right (L m) (P m)
  rw [hS]
  change |-(∑' m, P m) - (∑' m, L m)| < _
  rw [sub_eq_add_neg, ← neg_add_rev, ← hL.tsum_add hP, abs_neg]
  calc
    |∑' m, (L m + P m)| ≤ ∑' m, |L m + P m| := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := fun m ↦ L m + P m)
          (by simpa only [Real.norm_eq_abs] using habs))
    _ < ∑' m, B m := Summable.tsum_lt_tsum (fun m ↦ (hbound m).le) (hbound 0) habs hB.summable
    _ = _ := hB.tsum_eq

end MetaMathlibExt
