/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.NumberTheory.Recurrences.KJacobsthal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MathlibExt.NumberTheory.Recurrences.LucasBinetFormula
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Integral representation of the companion k-Jacobsthal numbers

We prove the integral representation of the companion `k`-Jacobsthal numbers at multiples:
`companionKJacobsthal_mul_eq_integral`, and Theorem 9, `two_mul_companionKJacobsthal`, which the
integral proof uses.

Statements from Weerayuth Nilsrakoo and Achariya Nilsrakoo, "An Integral Representation of
k-Jacobsthal and k-Jacobsthal-Lucas Numbers", *INTEGERS* 25 (2025), Article A74
(<https://math.colgate.edu/~integers/z74/z74.pdf>).

The Lean proof adapts two existing ones. `integral_kernel` follows
`jacobsthal_mul_add_eq_integral.integral_kernel` in
`MathlibExt/NumberTheory/Recurrences/JacobsthalOffsetIntegral.lean`, with `3` replaced by a nonzero
`δ` (its single exceptional point and the local derivative proof of the successor case). The
characteristic roots `α` and `β` and the Binet formulas in the main proof follow the setup of
`tendsto_lucasU_kJacobsthal_ratio` in `MathlibExt/NumberTheory/Recurrences/KJacobsthal.lean`.
-/

namespace MetaMathlibExt

open MeasureTheory

local notation "J[" k ", " n "]" => (lucasU (kJacobsthalParams k) n : ℝ)
local notation "jL[" k ", " n "]" => (lucasV (kJacobsthalParams k) n : ℝ)
local notation "Δ[" k "]" => Real.sqrt ((k : ℝ) ^ 2 + 8)

/-- **Companion $k$-Jacobsthal numbers via Lucas sequences.** For a natural number $k$ and
integers $a, b$, let $\mathcal{J}_{k,n}(a, b)$ be the companion $k$-Jacobsthal numbers, and let
$J_{k,n} = U_n(k, -2)$ and $j_{k,n} = V_n(k, -2)$ be the $k$-Jacobsthal and $k$-Jacobsthal–Lucas
numbers, the Lucas sequences $U$ and $V$ with parameters $(P, Q) = (k, -2)$. Then for every
natural number $n$, $2\,\mathcal{J}_{k,n}(a, b) = a\,j_{k,n} + (2b - ak)\,J_{k,n}$.

The source states this as $\mathcal{J}_{k,n} = \tfrac{a}{2} j_{k,n} + \tfrac{2b - ak}{2} J_{k,n}$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 9 (`integers-2025-A74-thm-9`). -/
public theorem two_mul_companionKJacobsthal (k : ℕ) (a b : ℤ) (n : ℕ) :
    2 * companionKJacobsthal k a b n =
      a * lucasV (kJacobsthalParams k) n + (2 * b - a * k) * lucasU (kJacobsthalParams k) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [companionKJacobsthal, lucasU, lucasV]; ring
  | one => simp [companionKJacobsthal, lucasU, lucasV, kJacobsthalParams]
  | more n ih1 ih2 =>
    have hC := companionKJacobsthal_add_two k a b n
    have hU := lucasU_add_two (kJacobsthalParams k) n
    have hV : lucasV (kJacobsthalParams k) (n + 2) =
        (kJacobsthalParams k).p * lucasV (kJacobsthalParams k) (n + 1) -
          (kJacobsthalParams k).q * lucasV (kJacobsthalParams k) n := rfl
    have hp : (kJacobsthalParams k).p = (k : ℤ) := rfl
    have hq : (kJacobsthalParams k).q = -2 := rfl
    rw [hC, hU, hV, hp, hq]
    linear_combination (k : ℤ) * ih2 + 2 * ih1

-- The primitive is (d / δ + c * x) * (b + δ * a * x) ^ n.
private theorem companionKJacobsthal_mul_eq_integral.integral_kernel (a b c d δ : ℝ)
    (hδ : δ ≠ 0) (h : b + δ * a ≠ 0) (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, (n * a * d + c * b + δ * (n + 1) * a * c * x) *
      (b + δ * a * x) ^ ((n : ℤ) - 1)) =
      (d / δ + c) * (b + δ * a) ^ n - (d / δ - c) * (b - δ * a) ^ n := by
  cases n with
  | zero =>
    have hne : ∀ᵐ x : ℝ, b + δ * a * x ≠ 0 := by
      by_cases ha : δ * a = 0
      · simpa [ha] using h
      · filter_upwards [volume.ae_ne (-b / (δ * a))] with x hx
        exact fun hz => hx ((eq_div_iff ha).2 (by linarith))
    calc
      _ = ∫ _ in (-1 : ℝ)..1, c := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hne] with x hx
        intro _
        simp only [Nat.cast_zero, zero_mul, zero_add, zero_sub, zpow_neg_one]
        field_simp
      _ = _ := by simp [intervalIntegral.integral_const]; ring
  | succ n =>
    simp only [Nat.cast_succ, add_sub_cancel_right, zpow_natCast]
    let F := fun x : ℝ => (d / δ + c * x) * (b + δ * a * x) ^ (n + 1)
    calc
      _ = F 1 - F (-1) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro x _
          have hlin (u v : ℝ) : HasDerivAt (fun y => u + v * y) v x := by
            simpa using ((hasDerivAt_id x).const_mul v).const_add u
          convert (hlin (d / δ) c).fun_mul ((hlin b (δ * a)).fun_pow (n + 1)) using 1
          simp only [Nat.add_sub_cancel, Nat.cast_succ, pow_succ]
          field_simp
          ring
        · apply Continuous.intervalIntegrable
          fun_prop
      _ = _ := by simp [F, sub_eq_add_neg]

/-- **Integral representation of the companion $k$-Jacobsthal numbers.** Let $k$, $\ell$, $n$ be
natural numbers and $a, b$ integers. Write $\mathcal{J}_{k,m} = \mathcal{J}_{k,m}(a, b)$ for the
companion $k$-Jacobsthal numbers, $J_{k,m} = U_m(k, -2)$ and $j_{k,m} = V_m(k, -2)$ for the
$k$-Jacobsthal and $k$-Jacobsthal-Lucas numbers, and $\Delta_k = \sqrt{k^2 + 8}$. Then, in
$\mathbb{R}$,
$$
\mathcal{J}_{k,\ell n} = \frac{1}{2^{n+1}} \int_{-1}^{1}
\bigl(a\,j_{k,\ell} + (2b - ak)\,n\,J_{k,\ell} + a(n+1)\Delta_k J_{k,\ell}\,x\bigr)
\bigl(j_{k,\ell} + \Delta_k J_{k,\ell}\,x\bigr)^{n-1}\,dx,
$$
where the power $n - 1$ is an integer power (for $n = 0$ it is the reciprocal).

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 12 (`integers-2025-A74-thm-12`). -/
public theorem companionKJacobsthal_mul_eq_integral (k ℓ n : ℕ) (a b : ℤ) :
    (companionKJacobsthal k a b (ℓ * n) : ℝ) =
      1 / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
        (a * jL[k, ℓ] + (2 * b - a * k) * n * J[k, ℓ] +
            a * (n + 1) * Δ[k] * J[k, ℓ] * x) *
          (jL[k, ℓ] + Δ[k] * J[k, ℓ] * x) ^ ((n : ℤ) - 1) := by
  let α := ((k : ℝ) + Δ[k]) / 2
  let β := ((k : ℝ) - Δ[k]) / 2
  have hΔ : 0 < Δ[k] := Real.sqrt_pos.2 (by positivity)
  have hΔ_ne : Δ[k] ≠ 0 := ne_of_gt hΔ
  have hα_pos : 0 < α := by dsimp [α]; positivity
  have hβα : β < α := by dsimp [α, β]; linarith
  have hsum : α + β = ((kJacobsthalParams k).p : ℝ) := by simp [α, β, kJacobsthalParams]; ring
  have hprod : α * β = ((kJacobsthalParams k).q : ℝ) := by
    simp [α, β, kJacobsthalParams]
    nlinarith [Real.sq_sqrt (show 0 ≤ (k : ℝ) ^ 2 + 8 by positivity)]
  have hbinet := (lucas_binet_formulas_of_field (kJacobsthalParams k) α β hsum hprod).1 hβα.ne'
  have hsub : α - β = Δ[k] := by dsimp [α, β]; ring
  have hplus (m : ℕ) : jL[k, m] + Δ[k] * J[k, m] = 2 * α ^ m := by
    rw [(hbinet m).1, (hbinet m).2, hsub]; field_simp; ring
  have hminus (m : ℕ) : jL[k, m] - Δ[k] * J[k, m] = 2 * β ^ m := by
    rw [(hbinet m).1, (hbinet m).2, hsub]; field_simp; ring
  have hpos : 0 < 2 * α ^ ℓ := by positivity
  have h_nonzero : jL[k, ℓ] + Δ[k] * J[k, ℓ] ≠ 0 := by rw [hplus ℓ]; exact ne_of_gt hpos
  have h_comp := two_mul_companionKJacobsthal k a b (ℓ * n)
  have h_comp_real : 2 * ((companionKJacobsthal k a b (ℓ * n) : ℤ) : ℝ) =
      (a : ℝ) * jL[k, ℓ * n] + (((2 * b - a * k : ℤ)) : ℝ) * J[k, ℓ * n] := by
    exact_mod_cast h_comp
  have hU := (hbinet (ℓ * n)).1
  have hV := (hbinet (ℓ * n)).2
  rw [hsub] at hU
  have hC : ((companionKJacobsthal k a b (ℓ * n) : ℤ) : ℝ) =
      ((a : ℝ) * jL[k, ℓ * n] + (((2 * b - a * k : ℤ)) : ℝ) * J[k, ℓ * n]) / 2 := by
    linarith
  have h_kernel :=
    companionKJacobsthal_mul_eq_integral.integral_kernel J[k, ℓ] jL[k, ℓ]
      (a : ℝ) (((2 * b - a * k : ℤ)) : ℝ) Δ[k] hΔ_ne h_nonzero n
  have h_congr : (∫ x in (-1 : ℝ)..1, (a * jL[k, ℓ] + (2 * b - a * k) * n * J[k, ℓ] +
      a * (n + 1) * Δ[k] * J[k, ℓ] * x) * (jL[k, ℓ] + Δ[k] * J[k, ℓ] * x) ^ ((n : ℤ) - 1)) =
      (∫ x in (-1 : ℝ)..1, (n * J[k, ℓ] * (((2 * b - a * k : ℤ)) : ℝ) + (a : ℝ) * jL[k, ℓ] +
        Δ[k] * (n + 1) * J[k, ℓ] * (a : ℝ) * x) *
        (jL[k, ℓ] + Δ[k] * J[k, ℓ] * x) ^ ((n : ℤ) - 1)) := by
    apply intervalIntegral.integral_congr
    intro x _
    push_cast
    ring
  rw [h_congr, h_kernel, hplus ℓ, hminus ℓ, hC, hV, hU]
  have h2 : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
  simp only [pow_add, pow_mul, mul_pow, pow_one]
  field_simp
  ring

end MetaMathlibExt
