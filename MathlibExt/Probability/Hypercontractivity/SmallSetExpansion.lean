/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCubeNoiseStability
public import MathlibExt.Probability.Hypercontractivity.VectorTwoPoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Small-set expansion of the noisy hypercube

From the Bonami–Beckner inequality `‖T_σ f‖₂ ≤ ‖f‖_{1+σ²}` on the uniform cube
(`StatMech.Probability.vtp_hypercontractivity`) and `Stab_{σ²}[f] = ‖T_σ f‖₂²`, the noise
stability satisfies `Stab_ρ[f] ≤ ‖f‖_{1+ρ}²` for `0 ≤ ρ ≤ 1`: the second form of O'Donnell's
(p,2)-Hypercontractivity Theorem. For the indicator `1_A` of a set of volume `α`,
`‖1_A‖_q = α^{1/q}` gives the Small-Set Expansion Theorem `Stab_ρ[1_A] ≤ α^{2/(1+ρ)}`: if `x` is
uniform in a small set `A` and `y` is `ρ`-correlated with `x`, then `y` is unlikely to lie in `A`.

## Main statements

* `BooleanCube.boolNoiseStab_le_bnt_qnorm_sq`: `Stab_ρ[f] ≤ ‖f‖_{1+ρ}²` for `0 ≤ ρ ≤ 1`.
* `BooleanCube.boolNoiseStab_le_rpow_of_indicator`: the Small-Set Expansion Theorem.

## References

* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Chapter 9: the (p,2)-Hypercontractivity Theorem (chapter introduction)
  and the Small-Set Expansion Theorem (Section 9.5).
-/

@[expose] public section

namespace BooleanCube

open scoped BigOperators
open StatMech.Probability

variable {n : ℕ}

/-- **Squared `L²` norm on the cube.** For every `g : BoolCube n → ℝ`, the square of the uniform
`L²` norm `StatMech.Probability.bnt_qnorm 2 g` is the second moment `𝔼[g²]`. -/
theorem bnt_qnorm_two_sq (g : BoolCube n → ℝ) : bnt_qnorm 2 g ^ 2 = 𝔼 x, g x ^ 2 := by
  have hpow : bnt_qnormPow 2 g = 𝔼 x, g x ^ 2 := by
    rw [bnt_qnormPow, bnt_uexp_eq_expect]
    refine Finset.expect_congr rfl fun x _ => ?_
    rw [Real.rpow_two, sq_abs]
  have hnn : 0 ≤ 𝔼 x, g x ^ 2 := Finset.expect_nonneg fun _ _ => sq_nonneg _
  rw [bnt_qnorm, hpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hnn]

/-- **(p,2)-hypercontractivity in noise-stability form.** For `0 ≤ ρ ≤ 1` and every
`f : BoolCube n → ℝ`, `Stab_ρ[f] ≤ ‖f‖_{1+ρ}²`, where `‖f‖_q = (𝔼|f|^q)^{1/q}` is
`StatMech.Probability.bnt_qnorm q f` (R. O'Donnell, *Analysis of Boolean Functions*, 2014,
Chapter 9, the (p,2)-Hypercontractivity Theorem: "Equivalently, `Stab_ρ[f] ≤ ‖f‖²_{1+ρ}` for
`0 ≤ ρ ≤ 1`"). -/
theorem boolNoiseStab_le_bnt_qnorm_sq {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (f : BoolCube n → ℝ) :
    boolNoiseStab ρ f ≤ bnt_qnorm (1 + ρ) f ^ 2 := by
  set σ := Real.sqrt ρ
  have hσ2 : σ ^ 2 = ρ := Real.sq_sqrt h0
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg ρ
  have hσ1 : σ ≤ 1 := Real.sqrt_le_one.mpr h1
  have hc := vtp_hypercontractivity hσ0 hσ1 n f
  rw [bnt_noiseOp_eq_boolNoiseOp, hσ2] at hc
  calc boolNoiseStab ρ f = boolNoiseStab (σ ^ 2) f := by rw [hσ2]
    _ = 𝔼 x, boolNoiseOp σ f x ^ 2 := boolNoiseStab_sq_eq_expect_sq σ f
    _ = bnt_qnorm 2 (boolNoiseOp σ f) ^ 2 := (bnt_qnorm_two_sq _).symm
    _ ≤ bnt_qnorm (1 + ρ) f ^ 2 := pow_le_pow_left₀ (bnt_qnorm_nonneg _ _) hc 2

/-- **Small-Set Expansion Theorem.** Let `f : BoolCube n → ℝ` be the indicator of a set
`A ⊆ {-1, 1}ⁿ` (values in `{0, 1}`) of volume `α = 𝔼[f]`. Then for every `0 ≤ ρ ≤ 1`,
`Stab_ρ[1_A] ≤ α^{2/(1+ρ)}`; here `Stab_ρ[1_A] = Pr[x ∈ A, y ∈ A]` for a `ρ`-correlated pair
`(x, y)` (R. O'Donnell, *Analysis of Boolean Functions*, 2014, Small-Set Expansion Theorem,
Section 9.5). -/
theorem boolNoiseStab_le_rpow_of_indicator {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    {f : BoolCube n → ℝ} (hf : ∀ x, f x = 0 ∨ f x = 1) :
    boolNoiseStab ρ f ≤ (𝔼 x, f x) ^ (2 / (1 + ρ)) := by
  have hq : (0 : ℝ) < 1 + ρ := by linarith
  have hpow : bnt_qnormPow (1 + ρ) f = 𝔼 x, f x := by
    rw [bnt_qnormPow, bnt_uexp_eq_expect]
    refine Finset.expect_congr rfl fun x _ => ?_
    rcases hf x with h | h
    · rw [h, abs_zero, Real.zero_rpow hq.ne']
    · rw [h, abs_one, Real.one_rpow]
  have hnn : 0 ≤ 𝔼 x, f x :=
    Finset.expect_nonneg fun x _ => by rcases hf x with h | h <;> simp [h]
  have hnorm : bnt_qnorm (1 + ρ) f ^ 2 = (𝔼 x, f x) ^ (2 / (1 + ρ)) := by
    rw [bnt_qnorm, hpow, ← Real.rpow_natCast, ← Real.rpow_mul hnn]
    congr 1
    push_cast
    ring
  exact hnorm ▸ boolNoiseStab_le_bnt_qnorm_sq h0 h1 f

end BooleanCube
