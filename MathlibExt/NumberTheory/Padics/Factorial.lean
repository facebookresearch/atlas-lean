/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Tactic.Ring

/-!
# Factorials in the p-adic numbers

Since `p ^ k ∣ n!` once `n ≥ p ^ k`, the factorials tend to `0` `p`-adically.

## Main statements

* `Padic.tendsto_factorial_atTop_nhds_zero`: `n! → 0` in `ℚ_[p]`.
* `Padic.hasSum_mul_factorial`: `∑_{n ≥ 0} n · n! = -1` in `ℚ_[p]`.
* `PadicInt.not_exists_continuous_eq_factorial`: no continuous function `ℤ_[p] → ℚ_[p]`
  interpolates `n ↦ n!`.
-/

@[expose] public section

open Filter Topology

namespace Padic

variable (p : ℕ) [Fact p.Prime]

/-- The factorials tend to `0` in `ℚ_[p]`. -/
theorem tendsto_factorial_atTop_nhds_zero :
    Tendsto (fun n : ℕ => (n.factorial : ℚ_[p])) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlim : Tendsto (fun k : ℕ => ((p : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)
  rw [Metric.tendsto_atTop] at hlim ⊢
  intro ε hε
  obtain ⟨K, hK⟩ := hlim ε hε
  refine ⟨p ^ K, fun n hn => ?_⟩
  have hdvd : p ^ K ∣ n.factorial :=
    Nat.dvd_factorial (pow_pos (Fact.out : p.Prime).pos K) hn
  have hle : ‖(n.factorial : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(K : ℤ)) := by
    have := (Padic.norm_int_le_pow_iff_dvd (p := p) (n.factorial : ℤ) K).2
      (by exact_mod_cast hdvd)
    simpa using this
  have h2 := hK K le_rfl
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h2
  rw [dist_zero_right, norm_norm]
  calc ‖(n.factorial : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(K : ℤ)) := hle
    _ = ((p : ℝ)⁻¹) ^ K := by rw [zpow_neg, zpow_natCast, inv_pow]
    _ < ε := h2

/-- `∑_{n ≥ 0} n · n! = -1` in `ℚ_[p]`: the partial sums are `N! - 1`. -/
theorem hasSum_mul_factorial :
    HasSum (fun n : ℕ => (n : ℚ_[p]) * n.factorial) (-1) := by
  have hsum : ∀ N : ℕ, ∑ n ∈ Finset.range N, (n : ℚ_[p]) * n.factorial =
      (N.factorial : ℚ_[p]) - 1 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Nat.factorial_succ]
      push_cast
      ring
  have hfac := tendsto_factorial_atTop_nhds_zero p
  have hsummable : Summable fun n : ℕ => (n : ℚ_[p]) * n.factorial := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [Nat.cofinite_eq_atTop]
    have h1 : Tendsto (fun n : ℕ => ((n + 1).factorial : ℚ_[p]) - n.factorial) atTop
        (𝓝 (0 - 0)) := ((tendsto_add_atTop_iff_nat 1).2 hfac).sub hfac
    rw [sub_zero] at h1
    refine h1.congr fun n => ?_
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hsummable.hasSum_iff_tendsto_nat]
  simp_rw [hsum]
  simpa using hfac.sub_const 1

end Padic

namespace PadicInt

/-- No continuous function `f : ℤ_[p] → ℚ_[p]` satisfies `f n = n!` for every natural number
`n`: along `n = p ^ k → 0`, the values `(p ^ k)!` tend to `0`, whereas `f 0 = 0! = 1`. -/
theorem not_exists_continuous_eq_factorial (p : ℕ) [Fact p.Prime] :
    ¬ ∃ f : ℤ_[p] → ℚ_[p], Continuous f ∧ ∀ n : ℕ, f n = (n.factorial : ℚ_[p]) := by
  rintro ⟨f, hf, hfn⟩
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpow : Tendsto (fun k : ℕ => ((p ^ k : ℕ) : ℤ_[p])) atTop (𝓝 0) := by
    have hlt : ‖(p : ℤ_[p])‖ < 1 := by
      rw [PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp1)
    simpa using tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  have h1 : Tendsto (fun k : ℕ => f ((p ^ k : ℕ) : ℤ_[p])) atTop (𝓝 (f ((0 : ℕ) : ℤ_[p]))) := by
    simpa [Function.comp_def] using (hf.tendsto _).comp hpow
  have h2 : Tendsto (fun k : ℕ => f ((p ^ k : ℕ) : ℤ_[p])) atTop (𝓝 0) := by
    have hk : Tendsto (fun k : ℕ => p ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hp1
    refine ((Padic.tendsto_factorial_atTop_nhds_zero p).comp hk).congr fun k => ?_
    rw [Function.comp_apply, hfn]
  have := tendsto_nhds_unique h1 h2
  rw [hfn 0] at this
  simp at this

end PadicInt
