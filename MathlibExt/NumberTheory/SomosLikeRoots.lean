/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity

/-!
# Root asymptotics of Somos-type sequences

Above the Somos constant, the normalized roots of a Somos-type sequence are nonincreasing
and converge to a limit greater than one.
-/

namespace MetaMathlibExt

open Filter Topology

/-- **Root asymptotics of Somos-type sequences.** Let $k \ge 2$ be a natural number, let
$\sigma_k = \exp\bigl(\sum_{m \ge 1} \log m / k^m\bigr)$ be the $k$-Somos constant, and let
$t : \mathbb{N} \to \mathbb{R}$ satisfy $t(n + 1) = t(n)^k / (n + 1)$ for all $n \ge 0$. If
$t(0) > \sigma_k$, then the sequence $n \mapsto t(n)^{1/k^n}$ is nonincreasing and converges to
some real number $c > 1$.

The sequence is constant from $n = 0$ to $n = 1$, so the paper's "decreases monotonically" is
read in the non-strict sense.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 8 (`jis-2024-24.8.1-lem-8`). -/
public theorem somosLike_root_antitone_tendsto (k : ℕ) (hk : 2 ≤ k) (t : ℕ → ℝ)
    (ht : ∀ n : ℕ, t (n + 1) = t n ^ k / (n + 1))
    (h0 : Real.exp (∑' m : ℕ, Real.log m / (k : ℝ) ^ m) < t 0) :
    ∃ c : ℝ, 1 < c ∧ Antitone (fun n : ℕ => t n ^ ((1 : ℝ) / (k : ℝ) ^ n)) ∧
      Tendsto (fun n : ℕ => t n ^ ((1 : ℝ) / (k : ℝ) ^ n)) atTop (𝓝 c) := by
  have hk₁ : 1 < (k : ℝ) := by exact_mod_cast (show 1 < k from hk)
  have hk₀ : 0 < (k : ℝ) := zero_lt_one.trans hk₁
  let a (m : ℕ) : ℝ := Real.log m / (k : ℝ) ^ m
  have ha_nonneg (m : ℕ) : 0 ≤ a m :=
    div_nonneg (Real.log_natCast_nonneg m) (pow_nonneg hk₀.le _)
  have hgeom : ‖(k : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk₀)]
    exact inv_lt_one_of_one_lt₀ hk₁
  have ha : Summable a := by
    refine (hasSum_coe_mul_geometric_of_norm_lt_one hgeom).summable.of_nonneg_of_le
      ha_nonneg fun m => ?_
    simpa only [a, inv_pow, ← div_eq_mul_inv] using
      div_le_div_of_nonneg_right (Real.log_le_self (Nat.cast_nonneg m)) (pow_nonneg hk₀.le m)
  have ht_pos (n : ℕ) : 0 < t n := by
    induction n with
    | zero => exact (Real.exp_pos _).trans h0
    | succ n ih =>
      rw [ht n]
      exact div_pos (pow_pos ih _) (by positivity)
  have hlog (n : ℕ) :
      Real.log (t n) / (k : ℝ) ^ n = Real.log (t 0) - ∑ m ∈ Finset.range (n + 1), a m := by
    induction n with
    | zero => simp [a]
    | succ n ih =>
      have hn : 0 < (n : ℝ) + 1 := by positivity
      rw [ht n, Real.log_div (pow_ne_zero _ (ht_pos n).ne') hn.ne', Real.log_pow,
        Finset.sum_range_succ, ← sub_sub, ← ih]
      simp only [a, Nat.cast_add, Nat.cast_one, sub_div, pow_succ']
      rw [mul_div_mul_left _ _ hk₀.ne']
  have hroot (n : ℕ) :
      t n ^ ((1 : ℝ) / (k : ℝ) ^ n) =
        Real.exp (Real.log (t 0) - ∑ m ∈ Finset.range (n + 1), a m) := by
    rw [Real.rpow_def_of_pos (ht_pos n), mul_one_div, hlog n]
  have hlimit : Tendsto (fun n => ∑ m ∈ Finset.range (n + 1), a m) atTop (𝓝 (∑' m, a m)) :=
    ha.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hgap : 0 < Real.log (t 0) - ∑' m, a m := by
    apply sub_pos.mpr
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) h0
  refine ⟨Real.exp (Real.log (t 0) - ∑' m, a m), Real.one_lt_exp_iff.mpr hgap, ?_, ?_⟩
  · refine antitone_nat_of_succ_le fun n => ?_
    simp only [hroot, Real.exp_le_exp, Finset.sum_range_succ (n := n + 1)]
    exact sub_le_sub_left (le_add_of_nonneg_right (ha_nonneg (n + 1))) _
  · simp only [hroot]
    exact Real.continuous_exp.continuousAt.tendsto.comp (tendsto_const_nhds.sub hlimit)

end MetaMathlibExt
