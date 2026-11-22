/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.PoissonConvergenceCore
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Tests for the analytic core of Poisson convergence

A restatement of `elem_symm_poly_tendsto_poisson` with its exact
public signature, a concrete instance (constant rows `1 / (n + 1)`,
`λ = 1`, `j = 2`), and a formalized counterexample to the
*uncorrected* v1 statement: the signed family `+1 / n` on the first
`n ^ 2` coordinates and `-1 / n` on the remaining `n ^ 2` satisfies
the v1 hypotheses with `λ = 0`, but its mass at `j = 1` stays above
`1 / 4`, so it does not converge to the Poisson mass `0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Real Topology
open scoped ENNReal NNReal Topology

namespace MathlibExtTest.Probability.PoissonConvergenceCore

/-- The corrected analytic core restates with the exact public signature. -/
example {k : ℕ → ℕ} {p : (n : ℕ) → Fin (k n) → ℝ} {lam : ℝ≥0}
    (hp_nonneg : ∀ n i, 0 ≤ p n i)
    (hMaxTendsto : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : Fin (k n), p n i < ε)
    (hSumTendsto : Filter.Tendsto (fun n => ∑ i : Fin (k n), p n i) atTop (𝓝 (lam : ℝ)))
    (j : ℕ) :
    Filter.Tendsto (fun n => ∑ A ∈ (Finset.univ : Finset (Fin (k n))).powersetCard j,
        (∏ i ∈ A, p n i) * (∏ i ∈ Finset.univ \ A, (1 - p n i)))
      atTop (𝓝 (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ j / (Nat.factorial j : ℝ))) :=
  elem_symm_poly_tendsto_poisson hp_nonneg hMaxTendsto hSumTendsto j

/-- Concrete instance: constant rows `1 / (n + 1)`, `λ = 1`, `j = 2`. -/
example : Filter.Tendsto (fun n => ∑ A ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard 2,
      (∏ _i ∈ A, (1:ℝ) / ((n : ℝ) + 1)) * (∏ _i ∈ Finset.univ \ A, (1 - (1:ℝ) / ((n : ℝ) + 1))))
    atTop (𝓝 (Real.exp (-((1 : ℝ≥0) : ℝ)) * ((1 : ℝ≥0) : ℝ) ^ 2 / (Nat.factorial 2 : ℝ))) := by
  have hp : ∀ (n : ℕ) (_i : Fin (n + 1)), 0 ≤ (1:ℝ) / ((n : ℝ) + 1) :=
    fun n _ => div_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg n) zero_le_one)
  have hMax : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ i : Fin (n + 1), (1:ℝ) / ((n : ℝ) + 1) < ε := by
    intro ε hε
    have hEv := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds hε)
    filter_upwards [hEv] with n hn i
    exact hn
  have hSum1 : ∀ n, ∑ i : Fin (n + 1), (1:ℝ) / ((n : ℝ) + 1) = 1 := by
    intro n
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    exact mul_one_div_cancel (by positivity)
  have hSum : Filter.Tendsto (fun n => ∑ i : Fin (n + 1), (1:ℝ) / ((n : ℝ) + 1)) atTop
      (𝓝 (((1 : ℝ≥0)) : ℝ)) := by
    simp only [NNReal.coe_one]
    rw [show (fun n => ∑ i : Fin (n + 1), (1:ℝ) / ((n : ℝ) + 1)) = fun _ => 1 from
      funext fun n => hSum1 n]
    exact tendsto_const_nhds
  exact elem_symm_poly_tendsto_poisson hp hMax hSum 2

/-- Mass at `j = 1` equals the full product times `∑ q i / (1 - q i)`. -/
private theorem mass_one_eq {m : ℕ} {q : Fin m → ℝ} (h : ∀ i, (1:ℝ) - q i ≠ 0) :
    ∑ A ∈ Finset.univ.powersetCard 1, (∏ i ∈ A, q i) * (∏ i ∈ Finset.univ \ A, (1 - q i))
      = (∏ i, (1 - q i)) * ∑ i, q i / (1 - q i) := by
  rw [Finset.powersetCard_one, Finset.sum_map, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  show (∏ j ∈ ({i} : Finset (Fin m)), q j) * (∏ j ∈ Finset.univ \ ({i} : Finset (Fin m)), (1 - q j))
      = (∏ j, (1 - q j)) * (q i / (1 - q i))
  rw [Finset.prod_singleton,
    Finset.prod_eq_mul_prod_sdiff_singleton i (fun j => 1 - q j)
      (fun hi => (hi (Finset.mem_univ i)).elim)]
  have hne := h i
  field_simp

/-- The counterexample family: `+1 / n` on the first `n ^ 2` coordinates,
`-1 / n` on the remaining `n ^ 2`. -/
private noncomputable def counterP : (n : ℕ) → Fin (2 * n ^ 2) → ℝ :=
  fun n i => if (i : ℕ) < n ^ 2 then 1 / (n : ℝ) else -1 / (n : ℝ)

/-- The counterexample family, indexed by `ℕ`. -/
private noncomputable def counterQ (n : ℕ) : ℕ → ℝ := fun i => if i < n ^ 2 then 1 / (n : ℝ) else -1 / (n : ℝ)

/-- Row sums of the counterexample family are `0`. -/
private theorem counter_sum (n : ℕ) : ∑ i : Fin (2 * n ^ 2), counterP n i = 0 := by
  have hEq : (∑ i : Fin (2 * n ^ 2), counterP n i)
      = ∑ i ∈ Finset.range (2 * n ^ 2), counterQ n i :=
    Fin.sum_univ_eq_sum_range (fun i => counterQ n i) (2 * n ^ 2)
  rw [hEq]
  have hsplit : (2 * n ^ 2) = n ^ 2 + n ^ 2 := by ring
  rw [hsplit, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range (n ^ 2), counterQ n x = (n ^ 2 : ℝ) * (1 / (n : ℝ)) := by
    have hpt : ∀ x ∈ Finset.range (n ^ 2), counterQ n x = 1 / (n : ℝ) := by
      intro x hx
      have hlt : x < n ^ 2 := Finset.mem_range.mp hx
      show (if x < n ^ 2 then (1:ℝ)/(n:ℝ) else -1/(n:ℝ)) = 1/(n:ℝ)
      rw [ite_eq_left hlt]
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_cast
  have h2 : ∑ x ∈ Finset.range (n ^ 2), counterQ n (n ^ 2 + x) = (n ^ 2 : ℝ) * (-1 / (n : ℝ)) := by
    have hpt : ∀ x ∈ Finset.range (n ^ 2), counterQ n (n ^ 2 + x) = -1 / (n : ℝ) := by
      intro x hx
      have hge : ¬ (n ^ 2 + x < n ^ 2) := by omega
      show (if n ^ 2 + x < n ^ 2 then (1:ℝ)/(n:ℝ) else -1/(n:ℝ)) = -1/(n:ℝ)
      rw [ite_eq_right hge]
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_cast
  rw [h1, h2]
  ring

/-- The `p / (1 - p)` sum of the counterexample family equals
`2 n ^ 2 / (n ^ 2 - 1)` for `n ≥ 2`. -/
private theorem counter_ratio_sum (n : ℕ) (hn : 2 ≤ n) :
    ∑ i : Fin (2 * n ^ 2), counterP n i / (1 - counterP n i)
      = 2 * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) := by
  have hEq : (∑ i : Fin (2 * n ^ 2), counterP n i / (1 - counterP n i))
      = ∑ i ∈ Finset.range (2 * n ^ 2), counterQ n i / (1 - counterQ n i) :=
    Fin.sum_univ_eq_sum_range (fun i => counterQ n i / (1 - counterQ n i)) (2 * n ^ 2)
  rw [hEq]
  have hsplit : (2 * n ^ 2) = n ^ 2 + n ^ 2 := by ring
  rw [hsplit, Finset.sum_range_add]
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1:ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hnne : (n : ℝ) ≠ 0 := hnR.ne'
  have hn1ne : (n : ℝ) - 1 ≠ 0 := by linarith
  have hnp1ne : (n : ℝ) + 1 ≠ 0 := by linarith
  have hden1 : (1:ℝ) - 1/(n:ℝ) ≠ 0 := by
    rw [sub_ne_zero, ne_eq, eq_comm, div_eq_one_iff_eq hnne]
    exact ne_of_lt hn1
  have hden2 : (1:ℝ) - (-1/(n:ℝ)) ≠ 0 := by
    have h2 : (1:ℝ) - (-1/(n:ℝ)) = 1 + 1/(n:ℝ) := by ring
    rw [h2]
    positivity
  have hterm1 : ∀ x : ℕ, x < n ^ 2 → counterQ n x / (1 - counterQ n x) = 1 / ((n : ℝ) - 1) := by
    intro x hx
    show (if x < n ^ 2 then (1:ℝ)/(n:ℝ) else -1/(n:ℝ))
      / (1 - (if x < n ^ 2 then (1:ℝ)/(n:ℝ) else -1/(n:ℝ))) = 1 / ((n : ℝ) - 1)
    rw [ite_eq_left hx, div_eq_iff hden1]
    field_simp
  have hterm2 : ∀ x : ℕ, counterQ n (n ^ 2 + x) / (1 - counterQ n (n ^ 2 + x))
      = -1 / ((n : ℝ) + 1) := by
    intro x
    have hge : ¬ (n ^ 2 + x < n ^ 2) := by omega
    show (if n ^ 2 + x < n ^ 2 then (1:ℝ)/(n:ℝ) else -1/(n:ℝ))
      / (1 - (if n ^ 2 + x < n ^ 2 then (1:ℝ)/(n:ℝ) else -1/(n:ℝ))) = -1 / ((n : ℝ) + 1)
    rw [ite_eq_right hge, div_eq_iff hden2]
    field_simp
    ring
  have h1 : ∑ x ∈ Finset.range (n ^ 2), counterQ n x / (1 - counterQ n x)
      = (n ^ 2 : ℝ) * (1 / ((n : ℝ) - 1)) := by
    rw [Finset.sum_congr rfl (fun x hx => hterm1 x (Finset.mem_range.mp hx)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_cast
  have h2 : ∑ x ∈ Finset.range (n ^ 2), counterQ n (n ^ 2 + x) / (1 - counterQ n (n ^ 2 + x))
      = (n ^ 2 : ℝ) * (-1 / ((n : ℝ) + 1)) := by
    rw [Finset.sum_congr rfl (fun x hx => hterm2 x),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_cast
  rw [h1, h2]
  have hden : ((n : ℝ) ^ 2 - 1) ≠ 0 := by nlinarith
  field_simp
  ring

/-- The full product of the counterexample family. -/
private theorem counter_prod (n : ℕ) (hn : 1 ≤ n) :
    ∏ i : Fin (2 * n ^ 2), (1 - counterP n i) = (1 - 1 / (n : ℝ) ^ 2) ^ (n ^ 2) := by
  have hEq : (∏ i : Fin (2 * n ^ 2), (1 - counterP n i))
      = ∏ i ∈ Finset.range (2 * n ^ 2), (1 - counterQ n i) :=
    Fin.prod_univ_eq_prod_range (fun i => 1 - counterQ n i) (2 * n ^ 2)
  rw [hEq]
  have hsplit : (2 * n ^ 2) = n ^ 2 + n ^ 2 := by ring
  rw [hsplit, Finset.prod_range_add]
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnne : (n : ℝ) ≠ 0 := hnR.ne'
  have h1 : ∏ x ∈ Finset.range (n ^ 2), (1 - counterQ n x) = (1 - 1 / (n : ℝ)) ^ (n ^ 2) := by
    rw [Finset.prod_congr rfl (fun x hx => by
      have hlt : x < n ^ 2 := Finset.mem_range.mp hx
      show 1 - (if x < n ^ 2 then (1:ℝ)/(n:ℝ) else -1/(n:ℝ)) = 1 - 1 / (n : ℝ)
      rw [ite_eq_left hlt])]
    rw [Finset.prod_const, Finset.card_range]
  have h2 : ∏ x ∈ Finset.range (n ^ 2), (1 - counterQ n (n ^ 2 + x))
      = (1 + 1 / (n : ℝ)) ^ (n ^ 2) := by
    rw [Finset.prod_congr rfl (fun x hx => by
      have hge : ¬ (n ^ 2 + x < n ^ 2) := by omega
      show 1 - (if n ^ 2 + x < n ^ 2 then (1:ℝ)/(n:ℝ) else -1/(n:ℝ)) = 1 + 1 / (n : ℝ)
      rw [ite_eq_right hge]
      ring)]
    rw [Finset.prod_const, Finset.card_range]
  rw [h1, h2, ← mul_pow]
  congr 1
  field_simp
  ring

/-- Closed form for the counterexample mass at `j = 1`. -/
private theorem counter_mass (n : ℕ) (hn : 2 ≤ n) :
    ∑ A ∈ Finset.univ.powersetCard 1,
      (∏ i ∈ A, counterP n i) * (∏ i ∈ Finset.univ \ A, (1 - counterP n i))
      = (1 - 1 / (n : ℝ) ^ 2) ^ (n ^ 2) * (2 * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) := by
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1:ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hne : ∀ i : Fin (2 * n ^ 2), (1:ℝ) - counterP n i ≠ 0 := by
    intro i
    by_cases hlt : (i : ℕ) < n ^ 2
    · show 1 - (if (i : ℕ) < n ^ 2 then (1:ℝ)/(n:ℝ) else -1/(n:ℝ)) ≠ 0
      rw [ite_eq_left hlt]
      have hEq : (1:ℝ) - 1/(n:ℝ) = ((n:ℝ) - 1)/(n:ℝ) := by field_simp
      rw [hEq]
      positivity
    · show 1 - (if (i : ℕ) < n ^ 2 then (1:ℝ)/(n:ℝ) else -1/(n:ℝ)) ≠ 0
      rw [ite_eq_right hlt]
      have hEq : (1:ℝ) - (-1/(n:ℝ)) = 1 + 1/(n:ℝ) := by ring
      rw [hEq]
      positivity
  rw [mass_one_eq hne, counter_prod n (by omega), counter_ratio_sum n hn]

/-- The counterexample mass at `j = 1` stays above `1 / 4`. -/
private theorem counter_mass_ge (n : ℕ) (hn : 2 ≤ n) :
    (1:ℝ) / 4 ≤ ∑ A ∈ Finset.univ.powersetCard 1,
      (∏ i ∈ A, counterP n i) * (∏ i ∈ Finset.univ \ A, (1 - counterP n i)) := by
  rw [counter_mass n hn]
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1:ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hLogBound : ∀ {x : ℝ}, |x| ≤ 1 / 2 → |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
    intro x hx
    have h1 : |x| < 1 := lt_of_le_of_lt hx (by norm_num)
    have h := Real.abs_log_sub_add_sum_range_le h1 1
    simp only [Finset.sum_range_one, zero_add, Nat.cast_zero, pow_one, div_one] at h
    have h2 : (0 : ℝ) < 1 - |x| := by linarith [abs_nonneg x]
    have h3 : |x| ^ 2 / (1 - |x|) ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ h2, sq_abs]
      nlinarith [sq_nonneg x, abs_nonneg x]
    have h4 : |Real.log (1 - x) + x| = |x + Real.log (1 - x)| := by rw [add_comm]
    rw [h4]
    exact h.trans h3
  have hx : (0:ℝ) < 1 / (n : ℝ) ^ 2 ∧ 1 / (n : ℝ) ^ 2 ≤ 1 / 2 := by
    refine ⟨by positivity, ?_⟩
    have h4 : (4:ℝ) ≤ (n : ℝ) ^ 2 := by
      have h2 : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h := pow_le_pow_left₀ (show (0:ℝ) ≤ 2 by norm_num) h2 2
      norm_num at h
      exact h
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (n : ℝ) ^ 2)]
    calc 1 / 2 * ((n : ℝ) ^ 2) = (n : ℝ) ^ 2 / 2 := by ring
      _ ≥ 4 / 2 := by linarith
      _ = 2 := by norm_num
      _ ≥ 1 := by norm_num
  have hlog : Real.log (1 - 1 / (n : ℝ) ^ 2) ≥ -2 * (1 / (n : ℝ) ^ 2) := by
    have hb := hLogBound (x := 1 / (n : ℝ) ^ 2) (by
      rw [abs_of_nonneg hx.1.le]; exact hx.2)
    have habs : |Real.log (1 - 1 / (n : ℝ) ^ 2) + 1 / (n : ℝ) ^ 2|
        ≤ 2 * (1 / (n : ℝ) ^ 2) ^ 2 := hb
    rw [abs_le] at habs
    have hsmall : 2 * (1 / (n : ℝ) ^ 2) ^ 2 ≤ 1 / (n : ℝ) ^ 2 := by
      have h1 : (1 / (n : ℝ) ^ 2) ≤ 1 / 2 := hx.2
      nlinarith [hx.1]
    linarith [habs.1, hsmall]
  have hProd : (1 - 1 / (n : ℝ) ^ 2) ^ (n ^ 2) ≥ Real.exp (-2) := by
    have hpos : (0:ℝ) < 1 - 1 / (n : ℝ) ^ 2 := by linarith [hx.1, hx.2]
    have hlogP : Real.log ((1 - 1 / (n : ℝ) ^ 2) ^ (n ^ 2)) ≥ -2 := by
      rw [Real.log_pow]
      have hcast : ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by norm_cast
      rw [hcast]
      have hmul : (n : ℝ) ^ 2 * Real.log (1 - 1 / (n : ℝ) ^ 2)
          ≥ (n : ℝ) ^ 2 * (-2 * (1 / (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      have hcalc : (n : ℝ) ^ 2 * (-2 * (1 / (n : ℝ) ^ 2)) = -2 := by
        field_simp
      linarith [hmul, hcalc]
    have hExp := Real.exp_le_exp.mpr hlogP
    rwa [Real.exp_log (by positivity : (0:ℝ) < (1 - 1 / (n : ℝ) ^ 2) ^ (n ^ 2))] at hExp
  have hfactor : (2:ℝ) ≤ 2 * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) := by
    rw [le_div_iff₀ (by nlinarith [hn1] : (0:ℝ) < (n : ℝ) ^ 2 - 1)]
    nlinarith
  have hexp2 : Real.exp 2 ≤ 8 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
    nlinarith [h1, Real.exp_pos 1]
  have hge : (1:ℝ)/4 ≤ 2 * Real.exp (-2) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    rw [le_div_iff₀ (Real.exp_pos 2)]
    linarith [hexp2]
  calc (1:ℝ)/4 ≤ 2 * Real.exp (-2) := hge
    _ = Real.exp (-2) * 2 := by ring
    _ ≤ (1 - 1 / (n : ℝ) ^ 2) ^ (n ^ 2) * (2 * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) :=
        mul_le_mul hProd hfactor (by norm_num)
          (pow_nonneg (by linarith [hx.1, hx.2] : (0:ℝ) ≤ 1 - 1 / (n : ℝ) ^ 2) _)

/-- The counterexample family satisfies the v1 hypotheses with `λ = 0`
(row sums are `0`, and the entries are `≤ 1 / n`), but its mass at
`j = 1` does not converge to the Poisson mass `0`: it stays above `1 / 4`. -/
private theorem counter_not_tendsto :
    ¬ Filter.Tendsto (fun n => ∑ A ∈ Finset.univ.powersetCard 1,
      (∏ i ∈ A, counterP n i) * (∏ i ∈ Finset.univ \ A, (1 - counterP n i)))
      atTop (𝓝 0) := by
  intro hT
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hT (1/4) (by norm_num)
  obtain ⟨n, hnN, hn2⟩ : ∃ n, N ≤ n ∧ 2 ≤ n := ⟨max N 2, le_max_left _ _, le_max_right _ _⟩
  have hge := counter_mass_ge n hn2
  have hlt := hN n hnN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith : (0:ℝ) ≤
    ∑ A ∈ Finset.univ.powersetCard 1,
      (∏ i ∈ A, counterP n i) * (∏ i ∈ Finset.univ \ A, (1 - counterP n i)))] at hlt
  linarith

/-- The v1 hypotheses for the counterexample family are satisfied with
`λ = 0`: row sums are `0` (hence tend to `0`) and every entry is `< ε`
eventually. -/
example : (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ i : Fin (2 * n ^ 2), counterP n i < ε)
    ∧ Filter.Tendsto (fun n => ∑ i : Fin (2 * n ^ 2), counterP n i) atTop (𝓝 ((0 : ℝ≥0) : ℝ)) := by
  constructor
  · intro ε hε
    have hEv : ∀ᶠ (n : ℕ) in atTop, (1:ℝ) / (n : ℝ) < ε := by
      have hT : Filter.Tendsto (fun n : ℕ => (1:ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
      exact hT.eventually (Iio_mem_nhds hε)
    filter_upwards [hEv] with n hn i
    by_cases hlt : (i : ℕ) < n ^ 2
    · show (if (i : ℕ) < n ^ 2 then (1:ℝ)/(n:ℝ) else -1/(n:ℝ)) < ε
      rw [ite_eq_left hlt]
      exact hn
    · show (if (i : ℕ) < n ^ 2 then (1:ℝ)/(n:ℝ) else -1/(n:ℝ)) < ε
      rw [ite_eq_right hlt]
      have : (-1:ℝ)/(n:ℝ) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg (by norm_num)
        positivity
      linarith
  · simp only [NNReal.coe_zero]
    rw [show (fun n => ∑ i : Fin (2 * n ^ 2), counterP n i) = fun _ => 0 from
      funext fun n => counter_sum n]
    exact tendsto_const_nhds

#print axioms ProbabilityTheory.elem_symm_poly_tendsto_poisson
#print axioms MathlibExtTest.Probability.PoissonConvergenceCore.counter_not_tendsto

end MathlibExtTest.Probability.PoissonConvergenceCore
