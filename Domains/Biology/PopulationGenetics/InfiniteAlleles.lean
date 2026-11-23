/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Homozygosity in the infinite-alleles model

Kimura and Crow's infinite-alleles model: a Wright–Fisher population of `M` gene copies (`M = 2N`
for `N` diploid individuals), in which every copy mutates with probability `u` per generation to
an allele never seen before. The homozygosity `F` is the probability that two distinct gene
copies drawn from the population carry the same allele. Two copies of the next generation
descend from the same parental copy with probability `1/M` and are then identical unless one of
them mutates; otherwise they descend from two distinct parental copies, which are identical with
probability `F`. A pair is identical only if neither copy mutates, so
`F' = (1 - u)² (1/M + (1 - 1/M) F)` (`homozygosityStep`).

The model needs two distinct gene copies, so its domain is `M ≥ 2` and `0 ≤ u ≤ 1`. The
theorems assume only `M ≥ 1`: for `M = 1` the identities still hold algebraically but have no
biological meaning.

## Main results

* `homozygosityStep_eq_self_iff`: for `0 < u ≤ 1` the unique fixed point is
  `F* = (1 - u)² / (M - (M - 1)(1 - u)²)` (`eqHomozygosity`).
* `tendsto_iterate_homozygosityStep`: `F_t → F*` from every initial value.
* `tendsto_eqHomozygosity`: with `M = 2N` and `u = θ/(4N)`, `F* → 1/(1 + θ)` as `N → ∞`;
  `tendsto_one_sub_eqHomozygosity`: the heterozygosity `H* = 1 - F* → θ/(1 + θ)`.

## References

* M. Kimura, J. F. Crow, *The number of alleles that can be maintained in a finite
  population*, Genetics 49 (1964), 725–738.
-/

@[expose] public section

open Filter Topology

namespace MathlibExt.Biology.PopulationGenetics.InfiniteAlleles

/-- One generation of drift and mutation in the infinite-alleles model with `M` gene copies and
mutation probability `u` per copy: `F' = (1 - u)² (1/M + (1 - 1/M) F)`. The model domain is
`2 ≤ M` (two distinct copies must exist) and `0 ≤ u ≤ 1`; the theorems below assume only
`1 ≤ M`, and `M = 1` is an algebraic extension with no biological meaning. For `M = 0` the
definition uses the junk value `1/0 = 0`. -/
noncomputable def homozygosityStep (M : ℕ) (u F : ℝ) : ℝ :=
  (1 - u) ^ 2 * (1 / M + (1 - 1 / M) * F)

/-- The equilibrium homozygosity `F* = (1 - u)² / (M - (M - 1)(1 - u)²)`. Biologically meaningful
for `2 ≤ M`; its denominator is positive for `1 ≤ M` and `0 < u ≤ 1`, the hypotheses of the
theorems below (`M = 1` being an algebraic extension). -/
noncomputable def eqHomozygosity (M : ℕ) (u : ℝ) : ℝ :=
  (1 - u) ^ 2 / (M - (M - 1) * (1 - u) ^ 2)

private theorem sq_one_sub_lt_one {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) : (1 - u) ^ 2 < 1 := by
  nlinarith

private theorem denom_pos {M : ℕ} (hM : 0 < M) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    0 < (M : ℝ) - (M - 1) * (1 - u) ^ 2 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hc := sq_one_sub_lt_one hu0 hu1
  nlinarith [sq_nonneg (1 - u)]

/-- The step contracts towards `F*` by the factor `(1 - u)² (1 - 1/M)`. -/
private theorem homozygosityStep_sub {M : ℕ} (hM : 0 < M) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (F : ℝ) : homozygosityStep M u F - eqHomozygosity M u =
      (1 - u) ^ 2 * (1 - 1 / M) * (F - eqHomozygosity M u) := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hd := (denom_pos hM hu0 hu1).ne'
  have hE : eqHomozygosity M u * (M - (M - 1) * (1 - u) ^ 2) = (1 - u) ^ 2 :=
    div_mul_cancel₀ _ hd
  have hinv : (M : ℝ) * (1 / M) = 1 := mul_one_div_cancel hM'
  unfold homozygosityStep
  linear_combination (-(1 / (M : ℝ))) * hE +
    (eqHomozygosity M u * (1 - (1 - u) ^ 2)) * hinv

/-- `F*` is a fixed point of the homozygosity recursion. -/
theorem homozygosityStep_eqHomozygosity {M : ℕ} (hM : 0 < M) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u ≤ 1) : homozygosityStep M u (eqHomozygosity M u) = eqHomozygosity M u := by
  have := homozygosityStep_sub hM hu0 hu1 (eqHomozygosity M u)
  rw [sub_self, mul_zero, sub_eq_zero] at this
  exact this

/-- For `0 < u ≤ 1`, `F*` is the unique fixed point of the homozygosity recursion. -/
theorem homozygosityStep_eq_self_iff {M : ℕ} (hM : 0 < M) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (F : ℝ) : homozygosityStep M u F = F ↔ F = eqHomozygosity M u := by
  refine ⟨fun h => ?_, fun h => h ▸ homozygosityStep_eqHomozygosity hM hu0 hu1⟩
  have hs := homozygosityStep_sub hM hu0 hu1 F
  rw [h] at hs
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hb : (1 - u) ^ 2 * (1 - 1 / M) < 1 := by
    have h1 : 1 - 1 / (M : ℝ) ≤ 1 := by
      have : 0 ≤ 1 / (M : ℝ) := by positivity
      linarith
    have h0 : 0 ≤ 1 - 1 / (M : ℝ) := by
      rw [sub_nonneg, div_le_one hM']
      exact_mod_cast hM
    calc (1 - u) ^ 2 * (1 - 1 / M) ≤ (1 - u) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ < 1 := by rw [mul_one]; exact sq_one_sub_lt_one hu0 hu1
  have : (1 - (1 - u) ^ 2 * (1 - 1 / M)) * (F - eqHomozygosity M u) = 0 := by
    linear_combination hs
  rcases mul_eq_zero.1 this with h0 | h0
  · linarith
  · linarith

/-- For `0 < u ≤ 1` the homozygosity converges to `F*` from every initial value `F₀`. -/
theorem tendsto_iterate_homozygosityStep {M : ℕ} (hM : 0 < M) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u ≤ 1) (F₀ : ℝ) :
    Tendsto (fun t : ℕ => (homozygosityStep M u)^[t] F₀) atTop (𝓝 (eqHomozygosity M u)) := by
  set b := (1 - u) ^ 2 * (1 - 1 / (M : ℝ))
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hiter : ∀ t : ℕ, (homozygosityStep M u)^[t] F₀ =
      eqHomozygosity M u + b ^ t * (F₀ - eqHomozygosity M u) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply', pow_succ]
      have := homozygosityStep_sub hM hu0 hu1 ((homozygosityStep M u)^[t] F₀)
      rw [ih] at this ⊢
      linear_combination this
  have h0 : 0 ≤ b := mul_nonneg (sq_nonneg _) (by
    rw [sub_nonneg, div_le_one hM']
    exact_mod_cast hM)
  have h1 : b < 1 := by
    have : 1 - 1 / (M : ℝ) ≤ 1 := by
      have : 0 ≤ 1 / (M : ℝ) := by positivity
      linarith
    calc b ≤ (1 - u) ^ 2 * 1 := mul_le_mul_of_nonneg_left this (sq_nonneg _)
      _ < 1 := by rw [mul_one]; exact sq_one_sub_lt_one hu0 hu1
  simp only [hiter]
  simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const
    (F₀ - eqHomozygosity M u)).const_add (eqHomozygosity M u)

/-- **Kimura–Crow limit**: with `M = 2N` gene copies and mutation probability `u = θ/(4N)`
(so that `θ = 4Nu`), the equilibrium homozygosity tends to `1/(1 + θ)` as `N → ∞`. -/
theorem tendsto_eqHomozygosity {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun N : ℕ => eqHomozygosity (2 * N) (θ / (4 * N))) atTop (𝓝 (1 / (1 + θ))) := by
  set g : ℝ → ℝ := fun ε => (1 - θ * ε / 4) ^ 2 / (θ - θ ^ 2 * ε / 8 + (1 - θ * ε / 4) ^ 2)
  have hc : ContinuousAt g 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num; linarith)
  have hg0 : g 0 = 1 / (1 + θ) := by simp only [g]; ring
  have h : Tendsto (fun N : ℕ => g (N : ℝ)⁻¹) atTop (𝓝 (1 / (1 + θ))) :=
    (hg0 ▸ hc.tendsto).comp tendsto_inv_atTop_nhds_zero_nat
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (N : ℝ) ≠ 0 := by positivity
  simp only [g, eqHomozygosity]
  push_cast
  have hinv : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hN'
  have hinv : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hN'
  congr 1
  · ring
  · linear_combination (-(θ - θ ^ 2 * (N : ℝ)⁻¹ / 8)) * hinv

/-- The equilibrium heterozygosity `H* = 1 - F*` tends to `θ/(1 + θ)` as `N → ∞` with
`M = 2N` and `u = θ/(4N)`. -/
theorem tendsto_one_sub_eqHomozygosity {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun N : ℕ => 1 - eqHomozygosity (2 * N) (θ / (4 * N))) atTop
      (𝓝 (θ / (1 + θ))) := by
  have h := (tendsto_eqHomozygosity hθ).const_sub 1
  convert h using 2
  field_simp
  ring

end MathlibExt.Biology.PopulationGenetics.InfiniteAlleles
