/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Wright's island model: equilibrium `F_ST`

In Wright's (infinite) island model each deme consists of `N` diploid individuals, i.e.
`M = 2N` gene copies, and in every generation a fraction `m` of the gene copies of a deme are
replaced by migrants drawn from an infinite pool of unrelated genes. Let `F` be the probability
that two distinct gene copies sampled in the same deme are identical by descent (relative to the
migrant pool; this is Wright's `F_ST`). Looking back one generation, the two copies are both
non-migrants with probability `(1 - m) ^ 2`, and then they descend from the same parental copy
with probability `1 / M` or from two distinct parental copies, identical by descent with
probability `F`, otherwise. This gives the recursion (time in generations)

  `F' = (1 - m) ^ 2 * (1 / M + (1 - 1 / M) * F)` (`islandStep`).

For `M ≥ 1` and `0 ≤ m ≤ 1` (the domain of the model; the definitions are total and carry no
meaning outside it) the recursion is a contraction with factor `(1 - m) ^ 2 (1 - 1 / M) < 1`,
and its unique fixed point is

  `F* = (1 - m) ^ 2 / (M - (M - 1) (1 - m) ^ 2)` (`islandEquilibrium`).

In the regime of many large demes exchanging few migrants, `N → ∞` with `4 N m = κ` fixed,
`F* → 1 / (1 + κ)`: Wright's classical `F_ST = 1 / (1 + 4 N m)`, stated here as an exact
limit.

## Main results

* `islandStep_islandEquilibrium`, `eq_islandEquilibrium_of_islandStep_eq`: `F*` is the unique
  fixed point of the recursion.
* `islandStep_iterate_sub`: `F_t - F* = ((1 - m) ^ 2 (1 - 1 / M)) ^ t (F_0 - F*)`.
* `tendsto_islandStep_iterate`: `F_t → F*` from every initial value.
* `islandEquilibrium_mem_Icc`, `islandEquilibrium_mem_Ico`, `islandEquilibrium_zero_right`:
  `F* ∈ [0, 1]`, `F* < 1` when `m > 0`, and `F* = 1` for isolated demes (`m = 0`).
* `tendsto_islandEquilibrium`: with `M = 2N` and `m = κ / (4N)`, `F* → 1 / (1 + κ)` as
  `N → ∞`.

## References

* S. Wright, *Evolution in Mendelian populations*, Genetics 16 (1931), 97–159.
* J. Wakeley, *Coalescent Theory: An Introduction*, Roberts & Company (2009).
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace MathlibExt.Biology.PopulationGenetics.IslandModel

/-- One generation of Wright's island-model identity-by-descent recursion for a deme of `M`
gene copies (`M = 2N` for `N` diploids) receiving a fraction `m` of migrants from an infinite
pool: `F' = (1 - m) ^ 2 * (1 / M + (1 - 1 / M) * F)`. Meaningful for `M ≥ 1` and
`0 ≤ m ≤ 1` (at `M = 0` Lean's `1 / 0 = 0` gives a junk value). -/
noncomputable def islandStep (M : ℕ) (m F : ℝ) : ℝ :=
  (1 - m) ^ 2 * (1 / M + (1 - 1 / M) * F)

/-- The equilibrium identity-by-descent probability (Wright's `F_ST`) of the island model:
`F* = (1 - m) ^ 2 / (M - (M - 1) (1 - m) ^ 2)`. Meaningful for `M ≥ 1` and `0 ≤ m ≤ 1`, where
the denominator is positive (`islandEquilibrium_denom_pos`). -/
noncomputable def islandEquilibrium (M : ℕ) (m : ℝ) : ℝ :=
  (1 - m) ^ 2 / (M - (M - 1) * (1 - m) ^ 2)

/-- For `M ≥ 1` and `0 ≤ m ≤ 1`, the per-generation contraction factor
`(1 - m) ^ 2 (1 - 1 / M)` lies in `[0, 1)`. -/
theorem islandFactor_mem_Ico {M : ℕ} (hM : 0 < M) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    (1 - m) ^ 2 * (1 - 1 / M) ∈ Ico (0 : ℝ) 1 := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 : 0 ≤ 1 - 1 / (M : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hM'
  have h2 : 1 - 1 / (M : ℝ) < 1 := by
    have : 0 < 1 / (M : ℝ) := by positivity
    linarith
  have h3 : (1 - m) ^ 2 ≤ 1 := by nlinarith [hm.1, hm.2]
  refine ⟨by positivity, ?_⟩
  calc (1 - m) ^ 2 * (1 - 1 / M) ≤ 1 * (1 - 1 / M) :=
        mul_le_mul_of_nonneg_right h3 h1
    _ < 1 := by rw [one_mul]; exact h2

/-- The denominator `M - (M - 1) (1 - m) ^ 2` of the equilibrium is positive (at least `1`) for
`M ≥ 1` and `0 ≤ m ≤ 1`. -/
theorem islandEquilibrium_denom_pos {M : ℕ} (hM : 0 < M) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    0 < (M : ℝ) - (M - 1) * (1 - m) ^ 2 := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h3 : (1 - m) ^ 2 ≤ 1 := by nlinarith [hm.1, hm.2]
  nlinarith [sq_nonneg (1 - m)]

/-- `F*` is a fixed point of the island-model recursion. -/
theorem islandStep_islandEquilibrium {M : ℕ} (hM : 0 < M) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    islandStep M m (islandEquilibrium M m) = islandEquilibrium M m := by
  have hD := (islandEquilibrium_denom_pos hM hm).ne'
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  unfold islandStep islandEquilibrium
  set D := (M : ℝ) - (M - 1) * (1 - m) ^ 2 with hDdef
  have key : 1 / (M : ℝ) + (1 - 1 / M) * ((1 - m) ^ 2 / D) = 1 / D := by
    field_simp
    rw [hDdef]
    ring
  rw [key, mul_one_div]

/-- `F*` is the only fixed point of the island-model recursion. -/
theorem eq_islandEquilibrium_of_islandStep_eq {M : ℕ} (hM : 0 < M) {m : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) {F : ℝ} (hF : islandStep M m F = F) : F = islandEquilibrium M m := by
  have hD := (islandEquilibrium_denom_pos hM hm).ne'
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  unfold islandStep at hF
  unfold islandEquilibrium
  rw [eq_div_iff hD]
  field_simp at hF
  linear_combination -hF

/-- **Geometric approach to equilibrium.** After `t` generations,
`F_t - F* = ((1 - m) ^ 2 (1 - 1 / M)) ^ t (F_0 - F*)`. -/
theorem islandStep_iterate_sub {M : ℕ} (hM : 0 < M) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (F₀ : ℝ) (t : ℕ) :
    (islandStep M m)^[t] F₀ - islandEquilibrium M m =
      ((1 - m) ^ 2 * (1 - 1 / M)) ^ t * (F₀ - islandEquilibrium M m) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', pow_succ, mul_comm (_ ^ t), mul_assoc, ← ih]
    conv_lhs => rw [← islandStep_islandEquilibrium hM hm]
    unfold islandStep
    ring

/-- **Convergence to equilibrium.** For `M ≥ 1` and `0 ≤ m ≤ 1`, the island-model recursion
converges to `F*` from every initial value `F₀`. -/
theorem tendsto_islandStep_iterate {M : ℕ} (hM : 0 < M) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (F₀ : ℝ) :
    Tendsto (fun t => (islandStep M m)^[t] F₀) atTop (𝓝 (islandEquilibrium M m)) := by
  have hc := islandFactor_mem_Ico hM hm
  have h : Tendsto (fun t => ((1 - m) ^ 2 * (1 - 1 / M)) ^ t * (F₀ - islandEquilibrium M m)
      + islandEquilibrium M m) atTop (𝓝 (0 * (F₀ - islandEquilibrium M m)
        + islandEquilibrium M m)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hc.1 hc.2).mul_const _).add_const _
  rw [zero_mul, zero_add] at h
  refine h.congr fun t => ?_
  rw [← islandStep_iterate_sub hM hm]
  ring

/-- The equilibrium identity-by-descent probability lies in `[0, 1]`. -/
theorem islandEquilibrium_mem_Icc {M : ℕ} (hM : 0 < M) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    islandEquilibrium M m ∈ Icc (0 : ℝ) 1 := by
  have hD := islandEquilibrium_denom_pos hM hm
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h3 : (1 - m) ^ 2 ≤ 1 := by nlinarith [hm.1, hm.2]
  refine ⟨div_nonneg (sq_nonneg _) hD.le, (div_le_one hD).2 ?_⟩
  nlinarith

/-- With migration (`0 < m ≤ 1`) the equilibrium identity-by-descent probability lies in
`[0, 1)`. -/
theorem islandEquilibrium_mem_Ico {M : ℕ} (hM : 0 < M) {m : ℝ} (hm : m ∈ Ioc (0 : ℝ) 1) :
    islandEquilibrium M m ∈ Ico (0 : ℝ) 1 := by
  have hD := islandEquilibrium_denom_pos hM (Ioc_subset_Icc_self hm)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h3 : (1 - m) ^ 2 < 1 := by nlinarith [hm.1, hm.2]
  refine ⟨div_nonneg (sq_nonneg _) hD.le, (div_lt_one hD).2 ?_⟩
  nlinarith

/-- Isolated demes (`m = 0`): the equilibrium is complete identity by descent, `F* = 1`. -/
@[simp]
theorem islandEquilibrium_zero_right (M : ℕ) : islandEquilibrium M 0 = 1 := by
  simp [islandEquilibrium]

/-- **Wright's `F_ST = 1 / (1 + 4 N m)` (Wright 1931).** For demes of `N` diploids (`M = 2N`
gene copies) and migration fraction `m = κ / (4N)`, so that `4 N m = κ` is held fixed, the
equilibrium `F*` tends to `1 / (1 + κ)` as `N → ∞`. -/
theorem tendsto_islandEquilibrium {κ : ℝ} (hκ : 0 ≤ κ) :
    Tendsto (fun N : ℕ => islandEquilibrium (2 * N) (κ / (4 * N))) atTop
      (𝓝 (1 / (1 + κ))) := by
  have hm : Tendsto (fun N : ℕ => κ / (4 * (N : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (κ / 4))
    refine this.congr fun N => ?_
    ring
  have hq : Tendsto (fun N : ℕ => κ ^ 2 / (8 * (N : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (κ ^ 2 / 8))
    refine this.congr fun N => ?_
    ring
  have hnum : Tendsto (fun N : ℕ => (1 - κ / (4 * (N : ℝ))) ^ 2) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hm).pow 2
  have hden : Tendsto (fun N : ℕ => κ - κ ^ 2 / (8 * (N : ℝ)) + (1 - κ / (4 * (N : ℝ))) ^ 2)
      atTop (𝓝 (κ - 0 + 1)) :=
    ((tendsto_const_nhds.sub hq).add hnum)
  rw [sub_zero, add_comm] at hden
  have hlim := hnum.div hden (by linarith)
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
  simp only [Pi.div_apply, islandEquilibrium]
  congr 1
  push_cast
  field_simp
  ring

end MathlibExt.Biology.PopulationGenetics.IslandModel
