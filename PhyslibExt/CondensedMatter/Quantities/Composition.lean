/-
Copyright (c) Meta Platforms, Inc. and affiliates.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

/-!
# MS01 quantities: composition simplex maps and dimension kernels

Arrhenius log identities, weight/mole-fraction bijections, and the
dimension-kernel dimension formula for the ATLAS MS01 pilot slice.

## i. Overview

This module proves the pure-mathematical cores needed by the MS01 roadmap slice
(quantities, units, dimensional analysis, composition conventions): the Arrhenius
log identity in natural and base-10 logarithms, the mutually inverse
weight-fraction/mole-fraction conversions on the open composition simplex
(including the wt%/at% percent forms), and the rank-nullity dimension formula
for the kernel of a rational dimension matrix.

Reuse decision: SI quantities as value-plus-dimension-vector are provided by the
Physlib `ISQDimensionBase` / `WithDim` interface (the MF01/CH01 Physlib-based ISQ
interface). This file deliberately does NOT create a parallel dimension-vector
library; the Physlib `WithDim` wrapping is stated here as the reuse decision
(the proving sandbox has Mathlib only, so the wrapping itself is neither
imported nor proved here).

Reuse-verified against Mathlib/Physlib/ATLAS main; no ATLAS-50 prerequisite PR
dependency: this file imports only Mathlib and ATLAS main as it stands. It does
NOT import any other ATLAS-50 module PR, and it does not depend on
CH01/CH03/MF03/MF05 or any other roadmap module's new API.

## ii. Key results

* `arrhenius_log`: under the Arrhenius model
  `y = A * Real.exp (-E / (R * T))` with `y, A, T, R` positive,
  `Real.log (y / y_ref) = Real.log (A / y_ref) - E / (R * T)`.
* `arrhenius_log10`: the base-10 form,
  `Real.logb 10 (y / y_ref)
    = Real.logb 10 (A / y_ref) - E / (R * T * Real.log 10)`.
* `moleFrac_wtFrac` / `wtFrac_moleFrac`: `wtFrac` and `moleFracOfWt` are
  mutually inverse bijections of the open simplex for positive molar masses.
* `wtPct_atPct`: the wt%/at% percent forms convert by the same mutually inverse
  maps scaled by 100.
* `dim_kernel_finrank`: for `D : Matrix (Fin m) (Fin n) ℚ`,
  `Module.finrank ℚ (LinearMap.ker D.toLin') = n - D.rank`.

## iii. Table of contents

* a. Arrhenius coordinates: `arrhenius_log`, `arrhenius_log10`.
* b. Composition simplex maps: `wtFrac`, `moleFracOfWt`, `moleFrac_wtFrac`,
  `wtFrac_moleFrac`, `wtPct`, `atPct`, `wtPct_atPct`.
* c. Dimension kernels: `dim_kernel_finrank`.

## iv. References

* Roadmap module MS01 (materials, core): quantities, units, dimensional
  analysis, composition conventions.
* MF01/CH01 Physlib-based ISQ interface (`ISQDimensionBase` / `WithDim`).
-/

@[expose] public section

/-! ## a. Arrhenius coordinates -/

/-- Arrhenius log identity (natural log): under `y = A * exp(-E / (R * T))`
with `y, A, T, R` positive, the log of `y / y_ref` splits into the log
prefactor ratio minus `E / (R * T)`. Mathematical consequence (MC) of the
stated model; no empirical parameter value is asserted. -/
lemma arrhenius_log {y y_ref A T R E : ℝ} (hy_ref : 0 < y_ref) (hA : 0 < A)
    (_hy : 0 < y) (_hT : 0 < T) (_hR : 0 < R)
    (h : y = A * Real.exp (-E / (R * T))) :
    Real.log (y / y_ref) = Real.log (A / y_ref) - E / (R * T) := by
  have hexp : Real.exp (-E / (R * T)) ≠ 0 := Real.exp_ne_zero _
  have hAmul : A * Real.exp (-E / (R * T)) ≠ 0 :=
    mul_ne_zero (ne_of_gt hA) hexp
  rw [h, Real.log_div hAmul (ne_of_gt hy_ref),
    Real.log_mul (ne_of_gt hA) hexp, Real.log_exp,
    Real.log_div (ne_of_gt hA) (ne_of_gt hy_ref)]
  ring

/-- Arrhenius log identity (base 10): the same statement as `arrhenius_log`
with `Real.logb 10`, converting via `Real.log 10`. Proved from
`arrhenius_log` through `Real.log_div_log`
(`Real.log x / Real.log b = Real.logb b x`). -/
lemma arrhenius_log10 {y y_ref A T R E : ℝ} (hy_ref : 0 < y_ref) (hA : 0 < A)
    (hy : 0 < y) (hT : 0 < T) (hR : 0 < R)
    (h : y = A * Real.exp (-E / (R * T))) :
    Real.logb 10 (y / y_ref)
      = Real.logb 10 (A / y_ref) - E / (R * T * Real.log 10) := by
  have h1 := arrhenius_log hy_ref hA hy hT hR h
  rw [← Real.log_div_log, ← Real.log_div_log, h1, sub_div, div_div]

/-! ## b. Composition simplex maps -/

/-- Weight fraction from mole fractions: `wtFrac M x i = M i * x i / ∑ j,
M j * x j`, for molar masses `M` and mole fractions `x` on the simplex. -/
noncomputable def wtFrac {ι : Type*} [Fintype ι] (M x : ι → ℝ) : ι → ℝ :=
  fun i => M i * x i / ∑ j, M j * x j

/-- Mole fraction from weight fractions: `moleFracOfWt M w i
= (w i / M i) / ∑ j, (w j / M j)`, for molar masses `M` and weight
fractions `w` on the simplex. -/
noncomputable def moleFracOfWt {ι : Type*} [Fintype ι] (M w : ι → ℝ) : ι → ℝ :=
  fun i => (w i / M i) / ∑ j, (w j / M j)

/-- Mole-to-weight-to-mole round trip: on the open simplex (`∀ i, 0 < x i`,
`∑ i, x i = 1`) with positive molar masses, `moleFracOfWt M` inverts
`wtFrac M`. Mathematical consequence (MC) within the stated model. -/
lemma moleFrac_wtFrac {ι : Type*} [Fintype ι] [Nonempty ι] {M x : ι → ℝ}
    (hM : ∀ i, 0 < M i) (hx : ∀ i, 0 < x i) (hsum : ∑ i, x i = 1) :
    moleFracOfWt M (wtFrac M x) = x := by
  have hS : 0 < ∑ j, M j * x j := by
    apply Finset.sum_pos
    · intro i _
      exact mul_pos (hM i) (hx i)
    · exact Finset.univ_nonempty
  have hSne : (∑ j, M j * x j) ≠ 0 := ne_of_gt hS
  have hT : (∑ j, ((M j * x j / ∑ k, M k * x k) / M j))
      = 1 / ∑ j, M j * x j := by
    have hpt : ∀ j, ((M j * x j / ∑ k, M k * x k) / M j)
        = x j / ∑ k, M k * x k := by
      intro j
      have hMj : M j ≠ 0 := ne_of_gt (hM j)
      field_simp
    simp only [hpt]
    rw [← Finset.sum_div, hsum]
  funext i
  simp only [moleFracOfWt, wtFrac]
  rw [hT]
  have hMi : M i ≠ 0 := ne_of_gt (hM i)
  field_simp

/-- Weight-to-mole-to-weight round trip: on the open simplex (`∀ i, 0 < w i`,
`∑ i, w i = 1`) with positive molar masses, `wtFrac M` inverts
`moleFracOfWt M`. Together with `moleFrac_wtFrac`, the two maps are mutually
inverse bijections of the open simplex. -/
lemma wtFrac_moleFrac {ι : Type*} [Fintype ι] [Nonempty ι] {M w : ι → ℝ}
    (hM : ∀ i, 0 < M i) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) :
    wtFrac M (moleFracOfWt M w) = w := by
  have hT : 0 < ∑ j, (w j / M j) := by
    apply Finset.sum_pos
    · intro i _
      exact div_pos (hw i) (hM i)
    · exact Finset.univ_nonempty
  have hTne : (∑ j, (w j / M j)) ≠ 0 := ne_of_gt hT
  have hS : (∑ j, M j * ((w j / M j) / ∑ k, (w k / M k)))
      = 1 / ∑ j, (w j / M j) := by
    have hpt : ∀ j, M j * ((w j / M j) / ∑ k, (w k / M k))
        = w j / ∑ k, (w k / M k) := by
      intro j
      have hMj : M j ≠ 0 := ne_of_gt (hM j)
      field_simp
    simp only [hpt]
    rw [← Finset.sum_div, hsum]
  funext i
  simp only [wtFrac, moleFracOfWt]
  rw [hS]
  have hMi : M i ≠ 0 := ne_of_gt (hM i)
  field_simp

/-- Weight percent: `100 * wtFrac M x i`. -/
noncomputable def wtPct {ι : Type*} [Fintype ι] (M x : ι → ℝ) : ι → ℝ :=
  fun i => 100 * wtFrac M x i

/-- Atomic percent (elemental case): `100 * x i` for mole fractions `x`. -/
noncomputable def atPct {ι : Type*} (x : ι → ℝ) : ι → ℝ :=
  fun i => 100 * x i

/-- wt%/at% conversion by the same mutually inverse maps scaled by 100:
normalizing a positive 100-sum vector to the simplex, converting, and scaling
back is the identity in both directions. Corollary of `wtFrac_moleFrac` and
`moleFrac_wtFrac` with the factor 100 carried through. -/
lemma wtPct_atPct {ι : Type*} [Fintype ι] [Nonempty ι] {M : ι → ℝ}
    (hM : ∀ i, 0 < M i) :
    (∀ {w : ι → ℝ}, (∀ i, 0 < w i) → ∑ i, w i = 100 →
      wtPct M (moleFracOfWt M (fun i => w i / 100)) = w)
    ∧ (∀ {x : ι → ℝ}, (∀ i, 0 < x i) → ∑ i, x i = 1 →
      atPct (moleFracOfWt M (wtFrac M x)) = atPct x) := by
  constructor
  · intro w hw hsum
    have h1 : ∀ i, 0 < w i / 100 := fun i => div_pos (hw i) (by norm_num)
    have h2 : ∑ i, w i / 100 = 1 := by
      rw [← Finset.sum_div, hsum]
      norm_num
    have h3 := wtFrac_moleFrac hM h1 h2
    funext i
    simp only [wtPct]
    rw [h3]
    ring
  · intro x hx hsum
    have h3 := moleFrac_wtFrac hM hx hsum
    rw [h3]

/-! ## c. Dimension kernels -/

/-- Dimension-kernel dimension formula (rank-nullity, MC): for a rational
dimension matrix `D`, the rational exponent vectors in the kernel — the
dimensionless-monomial exponents — form a space of dimension `n - D.rank`.
A full functional Buckingham Pi theorem requires additional scaling
hypotheses and is explicitly NOT claimed here. -/
lemma dim_kernel_finrank {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) :
    Module.finrank ℚ (LinearMap.ker D.toLin') = n - D.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker D.toLin'
  rw [Module.finrank_pi] at h
  rw [Fintype.card_fin] at h
  have hrank : D.rank = Module.finrank ℚ (LinearMap.range D.toLin') := by
    unfold Matrix.rank
    rw [Matrix.toLin'_apply']
  omega
