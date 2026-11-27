/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_PlaceEvaluation.lean`,
`Theorems/Thm_AlgebraicCurve_Place_ord_algebraMap.lean`,
`P2M/Sol/S_AlgebraicCurve_Place_ord_algebraMap.lean`
and
`P2M/Sol/S_AlgebraicCurve_Annulus_ord_residue_add_nonneg_and_abv_le_one_of_
isAttached_both_ends.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluation

/-!
# Evaluation at rational places: arithmetic and orders

This file adds to the evaluation `AlgebraicCurve.Place.evalAt` at a rational place `v` of a
function field `F` over `K`. On the valuation subring of `v`, evaluation is the identity on
constants, respects differences, powers and finite products, and gives the value in the sense of
the relational `AlgebraicCurve.Place.HasValueAt`. Every constant has order zero at every place,
and a regular function with a nonzero value at a rational place has order zero there.

## Main results

* `AlgebraicCurve.Place.evalAt_algebraMap`: evaluation at a rational place is the identity on
  constants.
* `AlgebraicCurve.Place.ord_algebraMap`: every constant has order zero at every place.
* `AlgebraicCurve.Place.ord_eq_zero_of_evalAt_ne_zero`: a regular function with a nonzero value
  at a rational place has order zero there.
-/

@[expose] public section

open IsLocalRing WithZero

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

theorem hasValueAt_evalAt (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasValueAt f (v.evalAt hv f) :=
  (v.hasValueAt_iff_residue hf _).mpr (v.algebraMap_evalAt hv hf).symm

/-- Evaluation at a rational place is the identity on constants. -/
theorem evalAt_algebraMap (hv : v.IsRational) (a : K) : v.evalAt hv (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem hv (v.algebraMap_mem a)]
  exact v.residueInv_algebraMap hv a

theorem evalAt_sub (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt hv (f - g) = v.evalAt hv f - v.evalAt hv g := by
  apply (algebraMap K v.ResidueField).injective
  rw [map_sub, v.algebraMap_evalAt hv (sub_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

theorem evalAt_pow (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt hv (f ^ n) = v.evalAt hv f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, v.evalAt_mul hv (pow_mem hf n) hf, ih]

theorem evalAt_prod (hv : v.IsRational) {ι : Type*} (S : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ S, f i ∈ v.toValuationSubring) :
    v.evalAt hv (∏ i ∈ S, f i) = ∏ i ∈ S, v.evalAt hv (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    have hfi : f i ∈ v.toValuationSubring := hf i (Finset.mem_insert_self _ _)
    have hS : ∀ j ∈ S, f j ∈ v.toValuationSubring :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      v.evalAt_mul hv hfi (prod_mem hS), ih hS]

/-- Every constant has order zero at every place (for `0` by the convention `ord 0 = 0`). -/
theorem ord_algebraMap (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, v.ord_zero]
  · have hu : IsUnit (algebraMap K v.toValuationSubring c) :=
      (isUnit_iff_ne_zero.mpr hc).map _
    have h1 : v.adicValuation (algebraMap K F c) = 1 := by
      rw [← v.coe_algebraMap]
      exact (v.adicValuation_coe_eq_one_iff _).mpr hu
    simp only [ord, h1, log_one, neg_zero]

/-- A regular function with a nonzero value at a rational place has order zero there. -/
theorem ord_eq_zero_of_evalAt_ne_zero (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt hv f ≠ 0) : v.ord f = 0 := by
  by_contra hne
  have hpos : 0 < v.ord f := lt_of_le_of_ne (v.ord_nonneg_of_mem hf) (Ne.symm hne)
  apply h
  have hnu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    rintro ⟨u, hu⟩
    have h0 : v.ord f = 0 := by
      have := v.ord_coe_unit u
      rwa [hu] at this
    omega
  have hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [v.evalAt_of_mem hv hf, (IsLocalRing.residue_eq_zero_iff _).2 hmax,
    ← map_zero (algebraMap K _), v.residueInv_algebraMap hv]

end Place

end AlgebraicCurve
