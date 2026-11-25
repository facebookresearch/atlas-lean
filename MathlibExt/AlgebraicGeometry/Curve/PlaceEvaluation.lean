/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_PlaceEvaluation.lean`,
`Theorems/Thm_AlgebraicCurve_Place_ord_algebraMap.lean`
and
`P2M/Sol/S_AlgebraicCurve_Place_ord_algebraMap.lean`
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

public import MathlibExt.AlgebraicGeometry.Curve.ChartDichotomy
public import MathlibExt.AlgebraicGeometry.Curve.Place

/-!
# Evaluating functions at a rational place

For a place `v` of a function field `F / K`, `v.IsRational` says that the residue field of `v`
is `K` itself (the structure map `K → v.ResidueField` is surjective). The value `v.evalAt f` of a
function `f` regular at `v` is the element of `K` whose image is the residue of `f`; outside the
valuation subring it is the junk value `0`. On regular functions at a rational place the
evaluation is additive and multiplicative and is the identity on constants.

We also record that nonzero constants have order zero at every place (`Place.ord_algebraMap`).
-/

@[expose] public section

noncomputable section

open IsLocalRing WithZero

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

/-- A place is rational when its residue field is the base field: the structure map
`K → v.ResidueField` is surjective. -/
def IsRational : Prop := Function.Surjective (algebraMap K v.ResidueField)

theorem algebraMap_residueField_injective :
    Function.Injective (algebraMap K v.ResidueField) :=
  (algebraMap K v.ResidueField).injective

/-- A one-sided inverse of the structure map `K → v.ResidueField`; it is a two-sided inverse
when `v` is rational. -/
def residueInv : v.ResidueField → K :=
  Function.invFun (algebraMap K v.ResidueField)

theorem algebraMap_residueInv (hv : v.IsRational) (x : v.ResidueField) :
    algebraMap K v.ResidueField (v.residueInv x) = x :=
  Function.invFun_eq (hv x)

theorem residueInv_algebraMap (a : K) : v.residueInv (algebraMap K v.ResidueField a) = a :=
  Function.leftInverse_invFun v.algebraMap_residueField_injective a

open Classical in
/-- The value of a function at a place: the residue of `f` pulled back to `K` when `f` lies in
the valuation subring of `v`, and `0` otherwise. It is meaningful at rational places. -/
def evalAt (f : F) : K :=
  if hf : f ∈ v.toValuationSubring then
    v.residueInv (residue v.toValuationSubring ⟨f, hf⟩)
  else 0

theorem evalAt_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = v.residueInv (residue v.toValuationSubring ⟨f, hf⟩) := by
  simp [evalAt, hf]

theorem algebraMap_evalAt (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    algebraMap K v.ResidueField (v.evalAt f)
      = residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [v.evalAt_of_mem hf]
  exact v.algebraMap_residueInv hv _

@[simp]
theorem evalAt_one : v.evalAt (1 : F) = 1 := by
  rw [v.evalAt_of_mem (one_mem _)]
  have h1 : (⟨(1 : F), one_mem _⟩ : v.toValuationSubring) = 1 := rfl
  rw [h1, map_one, ← map_one (algebraMap K v.ResidueField), v.residueInv_algebraMap]

/-- Evaluation is the identity on constants. -/
theorem evalAt_algebraMap (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

theorem evalAt_mul (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

theorem evalAt_sub (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

theorem evalAt_pow (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, v.evalAt_mul hv (pow_mem hf n) hf, ih]

theorem evalAt_prod (hv : v.IsRational) {ι : Type*} (S : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ S, f i ∈ v.toValuationSubring) :
    v.evalAt (∏ i ∈ S, f i) = ∏ i ∈ S, v.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    have hfi : f i ∈ v.toValuationSubring := hf i (Finset.mem_insert_self _ _)
    have hS : ∀ j ∈ S, f j ∈ v.toValuationSubring :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      v.evalAt_mul hv hfi (prod_mem hS), ih hS]

/-- Nonzero constants have order zero at every place. -/
theorem ord_algebraMap (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, v.ord_zero]
  · have hu : IsUnit (algebraMap K v.toValuationSubring c) :=
      (isUnit_iff_ne_zero.mpr hc).map _
    have h1 : v.adicValuation (algebraMap K F c) = 1 := by
      rw [← v.coe_algebraMap]
      exact (v.adicValuation_coe_eq_one_iff _).mpr hu
    simp only [ord, h1, log_one, neg_zero]

/-- A regular function with nonzero value at a place has order zero there. -/
theorem ord_eq_zero_of_evalAt_ne_zero {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
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
  rw [v.evalAt_of_mem hf, (IsLocalRing.residue_eq_zero_iff _).2 hmax,
    ← map_zero (algebraMap K _), v.residueInv_algebraMap]

end Place

end AlgebraicCurve
