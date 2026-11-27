/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_PlaceEvaluation.lean`
and
`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
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
public import MathlibExt.AlgebraicGeometry.Curve.Divisor
public import MathlibExt.AlgebraicGeometry.Curve.LPolynomial

/-!
# Evaluation at rational places

Let `F` be a function field over a base field `K`. A place `v` of `F` is rational when the map
from `K` to the residue field of `v` is surjective, which happens exactly when `v` has degree one
over `K`. At a rational place, an element of the valuation subring of `v` has a value in `K`: the
element of `K` with the same residue. This file defines that value and the evaluation of a
function on a divisor supported on rational places, and states Weil reciprocity for such divisors.

## Main definitions

* `AlgebraicCurve.Place.IsRational`: the base field `K` surjects onto the residue field.
* `AlgebraicCurve.Place.residueEquiv`: at a rational place, the `K`-algebra isomorphism from `K`
  onto the residue field; `AlgebraicCurve.Place.residueInv` is its inverse map.
* `AlgebraicCurve.Place.evalAt`: the value in `K` of a function at a rational place, with the
  value `0` at a pole.
* `CurveDivisor.evalFun`: the product of `f(v) ^ D(v)` over the support of a divisor `D` of
  rational places.
* `AlgebraicCurve.WeilReciprocity`: the statement `f(div g) = g(div f)` for nonzero `f` and `g`
  with disjoint divisors supported on rational places.

## Main results

* `AlgebraicCurve.Place.isRational_iff_deg_eq_one`: a place is rational exactly when it has
  degree one.
* `AlgebraicCurve.Place.evalAt_add` and `AlgebraicCurve.Place.evalAt_mul`: on the valuation
  subring, evaluation at a rational place is additive and multiplicative.

## Implementation notes

The source defines `residueInv`, `evalAt` and `evalFun` at every place, through
`Function.invFun`. Here they take a proof that the place is rational, or that every place in the
support of the divisor is, so no choice is made at other places; at rational places the values
are the source's. `WeilReciprocity` keeps the source's hypotheses and passes its rationality
hypotheses on to `evalFun`.
-/

@[expose] public section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

/-- A place is rational when the base field `K` surjects onto its residue field. -/
def IsRational : Prop := Function.Surjective (algebraMap K v.ResidueField)

/-- At a rational place, the isomorphism of `K`-algebras from the base field `K` onto the residue
field. -/
noncomputable def residueEquiv (hv : v.IsRational) : K ≃ₐ[K] v.ResidueField :=
  AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField)
    ⟨(algebraMap K v.ResidueField).injective, hv⟩

@[simp]
theorem residueEquiv_apply (hv : v.IsRational) (a : K) :
    v.residueEquiv hv a = algebraMap K v.ResidueField a :=
  rfl

/-- The inverse of the map from the base field `K` into the residue field at a rational place. -/
noncomputable def residueInv (hv : v.IsRational) : v.ResidueField → K :=
  (v.residueEquiv hv).symm

theorem algebraMap_residueInv (hv : v.IsRational) (x : v.ResidueField) :
    algebraMap K v.ResidueField (v.residueInv hv x) = x :=
  (v.residueEquiv hv).apply_symm_apply x

theorem residueInv_algebraMap (hv : v.IsRational) (a : K) :
    v.residueInv hv (algebraMap K v.ResidueField a) = a :=
  (v.residueEquiv hv).symm_apply_apply a

/-- A place is rational exactly when it has degree one. `Place.deg` is a `Module.finrank`, which
is `0` when the residue field has infinite degree over `K`; degree one makes that degree finite,
so no finiteness hypothesis is needed. -/
theorem isRational_iff_deg_eq_one : v.IsRational ↔ v.deg = 1 := by
  refine ⟨fun hv => ?_, fun h x => ?_⟩
  · change Module.finrank K v.ResidueField = 1
    rw [← (v.residueEquiv hv).toLinearEquiv.finrank_eq, Module.finrank_self]
  · have hbot : (⊥ : Subalgebra K v.ResidueField) = ⊤ :=
      Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr h
    have hx : x ∈ (⊥ : Subalgebra K v.ResidueField) := by
      rw [hbot]
      exact Algebra.mem_top
    exact Algebra.mem_bot.mp hx

open Classical in
/-- Evaluation of a function-field element at a rational place: the element of
the base field `K` whose image in the residue field is the residue of the
element when the element lies in the valuation subring, and `0` otherwise. -/
noncomputable def evalAt (hv : v.IsRational) (f : F) : K :=
  if hf : f ∈ v.toValuationSubring then
    v.residueInv hv (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩)
  else 0

theorem evalAt_of_mem (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt hv f = v.residueInv hv (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩) :=
  dite_eq_left hf

theorem algebraMap_evalAt (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    algebraMap K v.ResidueField (v.evalAt hv f)
      = IsLocalRing.residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [v.evalAt_of_mem hv hf]
  exact v.algebraMap_residueInv hv _

theorem evalAt_add (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) :
    v.evalAt hv (f + g) = v.evalAt hv f + v.evalAt hv g := by
  apply (algebraMap K v.ResidueField).injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_mul (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) :
    v.evalAt hv (f * g) = v.evalAt hv f * v.evalAt hv g := by
  apply (algebraMap K v.ResidueField).injective
  rw [map_mul, v.algebraMap_evalAt hv (mul_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

@[simp]
theorem evalAt_one (hv : v.IsRational) : v.evalAt hv (1 : F) = 1 := by
  rw [v.evalAt_of_mem hv (one_mem _)]
  have h1 : (⟨(1 : F), one_mem _⟩ : v.toValuationSubring) = 1 := rfl
  rw [h1, map_one, ← map_one (algebraMap K v.ResidueField), v.residueInv_algebraMap hv]

end Place

end AlgebraicCurve

namespace CurveDivisor

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Evaluation of a divisor of places supported on rational places against a
function-field element: the product over the divisor of the values of the
element at each place, raised to the divisor coefficient at that place.

The value is multiplicative in the divisor only where the element has nonzero
values. If `f` has the value `0` at `v` (a zero of `f`, or a pole, where
`Place.evalAt` gives `0`), then `[v]` and `-[v]` both evaluate to `0`, since
`0⁻¹ = 0`, while their sum evaluates to `1`. `WeilReciprocity` evaluates each of
its two nonzero functions only on the divisor of the other, whose support
carries none of its zeros or poles. -/
noncomputable def evalFun (f : F) (D : CurveDivisor (Place K F))
    (hD : ∀ v ∈ D.support, v.IsRational) : K :=
  ∏ v ∈ D.support.attach, (v : Place K F).evalAt (hD v v.2) f ^ D v

theorem evalFun_def (f : F) (D : CurveDivisor (Place K F))
    (hD : ∀ v ∈ D.support, v.IsRational) :
    evalFun f D hD = ∏ v ∈ D.support.attach, (v : Place K F).evalAt (hD v v.2) f ^ D v :=
  rfl

@[simp]
theorem evalFun_zero (f : F)
    (hD : ∀ v ∈ (0 : CurveDivisor (Place K F)).support, v.IsRational) :
    evalFun f 0 hD = 1 := by
  rw [evalFun_def]
  exact Finset.prod_eq_one fun v _ => (Finsupp.mem_support_iff.mp v.2 rfl).elim

theorem evalFun_single (f : F) (v : Place K F) (hv : v.IsRational) (n : ℤ)
    (hD : ∀ w ∈ (Finsupp.single v n).support, w.IsRational) :
    evalFun f (Finsupp.single v n) hD = v.evalAt hv f ^ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [evalFun_def, zpow_zero]
    exact Finset.prod_eq_one fun w _ => (Finsupp.mem_support_iff.mp w.2 (by simp)).elim
  · have hmem : v ∈ (Finsupp.single v n).support := by simpa using hn
    rw [evalFun_def, Finset.prod_eq_single_of_mem ⟨v, hmem⟩ (Finset.mem_attach _ _)]
    · change v.evalAt (hD v hmem) f ^ Finsupp.single v n v = _
      rw [Finsupp.single_eq_same]
    · intro w _ hw
      exact (hw (Subtype.ext (Finset.mem_singleton.mp (Finsupp.support_single_subset w.2)))).elim

end CurveDivisor

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F] in
/-- Weil reciprocity at rational places: for nonzero `f` and `g` in `F` whose
principal divisors have disjoint supports consisting of rational places,
evaluating `f` on the divisor of `g` agrees with evaluating `g` on the divisor
of `f`. Both functions must be nonzero: `Place.ord 0 = 0`, so the zero function
has the zero divisor, and for `f = 0` the two sides can be `0` and `1`. -/
def WeilReciprocity : Prop :=
  ∀ (f g : F) (Df Dg : CurveDivisor (Place K F)), f ≠ 0 → g ≠ 0 →
    (∀ v : Place K F, Df v = v.ord f) → (∀ v : Place K F, Dg v = v.ord g) →
    (∀ v : Place K F, v.ord f = 0 ∨ v.ord g = 0) →
    ∀ (hDf : ∀ v ∈ Df.support, Place.IsRational v)
      (hDg : ∀ v ∈ Dg.support, Place.IsRational v),
      CurveDivisor.evalFun f Dg hDg = CurveDivisor.evalFun g Df hDf

end AlgebraicCurve
