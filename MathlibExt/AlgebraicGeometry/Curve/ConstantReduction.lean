/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_ConstantReduction.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
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

public import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluationOrd

/-!
# Constant reduction of function fields

Let `A` be a valuation ring of the field of constants `L` of a function field `F`. A
`ConstantReduction A F Fbar` records a reduction of `F` modulo `A` to a function field `Fbar` over
the residue field of `A`: a valuation ring `integers` of `F` lying over `A`, its residue map onto
`Fbar`, and for each place `P` of `F` its reduction `placeDivisor P`, an effective divisor of
`Fbar`. A place need not reduce to a single place: modulo `5`, the place of `x ^ 2 + 1` of `ℚ(x)`
reduces to the sum of the places `x = 2` and `x = 3` of `𝔽₅(x)`.

The structure assumes, as fields, that a place and its reduction have the same degree
(`degree_placeDivisor`) and that reduction takes the divisor of a function with nonzero residue to
the divisor of that residue (`sum_smul_placeDivisor`). It does not construct a reduction, and these
two properties are not derived. From them this file builds the reduction map `divMap` on divisors,
shows that it preserves degrees and principal divisors, and derives the maps `degZeroMap` on
divisors of degree zero and `pic0Map` on the degree-zero Picard group `Pic0`. Good reduction,
`ConstantReduction.IsGood`, is equality of the genera of `Fbar` and `F`.

These two fields and the effectivity `placeDivisor_nonneg` are the characterising properties of
Deuring's reduction of divisors: effective divisors reduce to effective divisors, degrees are
preserved, and the divisor of a function with nonzero residue reduces to the divisor of that
residue (M. Deuring, *Reduktion algebraischer Funktionenkörper nach Primdivisoren des
Konstantenkörpers*, Math. Z. 47 (1942), 643–654).

The field `exists_smul_mem` gives `integers` the value group of `A`: a constant multiple of a
function that lies in `integers` with nonzero residue is a unit there. So the structure covers only
reductions with the value group of `A`. A constant reduction in general may have a larger value
group: the prolongation of the `5`-adic valuation to `ℚ(x)` in which `x` has value `1 / 2` has
residue field `𝔽₅(t)`, with `t` the residue of `x ^ 2 / 5`, and admits no `ConstantReduction` with
its valuation ring as `integers`.

This file adapts `Definitions/Def_AlgebraicCurve_ConstantReduction.lean` of the FLT project (see
the header) with two changes. There a place reduces to a single place of the same degree; here it
reduces to an effective divisor (`placeDivisor`), and `divMap` and the results about it are built on
that. And the two lemmas on orders of constant multiples are in the `Place` namespace:
`Place.ord_algebraMap`, from `MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluationOrd`, needs no
hypothesis on the constant, and `Place.ord_smul_of_ne_zero` is stated here.
-/

@[expose] public section

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Multiplying a function by a nonzero constant does not change its order at a place. -/
theorem ord_smul_of_ne_zero (v : Place K F) {c : K} (hc : c ≠ 0) (f : F) :
    v.ord (c • f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr hc) hf, v.ord_algebraMap, zero_add]

end Place

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]

/-- A reduction of the function field `F` over `L` modulo the valuation ring `A` of `L`, to the
function field `Fbar` over the residue field of `A`: a valuation ring `integers` of `F` lying over
`A`, a residue map from it onto `Fbar`, and the reduction `placeDivisor P` of each place `P` of `F`,
an effective divisor of `Fbar`. Two properties are assumed as fields, not derived: a place and its
reduction have the same degree (`degree_placeDivisor`), and the reduction of the divisor of a
function with nonzero residue is the divisor of that residue (`sum_smul_placeDivisor`). The field
`exists_smul_mem` restricts the structure to reductions with the value group of `A`. -/
structure ConstantReduction where
  /-- The valuation ring of `F` along which `F` is reduced. -/
  integers : ValuationSubring F
  /-- The residue map of `integers`, onto `Fbar`. -/
  residue : integers →+* Fbar
  /-- The reduction of a place of `F`, a divisor of `Fbar`. -/
  placeDivisor : Place L F → Divisor (ResidueField A) Fbar
  /-- `integers` lies over `A`: a constant is in `integers` exactly when it is in `A`. -/
  algebraMap_mem_iff : ∀ x : L, algebraMap L F x ∈ integers ↔ x ∈ A
  /-- The residue map is surjective. -/
  residue_surjective : Function.Surjective residue
  /-- The kernel of the residue map is the maximal ideal of `integers`. -/
  ker_residue : RingHom.ker residue = maximalIdeal integers
  /-- On constants in `A`, the residue map is reduction modulo the maximal ideal of `A`. -/
  residue_algebraMap : ∀ a : A,
    residue ⟨algebraMap L F a, (algebraMap_mem_iff a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a)
  /-- Every nonzero function has a constant multiple in `integers` with nonzero residue; so
  `integers` has the value group of `A`. -/
  exists_smul_mem : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ integers, residue ⟨c • f, h⟩ ≠ 0
  /-- The reduction of a place is effective. -/
  placeDivisor_nonneg : ∀ P, 0 ≤ placeDivisor P
  /-- Assumed: the reduction of a place has the degree of the place. -/
  degree_placeDivisor : ∀ P, Divisor.degree (placeDivisor P) = P.deg
  /-- Assumed: for a function `f` in `integers` with nonzero residue, reducing the divisor `D` of
  `f` place by place, with multiplicities, gives the divisor of the residue of `f`. -/
  sum_smul_placeDivisor : ∀ f : integers, residue f ≠ 0 → ∀ D : Divisor L F,
    (∀ P, D P = P.ord (f : F)) → ∀ Q, (D.sum fun P n => n • placeDivisor P) Q = Q.ord (residue f)

namespace ConstantReduction

variable {A F Fbar}

set_option linter.unusedVariables false in
/-- Good reduction: the reduced function field `Fbar` has the genus of `F`. The condition depends
on `R` only through `A`, `F` and `Fbar`; it takes `R` so that it reads as a property of a given
reduction. -/
def IsGood (R : ConstantReduction A F Fbar) : Prop :=
  genusFF (ResidueField A) Fbar = genusFF L F

/-- A reduction is good exactly when `Fbar` and `F` have the same genus. -/
theorem isGood_iff (R : ConstantReduction A F Fbar) :
    R.IsGood ↔ genusFF (ResidueField A) Fbar = genusFF L F :=
  Iff.rfl

variable (R : ConstantReduction A F Fbar)

/-- The reduction of divisors: a divisor `∑ nᵢ Pᵢ` of `F` goes to `∑ nᵢ • placeDivisor Pᵢ`. -/
def divMap : Divisor L F →+ Divisor (ResidueField A) Fbar :=
  Finsupp.liftAddHom fun P => zmultiplesHom _ (R.placeDivisor P)

theorem divMap_apply (D : Divisor L F) :
    R.divMap D = D.sum fun P n => n • R.placeDivisor P :=
  rfl

@[simp]
theorem divMap_single (P : Place L F) (n : ℤ) :
    R.divMap (Finsupp.single P n) = n • R.placeDivisor P := by
  rw [divMap_apply, Finsupp.sum_single_index (zero_smul ℤ (R.placeDivisor P))]

/-- The reduction of divisors preserves degrees, by `degree_placeDivisor`. -/
theorem degree_divMap (D : Divisor L F) :
    Divisor.degree (R.divMap D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add P n D _ _ ih =>
    rw [map_add, map_add, map_add, ih, divMap_single, map_zsmul, R.degree_placeDivisor,
      Divisor.degree_single, smul_eq_mul]

/-- The reduction of divisors takes principal divisors to principal divisors: a principal divisor is
the divisor of a function, which a constant multiple makes integral with nonzero residue without
changing its divisor, and `sum_smul_placeDivisor` applies to that multiple. -/
theorem divMap_mem_principal {D : Divisor L F}
    (hD : D ∈ Divisor.principal (K := L) (F := F)) :
    R.divMap D ∈ Divisor.principal (K := ResidueField A) (F := Fbar) := by
  obtain ⟨f, hf0, hDf⟩ := hD
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f hf0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : L) • f, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]
  exact ⟨R.residue ⟨c • f, hc⟩, hres, fun Q =>
    R.sum_smul_placeDivisor ⟨c • f, hc⟩ hres D
      (fun P => by rw [hDf P]; exact (P.ord_smul_of_ne_zero hc0 f).symm) Q⟩

/-- The reduction of divisors takes divisors of degree zero to divisors of degree zero. -/
theorem divMap_mem_degZero {D : Divisor L F}
    (hD : D ∈ Divisor.degZero (K := L) (F := F)) :
    R.divMap D ∈ Divisor.degZero (K := ResidueField A) (F := Fbar) := by
  rw [Divisor.mem_degZero] at hD ⊢
  rw [R.degree_divMap, hD]

/-- The reduction map on divisors of degree zero. -/
def degZeroMap :
    Divisor.degZero (K := L) (F := F) →+ Divisor.degZero (K := ResidueField A) (F := Fbar) :=
  (R.divMap.domRestrict (Divisor.degZero (K := L) (F := F))).codRestrict _
    fun D => R.divMap_mem_degZero D.2

@[simp]
theorem coe_degZeroMap (D : Divisor.degZero (K := L) (F := F)) :
    (R.degZeroMap D : Divisor (ResidueField A) Fbar) = R.divMap (D : Divisor L F) :=
  rfl

/-- The reduction map on degree-zero Picard groups, induced by `degZeroMap`: it is well defined
because `divMap` takes principal divisors to principal divisors. -/
def pic0Map : Pic0 L F →+ Pic0 (ResidueField A) Fbar :=
  QuotientAddGroup.map _ _ R.degZeroMap (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact R.divMap_mem_principal hD)

theorem pic0Map_mk (D : Divisor.degZero (K := L) (F := F)) :
    R.pic0Map (Pic0.mk D) = Pic0.mk (R.degZeroMap D) :=
  rfl

end ConstantReduction

end AlgebraicCurve

end
