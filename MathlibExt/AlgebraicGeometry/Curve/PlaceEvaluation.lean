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

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import MathlibExt.AlgebraicGeometry.Curve.Place

import Mathlib.Algebra.BigOperators.Finsupp.Basic

@[expose] public section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

/-- The residue field of a place: the residue field of its valuation
subring. -/
abbrev ResidueField : Type _ := IsLocalRing.ResidueField v.toValuationSubring

/-- A place is rational when the constant field surjects onto its residue
field. -/
def IsRational : Prop := Function.Surjective (algebraMap K v.ResidueField)

theorem algebraMap_residueField_injective :
    Function.Injective (algebraMap K v.ResidueField) :=
  (algebraMap K v.ResidueField).injective

/-- A chosen inverse of the constant-field map into the residue field,
defined by choice from the map; it is a genuine inverse at rational
places. -/
noncomputable def residueInv : v.ResidueField → K :=
  Function.invFun (algebraMap K v.ResidueField)

theorem algebraMap_residueInv (hv : v.IsRational) (x : v.ResidueField) :
    algebraMap K v.ResidueField (v.residueInv x) = x :=
  Function.invFun_eq (hv x)

theorem residueInv_algebraMap (a : K) :
    v.residueInv (algebraMap K v.ResidueField a) = a :=
  Function.leftInverse_invFun v.algebraMap_residueField_injective a

open Classical in
/-- Evaluation of a function-field element at a place: the chosen
constant-field representative of its residue when the element lies in
the valuation subring, and `0` otherwise. -/
noncomputable def evalAt (f : F) : K :=
  if hf : f ∈ v.toValuationSubring then
    v.residueInv (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩)
  else 0

theorem evalAt_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = v.residueInv (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩) :=
  dite_eq_left hf

theorem algebraMap_evalAt (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    algebraMap K v.ResidueField (v.evalAt f)
      = IsLocalRing.residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [v.evalAt_of_mem hf]
  exact v.algebraMap_residueInv hv _

@[simp]
theorem evalAt_one : v.evalAt (1 : F) = 1 := by
  rw [v.evalAt_of_mem (one_mem _)]
  have h1 : (⟨(1 : F), one_mem _⟩ : v.toValuationSubring) = 1 := rfl
  rw [h1, map_one, ← map_one (algebraMap K v.ResidueField), v.residueInv_algebraMap]

end Place

/-- A divisor on the places of `F` over `K`: a finitely supported integer
combination of places. -/
abbrev Divisor (K F : Type*) [Field K] [Field F] [Algebra K F] : Type _ :=
  Place K F →₀ ℤ

namespace Divisor

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Evaluation of a divisor against a function-field element: the product
over the divisor of the values of the element at each place, raised to
the divisor coefficient at that place. -/
noncomputable def evalFun (f : F) (D : Divisor K F) : K :=
  D.prod fun v n => v.evalAt f ^ n

theorem evalFun_def (f : F) (D : Divisor K F) :
    evalFun f D = ∏ v ∈ D.support, v.evalAt f ^ D v := rfl

@[simp]
theorem evalFun_zero (f : F) : evalFun f (0 : Divisor K F) = 1 :=
  Finsupp.prod_zero_index

theorem evalFun_single (f : F) (v : Place K F) (n : ℤ) :
    evalFun f (Finsupp.single v n) = v.evalAt f ^ n :=
  Finsupp.prod_single_index (zpow_zero _)

end Divisor

variable (K F : Type*) [Field K] [Field F] [Algebra K F] in
/-- The Weil reciprocity statement for principal divisors with disjoint
support at rational places: evaluating one principal divisor against the
other function agrees in both orders. -/
def WeilReciprocity : Prop :=
  ∀ (f g : F) (Df Dg : Divisor K F), f ≠ 0 → g ≠ 0 →
    (∀ v : Place K F, Df v = v.ord f) → (∀ v : Place K F, Dg v = v.ord g) →
    (∀ v : Place K F, v.ord f = 0 ∨ v.ord g = 0) →
    (∀ v ∈ Df.support, Place.IsRational v) → (∀ v ∈ Dg.support, Place.IsRational v) →
    Divisor.evalFun f Dg = Divisor.evalFun g Df

end AlgebraicCurve
