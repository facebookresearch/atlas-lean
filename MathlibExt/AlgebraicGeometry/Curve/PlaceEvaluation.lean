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

@[expose] public section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

/-- A place is rational when the constant field surjects onto its residue
field. -/
def IsRational : Prop := Function.Surjective (algebraMap K v.ResidueField)

theorem algebraMap_residueField_injective :
    Function.Injective (algebraMap K v.ResidueField) :=
  (algebraMap K v.ResidueField).injective

/-- The inverse of the constant-field map into the residue field at a rational
place. -/
noncomputable def residueInv (hv : v.IsRational) : v.ResidueField → K :=
  Function.surjInv hv

theorem algebraMap_residueInv (hv : v.IsRational) (x : v.ResidueField) :
    algebraMap K v.ResidueField (v.residueInv hv x) = x :=
  Function.surjInv_eq hv x

theorem residueInv_algebraMap (hv : v.IsRational) (a : K) :
    v.residueInv hv (algebraMap K v.ResidueField a) = a :=
  Function.leftInverse_surjInv ⟨v.algebraMap_residueField_injective, hv⟩ a

open Classical in
/-- Evaluation of a function-field element at a rational place: the
constant-field element whose image in the residue field is the residue of the
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
element at each place, raised to the divisor coefficient at that place. -/
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
/-- The Weil reciprocity statement for principal divisors with disjoint
support at rational places: evaluating one principal divisor against the
other function agrees in both orders. -/
def WeilReciprocity : Prop :=
  ∀ (f g : F) (Df Dg : CurveDivisor (Place K F)), f ≠ 0 → g ≠ 0 →
    (∀ v : Place K F, Df v = v.ord f) → (∀ v : Place K F, Dg v = v.ord g) →
    (∀ v : Place K F, v.ord f = 0 ∨ v.ord g = 0) →
    ∀ (hDf : ∀ v ∈ Df.support, Place.IsRational v)
      (hDg : ∀ v ∈ Dg.support, Place.IsRational v),
      CurveDivisor.evalFun f Dg hDg = CurveDivisor.evalFun g Df hDf

end AlgebraicCurve
