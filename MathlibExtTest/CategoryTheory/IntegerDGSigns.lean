/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.IntegerDGRestriction
import MathlibExt.CategoryTheory.DGSource.DGCochainCategory

/-! A nonzero differential and odd negative-degree cochains check both
the retained integer differential and the native Koszul composition sign.
No compact, analytic, or completion construction is assumed.
-/

open CategoryTheory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.IntegerDGRestriction
open CochainComplex.HomComplex

noncomputable section

set_option backward.isDefEq.respectTransparency false

private abbrev R := ULift.{1} ℤ
private abbrev A := ModuleCat.of R R
private def differential (n : ℤ) : A ⟶ A := if n = 0 then (2 : R) • 𝟙 A else 0
private theorem square (n : ℤ) : differential n ≫ differential (n+1) = 0 := by
  by_cases h : n = 0
  · subst n
    simp [differential]
  · simp [differential, h]
private def K : CochainComplex (ModuleCat.{1} R) ℤ :=
  CochainComplex.of (fun _ ↦ A) differential square
private def h : Cochain K K (-1) := Cochain.mk (fun _ _ _ ↦ 𝟙 A)
private abbrev D := IntegerDG R (CochainComplex (ModuleCat.{1} R) ℤ)

example : (((dgDifferential (C := D) Integers.{1} (-1)
    (show DGHom (C := D) Integers.{1} (-1) K K from h) : Cochain K K 0).v
      0 0 (by omega)).hom (1 : R)) = (2 : R) := by
  rw [integer_differential, dgDifferential_linearHomComplex]
  simp [δ, h, K, CochainComplex.of.d, differential, Module.End.mul_eq_comp]

example : (((dgComp (C := D) Integers.{1}
    (show DGHom (C := D) Integers.{1} (-1) K K from h)
    (show DGHom (C := D) Integers.{1} (-1) K K from h) (by omega : -1 + -1 = -2) :
      Cochain K K (-2)).v 0 (-2) (by omega)).hom (1 : R)) = (-1 : R) := by
  rw [integer_composition, dgComp_linearHomComplex]
  simp [h, Cochain.comp, Cochain.v]
  rfl

#print axioms MathlibExt.CategoryTheory.IntegerDGRestriction.integer_differential
#print axioms MathlibExt.CategoryTheory.IntegerDGRestriction.integer_composition
