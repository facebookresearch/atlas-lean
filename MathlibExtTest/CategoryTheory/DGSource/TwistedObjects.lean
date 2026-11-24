/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.DGSource.DGCochainCategory
import MathlibExt.CategoryTheory.DGSourceMore.DGTwistedTriangulated

/-!
# Tests for the ported differential graded category library

The cochain complexes of abelian groups form a differential graded category whose differential
is Mathlib's signed `δ` and whose composition carries the Koszul sign. On a complex with `ℤ` in
every degree and exactly one nonzero differential these operations give explicit values, and the
graded Leibniz rule
holds for them. The homotopy category of twisted objects over any differential graded category
carries the instances of the Bondal--Kapranov envelope.
-/

open CategoryTheory CochainComplex.HomComplex
open MathlibExt.DGSource

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.DGSourceTwistedObjects

/-- The complex `ℤ` in every degree, with differential `2` from degree `0` to degree `1` and
zero elsewhere. -/
private abbrev A : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ

private def differential (n : ℤ) : A ⟶ A := if n = 0 then (2 : ℤ) • 𝟙 A else 0

private theorem differential_comp (n : ℤ) : differential n ≫ differential (n + 1) = 0 := by
  by_cases h : n = 0
  · subst n
    simp [differential]
  · simp [differential, h]

private def K : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  CochainComplex.of (fun _ ↦ A) differential differential_comp

/-- The degree `-1` cochain whose components are all the identity. -/
private def h : DGHom ℤ (-1) K K := (Cochain.mk (fun _ _ _ ↦ 𝟙 A) : Cochain K K (-1))

/-- The differential of the DG category of cochain complexes is the signed `δ`: on `h` its
component from degree `0` to itself is multiplication by `2`. -/
example : ((dgDifferential ℤ (-1) h : Cochain K K 0).v 0 0 (by omega)).hom (1 : ℤ) =
    (2 : ℤ) := by
  rw [dgDifferential_linearHomComplex]
  simp [δ, h, K, CochainComplex.of.d, differential, Module.End.mul_eq_comp]

/-- Composition of two cochains of degree `-1` carries the Koszul sign `(-1) ^ ((-1) * (-1))`. -/
example : ((dgComp ℤ h h (by omega : -1 + -1 = -2) : Cochain K K (-2)).v 0 (-2)
    (by omega)).hom (1 : ℤ) = (-1 : ℤ) := by
  rw [dgComp_v ℤ h h (by omega) 0 (-1) (-2) (by omega) (by omega)]
  simp [h, Units.smul_def]
  rfl

/-- The identity of `K` is a cycle of degree zero. -/
example : dgDifferential ℤ 0 (dgId ℤ K) = 0 := dgDifferential_dgId ℤ K

/-- The graded Leibniz rule for the two cochains above, with the sign of the odd first factor. -/
example : dgDifferential ℤ (-2) (dgComp ℤ h h (by omega)) =
    dgComp ℤ (dgDifferential ℤ (-1) h) h (by omega) -
      dgComp ℤ h (dgDifferential ℤ (-1) h) (by omega) := by
  rw [dgDifferential_dgComp, Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    sub_eq_add_neg]

end MathlibExtTest.DGSourceTwistedObjects

section Instances

universe v u

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-- The cone triangles make the homotopy category of twisted objects pretriangulated. -/
example : Pretriangulated
    (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) :=
  inferInstance

/-- The octahedral axiom holds there. -/
example : IsTriangulated
    (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) :=
  inferInstance

end Instances
