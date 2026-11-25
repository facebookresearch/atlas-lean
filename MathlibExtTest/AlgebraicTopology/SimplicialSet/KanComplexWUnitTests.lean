/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWUnit

/-!
# Tests for the Kan realization--singular unit

Public-only clients for positive homotopy-group bijectivity and the
realization--singular unit weak equivalence on Kan complexes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra Opposite Simplicial
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet

namespace KanComplexWUnitTests

section PositiveDegrees

example (n : ℕ) (X : SSet.{u}) [SSet.KanComplex X]
    (x : X _⦋0⦌) :
    Function.Bijective
      (SSet.KanComplex.π.map (x := x)
        (sSetTopAdj.unit.app X) rfl (n + 1)) :=
  SSet.KanComplex.bijective_piMap_sSetTopAdj_unit_app_succ n X x

private abbrev realSingReal : SSet.{0} :=
  TopCat.toSSet.obj (TopCat.of ℝ)

private noncomputable def realSingRealPoint : realSingReal _⦋0⦌ :=
  TopCat.toSSetObj₀Equiv.symm (0 : ℝ)

example : Function.Bijective
    (SSet.KanComplex.π.map (x := realSingRealPoint)
      (sSetTopAdj.unit.app realSingReal) rfl 1) := by
  let _ : SSet.KanComplex realSingReal :=
    TopCat.toSSet_obj_kanComplex _
  exact SSet.KanComplex.bijective_piMap_sSetTopAdj_unit_app_succ
    0 realSingReal realSingRealPoint

example : Function.Bijective
    (SSet.KanComplex.π.map (x := realSingRealPoint)
      (sSetTopAdj.unit.app realSingReal) rfl 2) := by
  let _ : SSet.KanComplex realSingReal :=
    TopCat.toSSet_obj_kanComplex _
  exact SSet.KanComplex.bijective_piMap_sSetTopAdj_unit_app_succ
    1 realSingReal realSingRealPoint

end PositiveDegrees

section WeakEquivalence

example (X : SSet.{u}) [SSet.KanComplex X] :
    SSet.KanComplex.W (sSetTopAdj.unit.app X) :=
  SSet.KanComplex.W.sSetTopAdj_unit_app X

private theorem deltaZeroKanComplex :
    SSet.KanComplex (Δ[0] : SSet.{u}) := by
  rw [SSet.KanComplex.iff]
  intro n i _ _
  refine ⟨SSet.stdSimplex.isTerminalObj₀.from _, ?_⟩
  intro j hj
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

example : SSet.KanComplex.W
    (sSetTopAdj.unit.app (Δ[0] : SSet.{u})) := by
  let _ : SSet.KanComplex (Δ[0] : SSet.{u}) :=
    deltaZeroKanComplex
  exact SSet.KanComplex.W.sSetTopAdj_unit_app
    (Δ[0] : SSet.{u})

example : SSet.KanComplex.W
    (sSetTopAdj.unit.app realSingReal) := by
  let _ : SSet.KanComplex realSingReal :=
    TopCat.toSSet_obj_kanComplex _
  exact SSet.KanComplex.W.sSetTopAdj_unit_app realSingReal

end WeakEquivalence

section EmptyDisconnected

private noncomputable abbrev emptySingular : SSet.{1} :=
  TopCat.toSSet.obj (TopCat.of (ULift.{1} Empty))

private noncomputable abbrev twoPointSingular : SSet.{1} :=
  TopCat.toSSet.obj (TopCat.of (ULift.{1} (Fin 2)))

example : IsEmpty (emptySingular _⦋0⦌) :=
  (Equiv.isEmpty_congr
    (TopCat.toSSetObj₀Equiv (X := TopCat.of (ULift.{1} Empty)))).2 inferInstance

example : Nontrivial (twoPointSingular _⦋0⦌) :=
  (TopCat.toSSetObj₀Equiv
    (X := TopCat.of (ULift.{1} (Fin 2)))).nontrivial

example : SSet.KanComplex.W (sSetTopAdj.unit.app emptySingular) := by
  let _ : SSet.KanComplex emptySingular :=
    TopCat.toSSet_obj_kanComplex _
  exact SSet.KanComplex.W.sSetTopAdj_unit_app emptySingular

example : SSet.KanComplex.W (sSetTopAdj.unit.app twoPointSingular) := by
  let _ : SSet.KanComplex twoPointSingular :=
    TopCat.toSSet_obj_kanComplex _
  exact SSet.KanComplex.W.sSetTopAdj_unit_app twoPointSingular

end EmptyDisconnected

section Packaging

example (X : SSet.{u}) :
    Function.Bijective
      (SSet.mapπ₀ (sSetTopAdj.unit.app X)) :=
  SSet.bijective_mapπ₀_sSetTopAdj_unit_app X

example (X : SSet.{u}) [SSet.KanComplex X] :
    SSet.KanComplex.W (sSetTopAdj.unit.app X) ↔
      Function.Bijective
          (SSet.mapπ₀ (sSetTopAdj.unit.app X)) ∧
        ∀ (n : ℕ) (x : X _⦋0⦌), Function.Bijective
          (SSet.KanComplex.π.map (x := x)
            (sSetTopAdj.unit.app X) rfl (n + 1)) := by
  let _ : SSet.KanComplex ((Functor.id SSet.{u}).obj X) := by
    change SSet.KanComplex X
    infer_instance
  let _ : SSet.KanComplex
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj X) :=
    TopCat.toSSet_obj_kanComplex _
  exact SSet.KanComplex.W_iff (sSetTopAdj.unit.app X)

end Packaging

section MissingKan

variable (X : SSet.{u})

example : True := by
  fail_if_success
    have _ := SSet.KanComplex.W.sSetTopAdj_unit_app X
  trivial

end MissingKan

section DeltaOneBoundary

example : True := by
  fail_if_success
    let _ : SSet.KanComplex (Δ[1] : SSet.{0}) := inferInstance
  fail_if_success
    have _ := SSet.KanComplex.W.sSetTopAdj_unit_app
      (Δ[1] : SSet.{0})
  trivial

end DeltaOneBoundary

section WrongDegreeZero

variable (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌)

example : True := by
  fail_if_success
    have _ : Function.Bijective
        (SSet.KanComplex.π.map (x := x)
          (sSetTopAdj.unit.app X) rfl 0) :=
      SSet.KanComplex.bijective_piMap_sSetTopAdj_unit_app_succ
        0 X x
  trivial

end WrongDegreeZero

section ConcreteUniverses

variable (X₁ : SSet.{1}) [SSet.KanComplex X₁]
  (x₁ : X₁ _⦋0⦌)

example : Function.Bijective
    (SSet.KanComplex.π.map (x := x₁)
      (sSetTopAdj.unit.app X₁) rfl 1) :=
  SSet.KanComplex.bijective_piMap_sSetTopAdj_unit_app_succ
    0 X₁ x₁

example : SSet.KanComplex.W (sSetTopAdj.unit.app X₁) :=
  SSet.KanComplex.W.sSetTopAdj_unit_app X₁

example (X₀ : SSet.{0}) [SSet.KanComplex X₀]
    (x₀ : X₀ _⦋0⦌) : Function.Bijective
      (SSet.KanComplex.π.map (x := x₀)
        (sSetTopAdj.unit.app X₀) rfl 1) :=
  SSet.KanComplex.bijective_piMap_sSetTopAdj_unit_app_succ
    0 X₀ x₀

example (X₀ : SSet.{0}) [SSet.KanComplex X₀] :
    SSet.KanComplex.W (sSetTopAdj.unit.app X₀) :=
  SSet.KanComplex.W.sSetTopAdj_unit_app X₀

end ConcreteUniverses

section ScopeBoundary

example : True := by
  fail_if_success
    let _ : ModelCategory SSet.{0} := inferInstance
  fail_if_success
    let _ : CategoryWithWeakEquivalences SSet.{0} := inferInstance
  trivial

end ScopeBoundary

section PrivateBoundary

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.FibrationSequence.subsingleton_pi_realSing_basedPath

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.FibrationSequence.unitObjZeroIso

end PrivateBoundary

#print axioms SSet.KanComplex.bijective_piMap_sSetTopAdj_unit_app_succ
#print axioms SSet.KanComplex.W.sSetTopAdj_unit_app
#print axioms SSet.bijective_mapπ₀_sSetTopAdj_unit_app
#print axioms SSet.KanComplex.W_iff

end KanComplexWUnitTests

end MathlibExtTest.AlgebraicTopology.SimplicialSet
