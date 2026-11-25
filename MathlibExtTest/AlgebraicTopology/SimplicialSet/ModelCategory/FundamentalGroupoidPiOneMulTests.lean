/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne

/-!
# Multiplicative first homotopy group comparison tests

These checks exercise the multiplicative comparison between the first
simplicial homotopy group and endomorphisms in the fundamental groupoid.  In
particular, the representative test retains the noncommutative order forced by
the opposite multiplication convention on `CategoryTheory.End`.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOneMulTests

#check @SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd
#check @SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_mk
#check @SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_naturality
#check @SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_action

#check @SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd.{1}
#check @SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_mk.{1}
#check @SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_naturality.{1}
#check @SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_action.{1}

#check @SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd.{0}
#check @SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_mk.{0}
#check @SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_naturality.{0}
#check @SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_action.{0}

#print axioms SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd
#print axioms SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_mk
#print axioms SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_naturality
#print axioms SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_action

/-- error: Unknown constant `SSet.KanComplex.edgePtEquiv` -/
#guard_msgs in
#check SSet.KanComplex.edgePtEquiv

/-- error: Unknown constant `SSet.KanComplex.relStruct₀OfHomotopyR` -/
#guard_msgs in
#check SSet.KanComplex.relStruct₀OfHomotopyR

/-- error: Unknown constant `SSet.KanComplex.homotopyROfRelStruct₀` -/
#guard_msgs in
#check SSet.KanComplex.homotopyROfRelStruct₀

/-- error: Unknown constant `SSet.KanComplex.πOneToHom` -/
#guard_msgs in
#check SSet.KanComplex.πOneToHom

/-- error: Unknown constant `SSet.KanComplex.homEquiv` -/
#guard_msgs in
#check SSet.KanComplex.homEquiv

/-- error: Unknown constant `SSet.KanComplex.compStructOfMulStruct` -/
#guard_msgs in
#check SSet.KanComplex.compStructOfMulStruct

/-- error: Unknown constant `SSet.KanComplex.actionHomotopy` -/
#guard_msgs in
#check SSet.KanComplex.actionHomotopy

noncomputable example {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌) :
    Group (SSet.KanComplex.π 1 X x) :=
  inferInstance

example {X : SSet.{u}} [SSet.KanComplex X] (_x : X _⦋0⦌) : True := by
  fail_if_success
    have witness : CommGroup (SSet.KanComplex.π 1 X _x) := inferInstance
  trivial

-- With an explicitly supplied instance, the synthesis guard must fail.
example {X : SSet.{u}} [SSet.KanComplex X] (x : X _⦋0⦌)
    [CommGroup (SSet.KanComplex.π 1 X x)] : True := by
  fail_if_success
    fail_if_success
      have witness : CommGroup (SSet.KanComplex.π 1 X x) := inferInstance
  trivial

private def loopEdge {X : SSet.{u}} {x : X _⦋0⦌}
    (p : X.PtSimplex 1 x) : X.Edge x x :=
  SSet.Edge.mk (SSet.yonedaEquiv (SSet.RelativeMorphism.map p))
    (by simp [← SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])
    (by simp [← SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const])

/-- The representative formula is available without exposing its quotient
implementation. -/
private theorem representative_client {X : SSet.{u}} [SSet.KanComplex X]
    (x : X _⦋0⦌) (p : X.PtSimplex 1 x) :
    SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd x
        (SSet.KanComplex.π.mk p) =
      End.of (CategoryTheory.inv (SSet.FundamentalGroupoid.homMk (loopEdge p))) := by
  simpa only [loopEdge] using
    SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_mk x p

/-- The two factors remain in reversed categorical-composition order.  This
uses only `Group`, not `CommGroup`, and therefore detects deletion of the
inverse in the comparison. -/
private theorem noncommutative_representative_order_client
    {X : SSet.{u}} [SSet.KanComplex X] {x : X _⦋0⦌}
    {p q r : X.PtSimplex 1 x}
    (h : SSet.PtSimplex.MulStruct p q r (0 : Fin 1)) :
    SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd x
        (SSet.KanComplex.π.mk r) =
      End.of (CategoryTheory.inv (SSet.FundamentalGroupoid.homMk (loopEdge q)) ≫
        CategoryTheory.inv (SSet.FundamentalGroupoid.homMk (loopEdge p))) := by
  rw [← h.mul_eq, map_mul]
  apply End.ext
  simp only [End.mul_asHom,
    SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_mk, loopEdge]

/-- Naturality has the target comparison on the left and functorial image on
the right. -/
private theorem naturality_client {X Y : SSet.{u}} [SSet.KanComplex X]
    [SSet.KanComplex Y] (f : X ⟶ Y) (x : X _⦋0⦌)
    (a : SSet.KanComplex.π 1 X x) :
    SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd (X := Y) (f.app _ x)
        (SSet.KanComplex.π.map f rfl 1 a) =
      (SSet.mapFundamentalGroupoid f).mapEnd (SSet.FundamentalGroupoid.mk x)
        (SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd x a) :=
  SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_naturality f x a

/-- Fundamental-groupoid transport is conjugation in the orientation
`q⁻¹ ≫ _ ≫ q`. -/
private theorem action_client {X : SSet.{u}} [SSet.KanComplex X]
    {x y : X _⦋0⦌}
    (q : SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk y)
    (a : SSet.KanComplex.π 1 X x) :
    SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd y
        (SSet.KanComplex.π.action q a) =
      (asIso q).conj
        (SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd x a) :=
  SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_action q a

end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOneMulTests

end
