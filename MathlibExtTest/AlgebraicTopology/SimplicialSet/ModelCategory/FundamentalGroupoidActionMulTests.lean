/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidActionMul

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidActionMul

open SSet SSet.KanComplex

#check @π.action_mul
#check @π.actionMulEquiv
#check @π.actionMulEquiv_apply
#check @π.actionMulEquiv_id
#check @π.actionMulEquiv_comp

#check @π.action_mul.{1}
#check @π.action_mul.{0}
#check @π.actionMulEquiv.{1}
#check @π.actionMulEquiv.{0}
#check @π.actionMulEquiv_apply.{1}
#check @π.actionMulEquiv_apply.{0}
#check @π.actionMulEquiv_id.{1}
#check @π.actionMulEquiv_id.{0}
#check @π.actionMulEquiv_comp.{1}
#check @π.actionMulEquiv_comp.{0}

section Symbolic

variable {X : SSet.{u}} [KanComplex X] {m : ℕ} {x y z : X _⦋0⦌}

example (p : FundamentalGroupoid.mk (X := X) x ⟶ FundamentalGroupoid.mk y)
    (a b : π (m + 1) X x) :
    π.action p (a * b) = π.action p a * π.action p b :=
  π.action_mul p a b

example (p : FundamentalGroupoid.mk (X := X) x ⟶ FundamentalGroupoid.mk y) :
    π (m + 1) X x ≃* π (m + 1) X y :=
  π.actionMulEquiv p

example (p : FundamentalGroupoid.mk (X := X) x ⟶ FundamentalGroupoid.mk y)
    (a : π (m + 1) X x) :
    π.actionMulEquiv p a = π.action p a :=
  π.actionMulEquiv_apply p a

example :
    π.actionMulEquiv (m := m) (𝟙 (FundamentalGroupoid.mk (X := X) x)) =
      MulEquiv.refl (π (m + 1) X x) :=
  π.actionMulEquiv_id x

example (p : FundamentalGroupoid.mk (X := X) x ⟶ FundamentalGroupoid.mk y)
    (q : FundamentalGroupoid.mk (X := X) y ⟶ FundamentalGroupoid.mk z) :
    π.actionMulEquiv (m := m) (p ≫ q) =
      (π.actionMulEquiv (m := m) p).trans (π.actionMulEquiv (m := m) q) :=
  π.actionMulEquiv_comp p q

end Symbolic

section DegreeZero

variable {X : SSet.{u}} [KanComplex X] {x y : X _⦋0⦌}

example : Group (π 1 X x) := inferInstance

example (p : FundamentalGroupoid.mk (X := X) x ⟶ FundamentalGroupoid.mk y)
    (a b : π 1 X x) :
    π.action p (a * b) = π.action p a * π.action p b :=
  π.action_mul (m := 0) p a b

example : True := by
  fail_if_success let _ : CommGroup (π 1 X x) := inferInstance
  trivial

#guard ((Fin.last 0).castSucc.castSucc : Fin 3).val = 0
#guard ((Fin.last 0).castSucc.succ : Fin 3).val = 1
#guard ((Fin.last 0).succ.succ : Fin 3).val = 2

end DegreeZero

section DegreeOne

variable {X : SSet.{u}} [KanComplex X] {x y : X _⦋0⦌}

example (p : FundamentalGroupoid.mk (X := X) x ⟶ FundamentalGroupoid.mk y)
    (a b : π 2 X x) :
    π.action p (a * b) = π.action p a * π.action p b :=
  π.action_mul (m := 1) p a b

end DegreeOne

/-- error: Unknown constant `SSet.KanComplex.π.actionPathSimplex` -/
#guard_msgs in
#check SSet.KanComplex.π.actionPathSimplex

/-- error: Unknown constant `SSet.KanComplex.π.actionPathSimplex_naturality` -/
#guard_msgs in
#check SSet.KanComplex.π.actionPathSimplex_naturality

/-- error: Unknown constant `SSet.KanComplex.π.actionPathSimplex_boundary` -/
#guard_msgs in
#check SSet.KanComplex.π.actionPathSimplex_boundary

/-- error: Unknown constant `SSet.KanComplex.π.actionPathSimplex_eval₀` -/
#guard_msgs in
#check SSet.KanComplex.π.actionPathSimplex_eval₀

/-- error: Unknown constant `SSet.KanComplex.π.actionPathSimplex_eval₁` -/
#guard_msgs in
#check SSet.KanComplex.π.actionPathSimplex_eval₁

/-- error: Unknown constant `SSet.KanComplex.π.edgePathSimplex` -/
#guard_msgs in
#check SSet.KanComplex.π.edgePathSimplex

/-- error: Unknown constant `SSet.KanComplex.π.edgePathSimplex_naturality` -/
#guard_msgs in
#check SSet.KanComplex.π.edgePathSimplex_naturality

/-- error: Unknown constant `SSet.KanComplex.π.edgePathSimplex_endpoints` -/
#guard_msgs in
#check SSet.KanComplex.π.edgePathSimplex_endpoints

/-- error: Unknown constant `SSet.KanComplex.π.actionMulFaces` -/
#guard_msgs in
#check SSet.KanComplex.π.actionMulFaces

/-- error: Unknown constant `SSet.KanComplex.π.actionMulFaces_compatible` -/
#guard_msgs in
#check SSet.KanComplex.π.actionMulFaces_compatible

/-- error: Unknown constant `SSet.KanComplex.π.actionMulFaces_eval₀` -/
#guard_msgs in
#check SSet.KanComplex.π.actionMulFaces_eval₀

/-- error: Unknown constant `SSet.KanComplex.π.actionMulActionStruct` -/
#guard_msgs in
#check SSet.KanComplex.π.actionMulActionStruct

/-- error: Unknown constant `SSet.KanComplex.π.action_weakEquivalence` -/
#guard_msgs in
#check SSet.KanComplex.π.action_weakEquivalence

/-- error: Unknown constant `SSet.KanComplex.π.action_realization` -/
#guard_msgs in
#check SSet.KanComplex.π.action_realization

/-- error: Unknown constant `SSet.KanComplex.π.action_derived` -/
#guard_msgs in
#check SSet.KanComplex.π.action_derived

#print axioms SSet.KanComplex.π.action_mul
#print axioms SSet.KanComplex.π.actionMulEquiv
#print axioms SSet.KanComplex.π.actionMulEquiv_apply
#print axioms SSet.KanComplex.π.actionMulEquiv_id
#print axioms SSet.KanComplex.π.actionMulEquiv_comp

end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidActionMul
