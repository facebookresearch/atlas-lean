/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalSimplices
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable

/-!
# Finite Joyal Interval Simplices
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace SSet.FiniteJoyalIntervalSimplicesTest

theorem concreteCounts :
    Nat.card (joyalInterval.{u} _⦋0⦌) = 2 ∧
    Nat.card (joyalInterval.{u}.nonDegenerate 1) = 3 ∧
    Nat.card (joyalInterval.{u}.nonDegenerate 2) = 2 :=
  ⟨joyalInterval.card_vertices, joyalInterval.card_nonDegenerate_edges,
    joyalInterval.card_nonDegenerate_triangles⟩

/-- The separately named backward maps remain strictly distinct. -/
theorem distinctBackwardGenerators :
    joyalInterval.leftInverse.{u} ≠ joyalInterval.rightInverse.{u} := by
  intro h
  have heq : joyalInterval.nonDegenerateEdgesEquiv.{u} 1 =
      joyalInterval.nonDegenerateEdgesEquiv.{u} 2 := by
    apply Subtype.ext
    rw [joyalInterval.nonDegenerateEdgesEquiv_one,
      joyalInterval.nonDegenerateEdgesEquiv_two, h]
  have hi := joyalInterval.nonDegenerateEdgesEquiv.{u}.injective heq
  exact (by decide : (1 : Fin 3) ≠ 2) hi

/-- The enumeration also distinguishes the actual complete triangle maps. -/
theorem distinctTriangles :
    joyalInterval.leftTriangle.{u} ≠ joyalInterval.rightTriangle.{u} := by
  intro h
  have heq : joyalInterval.nonDegenerateTrianglesEquiv.{u} 0 =
      joyalInterval.nonDegenerateTrianglesEquiv.{u} 1 := by
    apply Subtype.ext
    rw [joyalInterval.nonDegenerateTrianglesEquiv_zero,
      joyalInterval.nonDegenerateTrianglesEquiv_one, h]
  have hi := joyalInterval.nonDegenerateTrianglesEquiv.{u}.injective heq
  exact (by decide : (0 : Fin 2) ≠ 1) hi

/-- The endpoint coproduct is usable directly as a monomorphism by clients. -/
theorem endpointCoprod_detectsEquality {Z : SSet.{u}}
    (a b : Z ⟶ (Δ[0] : SSet.{u}) ⨿ Δ[0])
    (h : a ≫ joyalInterval.endpointCoprod.{u} = b ≫ joyalInterval.endpointCoprod.{u}) :
    a = b :=
  (cancel_mono joyalInterval.endpointCoprod).1 h

/-- Finiteness supplies the native presentability input for the small object argument. -/
theorem finitelyPresentable : IsFinitelyPresentable.{u} joyalInterval.{u} := by
  infer_instance

end SSet.FiniteJoyalIntervalSimplicesTest
