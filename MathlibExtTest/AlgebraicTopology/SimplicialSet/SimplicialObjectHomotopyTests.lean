/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialObjectHomotopy

/-!
# Tests for the reverse simplicial-homotopy adapter

These tests pin the interval-cut formulas, all faces and degeneracies, both
literal cylinder endpoints, the left-inverse round trip to Mathlib's existing
conversion, and universe polymorphism.  They make no realization,
weak-equivalence, extra-degeneracy, or model-category claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace SimplicialObjectHomotopyTests

variable {X Y : SSet.{u}} {f g : X ⟶ Y}
  (H : SimplicialObject.Homotopy f g)

example (n : ℕ) :
    Fin (n + 2) ≃ (Δ[1] : SSet.{u}).obj (op ⦋n⦌) :=
  SSet.stdSimplex.objMk₁Equiv n

example : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y :=
  H.toSSetHomotopyMap

example : SSet.Homotopy f g :=
  H.toSSetHomotopy

example (n : ℕ) (x : X.obj (op ⦋n⦌)) :
    (H.toSSetHomotopyMap.app (op ⦋n⦌))
        (x, SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) =
      g.app (op ⦋n⦌) x := by
  exact H.toSSetHomotopyMap_app_objMk₁_zero n x

example (n : ℕ) (x : X.obj (op ⦋n⦌)) (j : Fin (n + 1)) :
    (H.toSSetHomotopyMap.app (op ⦋n⦌))
        (x, SSet.stdSimplex.objMk₁ j.succ) =
      (H.h j ≫ Y.δ j.succ) x := by
  exact H.toSSetHomotopyMap_app_objMk₁_succ n x j

section LowCuts

example (x : X.obj (op ⦋0⦌)) :
    (H.toSSetHomotopyMap.app (op ⦋0⦌))
        (x, SSet.stdSimplex.objMk₁ (0 : Fin 2)) =
      g.app (op ⦋0⦌) x := by
  exact H.toSSetHomotopyMap_app_objMk₁_zero 0 x

example (x : X.obj (op ⦋0⦌)) :
    (H.toSSetHomotopyMap.app (op ⦋0⦌))
        (x, SSet.stdSimplex.objMk₁ (1 : Fin 2)) =
      (H.h (0 : Fin 1) ≫ Y.δ (1 : Fin 2)) x := by
  exact H.toSSetHomotopyMap_app_objMk₁_succ 0 x 0

example (x : X.obj (op ⦋1⦌)) (j : Fin 2) :
    (H.toSSetHomotopyMap.app (op ⦋1⦌))
        (x, SSet.stdSimplex.objMk₁ j.succ) =
      (H.h j ≫ Y.δ j.succ) x := by
  exact H.toSSetHomotopyMap_app_objMk₁_succ 1 x j

example (x : X.obj (op ⦋2⦌)) (j : Fin 3) :
    (H.toSSetHomotopyMap.app (op ⦋2⦌))
        (x, SSet.stdSimplex.objMk₁ j.succ) =
      (H.h j ≫ Y.δ j.succ) x := by
  exact H.toSSetHomotopyMap_app_objMk₁_succ 2 x j

end LowCuts

section Naturality

example {n : ℕ} (i : Fin (n + 2)) :
    (X ⊗ (Δ[1] : SSet.{u})).map (SimplexCategory.δ i).op ≫
        H.toSSetHomotopyMap.app (op ⦋n⦌) =
      H.toSSetHomotopyMap.app (op ⦋n + 1⦌) ≫
        Y.map (SimplexCategory.δ i).op :=
  H.toSSetHomotopyMap.naturality (SimplexCategory.δ i).op

example {n : ℕ} (i : Fin (n + 1)) :
    (X ⊗ (Δ[1] : SSet.{u})).map (SimplexCategory.σ i).op ≫
        H.toSSetHomotopyMap.app (op ⦋n + 1⦌) =
      H.toSSetHomotopyMap.app (op ⦋n⦌) ≫
        Y.map (SimplexCategory.σ i).op :=
  H.toSSetHomotopyMap.naturality (SimplexCategory.σ i).op

example {a b : SimplexCategoryᵒᵖ} (φ : a ⟶ b) :
    (X ⊗ (Δ[1] : SSet.{u})).map φ ≫
        H.toSSetHomotopyMap.app b =
      H.toSSetHomotopyMap.app a ≫ Y.map φ :=
  H.toSSetHomotopyMap.naturality φ

end Naturality

section EndpointsAndRoundTrip

example : SSet.ι₀ ≫ H.toSSetHomotopy.h = f :=
  H.toSSetHomotopy_h₀

example : SSet.ι₁ ≫ H.toSSetHomotopy.h = g :=
  H.toSSetHomotopy_h₁

example : H.toSSetHomotopy.toSimplicialObjectHomotopy = H := by
  simp

example {n : ℕ} (i : Fin (n + 1)) :
    H.toSSetHomotopy.toSimplicialObjectHomotopy.h i = H.h i := by
  have h := congrArg
    (fun K : SimplicialObject.Homotopy f g => K.h i)
    H.toSSetHomotopy_toSimplicialObjectHomotopy
  exact h

/- error: type mismatch -/
#guard_msgs (error, substring := true) in
example : SSet.ι₀ ≫ H.toSSetHomotopy.h = g :=
  H.toSSetHomotopy_h₁

end EndpointsAndRoundTrip

section Universes

variable {X₀ Y₀ : SSet.{0}} {f₀ g₀ : X₀ ⟶ Y₀}
  (H₀ : SimplicialObject.Homotopy f₀ g₀)
variable {X₁ Y₁ : SSet.{1}} {f₁ g₁ : X₁ ⟶ Y₁}
  (H₁ : SimplicialObject.Homotopy f₁ g₁)

example : SSet.Homotopy f₀ g₀ := H₀.toSSetHomotopy
example : SSet.Homotopy f₁ g₁ := H₁.toSSetHomotopy

end Universes

section Nonclaims

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences_of_simplicialObjectHomotopyEquiv

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check SimplicialObject.Augmented.ExtraDegeneracy.hom_mem_realizationWeakEquivalences

end Nonclaims

#print axioms SSet.stdSimplex.objMk₁Equiv
#print axioms CategoryTheory.SimplicialObject.Homotopy.toSSetHomotopyMap
#print axioms CategoryTheory.SimplicialObject.Homotopy.toSSetHomotopy
#print axioms CategoryTheory.SimplicialObject.Homotopy.toSSetHomotopy_toSimplicialObjectHomotopy

end SimplicialObjectHomotopyTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
