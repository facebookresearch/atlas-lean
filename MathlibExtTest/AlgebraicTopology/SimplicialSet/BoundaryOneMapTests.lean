/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryOneMap

import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular

/-!
# Tests for maps from the boundary of the one-simplex

These clients pin the universe-polymorphic source, finite and nonsingular
instance inference, and the deliberately reversed face-index orientation:
face `1` selects the first vertex and face `0` selects the second.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace BoundaryOneMapTests

universe u

section Symbolic

variable {Y : SSet.{u}} (x₀ x₁ : Y _⦋0⦌)

example : (∂Δ[1] : SSet.{u}) ⟶ Y :=
  SSet.boundaryOneMap x₀ x₁

example : (∂Δ[1] : SSet.{u}).Finite := inferInstance

example : (∂Δ[1] : SSet.{u}).Nonsingular := inferInstance

example :
    SSet.boundary.ι (1 : Fin 2) ≫ SSet.boundaryOneMap x₀ x₁ =
      SSet.const x₀ := by
  simp

example :
    SSet.boundary.ι (0 : Fin 2) ≫ SSet.boundaryOneMap x₀ x₁ =
      SSet.const x₁ := by
  simp

example :
    (SSet.boundaryOneMap x₀ x₁).app (op ⦋0⦌)
        ((SSet.boundary.ι (1 : Fin 2)).app (op ⦋0⦌)
          (SSet.stdSimplex.obj₀Equiv.symm 0)) = x₀ := by
  let v : (Δ[0] : SSet.{u}) _⦋0⦌ :=
    SSet.stdSimplex.obj₀Equiv.symm 0
  have h := congrArg
    (fun k => k.app (op ⦋0⦌) v)
    (SSet.boundary_ι_one_boundaryOneMap x₀ x₁)
  change (SSet.boundaryOneMap x₀ x₁).app (op ⦋0⦌)
      ((SSet.boundary.ι (1 : Fin 2)).app (op ⦋0⦌) v) =
    (SSet.const x₀).app (op ⦋0⦌) v at h
  simpa [v, SSet.const] using h

example :
    (SSet.boundaryOneMap x₀ x₁).app (op ⦋0⦌)
        ((SSet.boundary.ι (0 : Fin 2)).app (op ⦋0⦌)
          (SSet.stdSimplex.obj₀Equiv.symm 0)) = x₁ := by
  let v : (Δ[0] : SSet.{u}) _⦋0⦌ :=
    SSet.stdSimplex.obj₀Equiv.symm 0
  have h := congrArg
    (fun k => k.app (op ⦋0⦌) v)
    (SSet.boundary_ι_zero_boundaryOneMap x₀ x₁)
  change (SSet.boundaryOneMap x₀ x₁).app (op ⦋0⦌)
      ((SSet.boundary.ι (0 : Fin 2)).app (op ⦋0⦌) v) =
    (SSet.const x₁).app (op ⦋0⦌) v at h
  simpa [v, SSet.const] using h

example :
    SSet.boundary.ι (1 : Fin 2) ≫ SSet.boundaryOneMap x₀ x₀ =
      SSet.const x₀ := by
  simp

example :
    SSet.boundary.ι (0 : Fin 2) ≫ SSet.boundaryOneMap x₀ x₀ =
      SSet.const x₀ := by
  simp

end Symbolic

section Universes

example {Y : SSet.{0}} (x₀ x₁ : Y _⦋0⦌) :
    (∂Δ[1] : SSet.{0}) ⟶ Y :=
  SSet.boundaryOneMap x₀ x₁

example {Y : SSet.{1}} (x₀ x₁ : Y _⦋0⦌) :
    (∂Δ[1] : SSet.{1}) ⟶ Y :=
  SSet.boundaryOneMap x₀ x₁

end Universes

section Surface

#check SSet.boundaryOneMap
#check SSet.boundary_ι_one_boundaryOneMap
#check SSet.boundary_ι_zero_boundaryOneMap

#guard_msgs (error, substring := true) in
#check SSet.boundaryOneLabel

#guard_msgs (error, substring := true) in
#check SSet.boundaryOneLabel_eq

#guard_msgs (error, substring := true) in
#check SSet.twoVertex

end Surface

#print axioms SSet.boundaryOneMap
#print axioms SSet.boundary_ι_one_boundaryOneMap
#print axioms SSet.boundary_ι_zero_boundaryOneMap

end BoundaryOneMapTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
