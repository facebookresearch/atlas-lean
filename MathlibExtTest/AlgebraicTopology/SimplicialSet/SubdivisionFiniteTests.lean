/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Finite

/-!
# Tests for finiteness of simplicial subdivision

These public-only clients exercise the all-universe finite-subdivision
instance on empty, representable, coproduct, and simplicial-circle boundaries.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace SubdivisionFiniteTests

/-- The generic instance is available at symbolic universe. -/
example (A : SSet.{u}) [A.Finite] : (SSet.sd.obj A).Finite :=
  inferInstance

example (A : SSet.{u}) [A.Finite] : (SSet.sd.obj A).Finite :=
  SSet.finite_sd A

/-- Empty input remains finite after subdivision. -/
example : (SSet.sd.obj (⊥_ SSet.{u})).Finite := inferInstance

/-- Standard-simplex boundaries at symbolic universe. -/
example : (SSet.sd.obj (Δ[0] : SSet.{u})).Finite := inferInstance
example : (SSet.sd.obj (Δ[1] : SSet.{u})).Finite := inferInstance
example : (SSet.sd.obj (Δ[2] : SSet.{u})).Finite := inferInstance

/-- Finite coproduct input. -/
example :
    (SSet.sd.obj ((Δ[0] : SSet.{u}) ⨿ (Δ[1] : SSet.{u}))).Finite :=
  inferInstance

private noncomputable local instance finiteS1 : SSet.Finite SSet.S1 := by
  let F := parallelPair
    (SSet.stdSimplex.δ 0 : Δ[0] ⟶ Δ[1]) (SSet.stdSimplex.δ 1)
  change SSet.Finite (colimit F)
  apply SSet.finite_of_isColimit (colimit.isColimit F)
  intro j
  rcases j with (_ | _) <;> dsimp [F] <;> infer_instance

/-- The simplicial-circle quotient boundary. -/
example : (SSet.sd.obj SSet.S1).Finite := inferInstance

/-- Concrete universe-one and universe-zero clients. -/
example : (SSet.sd.obj (Δ[2] : SSet.{1})).Finite := inferInstance
example : (SSet.sd.obj (Δ[2] : SSet.{0})).Finite := inferInstance

/-- Finiteness does not install arbitrary subdivision nonsingularity. -/
example (A : SSet.{u}) [A.Finite] : True := by
  fail_if_success
    let _ : (SSet.sd.obj A).Nonsingular := inferInstance
  trivial

/-- error: Unknown constant `SSet.regular_sd` -/
#guard_msgs (error, substring := true) in
#check SSet.regular_sd

#print axioms SSet.finite_sd_simplex
#print axioms SSet.finite_sd

end SubdivisionFiniteTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
