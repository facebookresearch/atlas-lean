/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The single-coordinate descent proof is adapted from Formal-Math's
`MathlibExtTest/Algebra/Category/ModuleCat/FinsuppCofanTests.lean`.
Author: @toskua
-/

module

import Mathlib.Data.Matrix.Basic
import MathlibExt.Algebra.Category.ModuleCat.FinsuppCofan

/-! # Finite-support descent over a noncommutative ring -/

open CategoryTheory CategoryTheory.Limits

private abbrev R := Matrix (Fin 2) (Fin 2) ℤ

/-- A cocone on two copies of the left regular module with different legs. -/
private noncomputable def firstCofan : Cofan (fun _ : Fin 2 => ModuleCat.of R R) :=
  Cofan.mk (ModuleCat.of R R) fun i => if i = 0 then 𝟙 _ else 0

/-- The descended map keeps the first matrix and discards the second. -/
example (A B : R) :
    ((ModuleCat.finsuppCofanIsColimit R R (Fin 2)).desc firstCofan).hom
      (Finsupp.single 0 A + Finsupp.single 1 B) = A := by
  let h := ModuleCat.finsuppCofanIsColimit R R (Fin 2)
  let desc : (Fin 2 →₀ R) →ₗ[R] R := (h.desc firstCofan).hom
  change desc (Finsupp.single 0 A + Finsupp.single 1 B) = A
  have leg (i : Fin 2) (M : R) :
      desc (Finsupp.single i M) = (firstCofan.inj i).hom M := by
    have eq := h.fac firstCofan (Discrete.mk i)
    with_unfolding_all exact congrArg (fun f => f.hom M) eq
  rw [map_add, leg, leg]
  simp [firstCofan]
  change A + 0 = A
  exact add_zero _
