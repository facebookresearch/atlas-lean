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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Map
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Ring.Prod

/-!
# General linear groups over product semirings

Mathlib gives the entrywise ring equivalence
`Matrix n n (R × S) ≃+* Matrix n n R × Matrix n n S` and this file induces the
multiplicative equivalence
`GL n (R × S) ≃* GL n R × GL n S`.

The coefficient rings and finite matrix index may live in independent
universes.  No topology, commutativity, determinant, or K-theory API is used.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Matrix.GeneralLinearGroup

variable {R R' : Type u} {S S' : Type v}
variable [Semiring R] [Semiring S] [Semiring R'] [Semiring S']

/-- Finite general linear groups commute with binary products of rings. -/
def prodSemiringEquiv (n : Type*) [Fintype n] [DecidableEq n] :
    GL n (R × S) ≃* GL n R × GL n S :=
  (Units.mapEquiv (Matrix.prodRingEquiv n R S).toMulEquiv).trans
    MulEquiv.prodUnits

@[simp]
theorem prodSemiringEquiv_apply_fst (n : Type*) [Fintype n] [DecidableEq n]
    (A : GL n (R × S)) :
    (prodSemiringEquiv (R := R) (S := S) n A).1 =
      mapRingHom (RingHom.fst R S) A := by
  apply Units.ext
  rfl

@[simp]
theorem prodSemiringEquiv_apply_snd (n : Type*) [Fintype n] [DecidableEq n]
    (A : GL n (R × S)) :
    (prodSemiringEquiv (R := R) (S := S) n A).2 =
      mapRingHom (RingHom.snd R S) A := by
  apply Units.ext
  rfl

@[simp]
theorem coe_prodSemiringEquiv_symm_apply (n : Type*) [Fintype n] [DecidableEq n]
    (A : GL n R × GL n S) (i j : n) :
    ((↑((prodSemiringEquiv (R := R) (S := S) n).symm A) : Matrix n n (R × S)) i j) =
      ((A.1 : Matrix n n R) i j, (A.2 : Matrix n n S) i j) :=
  rfl

@[simp]
theorem prodSemiringEquiv_mapRingHom (n : Type*) [Fintype n] [DecidableEq n]
    (f : R →+* R') (g : S →+* S') (A : GL n (R × S)) :
    prodSemiringEquiv (R := R') (S := S') n (mapRingHom (f.prodMap g) A) =
      (mapRingHom f (prodSemiringEquiv (R := R) (S := S) n A).1,
        mapRingHom g (prodSemiringEquiv (R := R) (S := S) n A).2) := by
  apply Prod.ext <;> apply Units.ext <;> rfl

end Matrix.GeneralLinearGroup
