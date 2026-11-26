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

Let R,S be semirings and n a finite index type, with all types allowed independent universes.
Entrywise coordinate projection identifies Matrix n n(R×S) with Matrix n n R×Matrix n n S as
semirings, and induces GL(n,R×S)≃GL(n,R)×GL(n,S).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Matrix

variable {R R' : Type u} {S S' : Type v}
variable [Semiring R] [Semiring S] [Semiring R'] [Semiring S']

@[simp]
theorem prodRingEquiv_apply_fst (n : Type*) [Fintype n]
    (A : Matrix n n (R × S)) :
    (prodRingEquiv n R S A).1 =
      A.map (RingHom.fst R S) :=
  rfl

@[simp]
theorem prodRingEquiv_apply_snd (n : Type*) [Fintype n]
    (A : Matrix n n (R × S)) :
    (prodRingEquiv n R S A).2 =
      A.map (RingHom.snd R S) :=
  rfl

end Matrix

namespace Matrix.GeneralLinearGroup

variable {R R' : Type u} {S S' : Type v}
variable [Semiring R] [Semiring S] [Semiring R'] [Semiring S']

/-- **Product-semiring general linear group equivalence.**

Let R,S be semirings and n a finite index type. The group equivalence prodSemiringEquiv
n:GL(n,R×S)≃*GL(n,R)×GL(n,S) sends A to (A.map fst,A.map snd); its inverse combines the two
matrices entrywise. Empty indices and independent coefficient universes are included.
-/
def prodSemiringEquiv (n : Type*) [Fintype n] [DecidableEq n] :
    GL n (R × S) ≃* GL n R × GL n S :=
  (Units.mapEquiv (Matrix.prodRingEquiv n R S).toMulEquiv).trans
    MulEquiv.prodUnits

@[simp]
theorem prodEquiv_apply_fst (n : Type*) [Fintype n] [DecidableEq n]
    (A : GL n (R × S)) :
    (prodSemiringEquiv (R := R) (S := S) n A).1 =
      mapRingHom (RingHom.fst R S) A := by
  apply Units.ext
  rfl

@[simp]
theorem prodEquiv_apply_snd (n : Type*) [Fintype n] [DecidableEq n]
    (A : GL n (R × S)) :
    (prodSemiringEquiv (R := R) (S := S) n A).2 =
      mapRingHom (RingHom.snd R S) A := by
  apply Units.ext
  rfl

@[simp]
theorem coe_prodEquiv_symm_apply (n : Type*) [Fintype n] [DecidableEq n]
    (A : GL n R × GL n S) (i j : n) :
    ((↑((prodSemiringEquiv (R := R) (S := S) n).symm A) : Matrix n n (R × S)) i j) =
      ((A.1 : Matrix n n R) i j, (A.2 : Matrix n n S) i j) :=
  rfl

@[simp]
theorem prodEquiv_mapRingHom (n : Type*) [Fintype n] [DecidableEq n]
    (f : R →+* R') (g : S →+* S') (A : GL n (R × S)) :
    prodSemiringEquiv (R := R') (S := S') n (mapRingHom (f.prodMap g) A) =
      (mapRingHom f (prodSemiringEquiv (R := R) (S := S) n A).1,
        mapRingHom g (prodSemiringEquiv (R := R) (S := S) n A).2) := by
  apply Prod.ext <;> apply Units.ext <;> rfl

end Matrix.GeneralLinearGroup
