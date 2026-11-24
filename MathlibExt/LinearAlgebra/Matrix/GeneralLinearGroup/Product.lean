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

This file gives the entrywise ring equivalence
`Matrix n n (R × S) ≃+* Matrix n n R × Matrix n n S` and its induced
multiplicative equivalence
`GL n (R × S) ≃* GL n R × GL n S`.

The coefficient rings and finite matrix index may live in independent
universes.  No topology, commutativity, determinant, or K-theory API is used.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Matrix

variable {R R' : Type u} {S S' : Type v}
variable [Semiring R] [Semiring S] [Semiring R'] [Semiring S']

/-- Entrywise equivalence between matrices over a product ring and pairs of
matrices. -/
def prodRingEquiv (n : Type*) [Fintype n] :
    Matrix n n (R × S) ≃+* Matrix n n R × Matrix n n S where
  toFun A := (A.map (RingHom.fst R S), A.map (RingHom.snd R S))
  invFun A i j := (A.1 i j, A.2 i j)
  left_inv A := by
    ext i j <;> rfl
  right_inv A := by
    rcases A with ⟨A, B⟩
    rfl
  map_add' A B := by
    rfl
  map_mul' A B := by
    apply Prod.ext
    · ext i j
      change (RingHom.fst R S) (∑ k, A i k * B k j) =
        ∑ k, (RingHom.fst R S) (A i k) * (RingHom.fst R S) (B k j)
      simp
    · ext i j
      change (RingHom.snd R S) (∑ k, A i k * B k j) =
        ∑ k, (RingHom.snd R S) (A i k) * (RingHom.snd R S) (B k j)
      simp

@[simp]
theorem prodRingEquiv_apply_fst (n : Type*) [Fintype n]
    (A : Matrix n n (R × S)) :
    (prodRingEquiv (R := R) (S := S) n A).1 =
      A.map (RingHom.fst R S) :=
  rfl

@[simp]
theorem prodRingEquiv_apply_snd (n : Type*) [Fintype n]
    (A : Matrix n n (R × S)) :
    (prodRingEquiv (R := R) (S := S) n A).2 =
      A.map (RingHom.snd R S) :=
  rfl

@[simp]
theorem prodRingEquiv_symm_apply (n : Type*) [Fintype n]
    (A : Matrix n n R × Matrix n n S) (i j : n) :
    (prodRingEquiv (R := R) (S := S) n).symm A i j =
      (A.1 i j, A.2 i j) :=
  rfl

end Matrix

namespace Matrix.GeneralLinearGroup

variable {R R' : Type u} {S S' : Type v}
variable [Semiring R] [Semiring S] [Semiring R'] [Semiring S']

/-- Finite general linear groups commute with binary products of rings. -/
def prodEquiv (n : Type*) [Fintype n] [DecidableEq n] :
    GL n (R × S) ≃* GL n R × GL n S :=
  (Units.mapEquiv (Matrix.prodRingEquiv (R := R) (S := S) n).toMulEquiv).trans
    MulEquiv.prodUnits

@[simp]
theorem prodEquiv_apply_fst (n : Type*) [Fintype n] [DecidableEq n]
    (A : GL n (R × S)) :
    (prodEquiv (R := R) (S := S) n A).1 =
      mapRingHom (RingHom.fst R S) A := by
  apply Units.ext
  rfl

@[simp]
theorem prodEquiv_apply_snd (n : Type*) [Fintype n] [DecidableEq n]
    (A : GL n (R × S)) :
    (prodEquiv (R := R) (S := S) n A).2 =
      mapRingHom (RingHom.snd R S) A := by
  apply Units.ext
  rfl

@[simp]
theorem coe_prodEquiv_symm_apply (n : Type*) [Fintype n] [DecidableEq n]
    (A : GL n R × GL n S) (i j : n) :
    ((↑((prodEquiv (R := R) (S := S) n).symm A) : Matrix n n (R × S)) i j) =
      ((A.1 : Matrix n n R) i j, (A.2 : Matrix n n S) i j) :=
  rfl

@[simp]
theorem prodEquiv_mapRingHom (n : Type*) [Fintype n] [DecidableEq n]
    (f : R →+* R') (g : S →+* S') (A : GL n (R × S)) :
    prodEquiv (R := R') (S := S') n (mapRingHom (f.prodMap g) A) =
      (mapRingHom f (prodEquiv (R := R) (S := S) n A).1,
        mapRingHom g (prodEquiv (R := R) (S := S) n A).2) := by
  apply Prod.ext <;> apply Units.ext <;> rfl

end Matrix.GeneralLinearGroup
