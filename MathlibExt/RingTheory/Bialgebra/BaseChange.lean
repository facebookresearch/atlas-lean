/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/

module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bialgebra scalar extension along a tower

Let R → S → T be compatible algebras of commutative semirings, and A an R-bialgebra with an
arbitrary semiring multiplication. Successive scalar extension T ⊗[S] (S ⊗[R] A) is
canonically isomorphic to T ⊗[R] A as a T-bialgebra.

The comparison sends t ⊗ (s ⊗ a) to (s • t) ⊗ a, and its inverse sends t ⊗ a to t ⊗ (1_S ⊗ a).
Its underlying linear equivalence is tensor-tower cancellation. These maps preserve
multiplication, counit and coproduct and are natural in R-bialgebra maps. The scalar and
bialgebra carrier universes are independent.
-/

@[expose] public section

noncomputable section

open Coalgebra
open scoped BigOperators TensorProduct

namespace Bialgebra.TensorProduct

universe u v w z z'

private theorem comul_baseChange_tmul
    {R : Type u} [CommSemiring R] {S : Type v} [CommSemiring S] [Algebra R S]
    {A : Type z} [AddCommMonoid A] [Module R A] [Coalgebra R A] (s : S) (a : A) :
    Coalgebra.comul (R := S) (s ⊗ₜ[R] a) =
      ∑ i ∈ (ℛ R a).index,
        ((1 : S) ⊗ₜ[R] (ℛ R a).left i) ⊗ₜ[S] (s ⊗ₜ[R] (ℛ R a).right i) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← (ℛ R a).eq]
  simp only [TensorProduct.tmul_sum, map_sum,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]

variable (R : Type u) [CommSemiring R] (S : Type v) [CommSemiring S]
  (T : Type w) [CommSemiring T] [Algebra R S] [Algebra S T] [Algebra R T]
  [IsScalarTower R S T] (A : Type z) [Semiring A] [Bialgebra R A]

private theorem insert_counit_tmul (t : T) (a : A) :
    Coalgebra.counit (R := T)
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A).symm
          (t ⊗ₜ[R] a)) = Coalgebra.counit (R := T) (t ⊗ₜ[R] a) := by
  simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def,
    map_mul, map_one, mul_one, ← IsScalarTower.algebraMap_apply R S T]

private theorem insert_comul_tmul (t : T) (a : A) :
    _root_.TensorProduct.map
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A).symm.toLinearMap
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A).symm.toLinearMap
        (Coalgebra.comul (R := T) (t ⊗ₜ[R] a)) =
      Coalgebra.comul (R := T)
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A).symm
          (t ⊗ₜ[R] a)) := by
  have hinner := comul_baseChange_tmul (R := R) (S := S) (1 : S) a
  rw [comul_baseChange_tmul (R := R) (S := T) t a,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.comul_tmul, CommSemiring.comul_apply, hinner]
  simp only [TensorProduct.tmul_sum, map_sum, _root_.TensorProduct.map_tmul,
    LinearEquiv.coe_toLinearMap,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]

/-- Bialgebra equivalence for successive scalar extension.

For a commutative semiring tower R → S → T and an R-bialgebra semiring A, tensor-tower
cancellation gives T ⊗[S] (S ⊗[R] A) ≃ₐc[T] T ⊗[R] A. No commutativity of A is required. -/
def cancelBaseChange : T ⊗[S] (S ⊗[R] A) ≃ₐc[T] T ⊗[R] A :=
  (BialgEquiv.ofAlgEquiv
    (AlgEquiv.ofLinearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A).symm
      (by simp only [Algebra.TensorProduct.one_def,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul])
      (LinearMap.map_mul_of_map_mul_tmul
        (f := (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A).symm.toLinearMap)
        (fun t t' a a' => by
          simp only [LinearEquiv.coe_toLinearMap,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul])))
    (by
      ext t a
      change Coalgebra.counit (R := T)
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A).symm
            (t ⊗ₜ[R] a)) = Coalgebra.counit (R := T) (t ⊗ₜ[R] a)
      exact insert_counit_tmul R S T A t a)
    (by
      ext t a
      change _root_.TensorProduct.map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A).symm.toLinearMap
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A).symm.toLinearMap
          (Coalgebra.comul (R := T) (t ⊗ₜ[R] a)) =
        Coalgebra.comul (R := T)
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A).symm
            (t ⊗ₜ[R] a))
      exact insert_comul_tmul R S T A t a)).symm

/-- Pure-tensor formula for bialgebra tower cancellation.

For t ∈ T, s ∈ S and a ∈ A, the comparison sends t ⊗[S] (s ⊗[R] a) to (s • t) ⊗[R] a, using
the S-action on T. -/
@[simp]
theorem cancelBaseChange_tmul (t : T) (s : S) (a : A) :
    cancelBaseChange R S T A (t ⊗ₜ[S] (s ⊗ₜ[R] a)) = (s • t) ⊗ₜ[R] a := by
  change (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A)
    (t ⊗ₜ[S] (s ⊗ₜ[R] a)) = _
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S T t a s

/-- Pure-tensor formula for inverse bialgebra tower cancellation.

The inverse comparison sends t ⊗[R] a to t ⊗[S] (1_S ⊗[R] a). -/
@[simp]
theorem cancelBaseChange_symm_tmul (t : T) (a : A) :
    (cancelBaseChange R S T A).symm (t ⊗ₜ[R] a) = t ⊗ₜ[S] ((1 : S) ⊗ₜ[R] a) := by
  change (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A).symm
    (t ⊗ₜ[R] a) = _
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S T t a

/-- Underlying linear equivalence of bialgebra tower cancellation.

The linear equivalence underlying cancelBaseChange is
TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A, with the same coefficient and
unit-insertion formulas. -/
@[simp]
theorem cancelBaseChange_toLinearEquiv :
    (cancelBaseChange R S T A).toCoalgEquiv.toLinearEquiv =
      TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro x
  change cancelBaseChange R S T A x =
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A) x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp only [map_zero]
  · intro t y
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp only [TensorProduct.tmul_zero, map_zero]
    · intro s a
      exact (cancelBaseChange_tmul R S T A t s a).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S T t a s).symm
    · intro y y' hy hy'
      simp only [TensorProduct.tmul_add, map_add, hy, hy']
  · intro x y hx hy
    simp only [map_add, hx, hy]

/-- Naturality of bialgebra tower cancellation.

For an R-bialgebra map f : A → B, direct scalar extension of f after cancelBaseChange on A
equals cancelBaseChange on B after extending f successively along R → S → T. The T and S
coefficient factors are unchanged. -/
theorem cancelBaseChange_naturality
    {B : Type z'} [Semiring B] [Bialgebra R B] (f : A →ₐc[R] B) :
    (Bialgebra.TensorProduct.map (BialgHom.id T T) f).comp
        (cancelBaseChange R S T A).toBialgHom =
      (cancelBaseChange R S T B).toBialgHom.comp
        (Bialgebra.TensorProduct.map (BialgHom.id T T)
          (Bialgebra.TensorProduct.map (BialgHom.id S S) f)) := by
  apply BialgHom.ext
  intro x
  change (Bialgebra.TensorProduct.map (BialgHom.id T T) f) (cancelBaseChange R S T A x) =
    cancelBaseChange R S T B ((Bialgebra.TensorProduct.map (BialgHom.id T T)
      (Bialgebra.TensorProduct.map (BialgHom.id S S) f)) x)
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp only [map_zero]
  · intro t y
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp only [TensorProduct.tmul_zero, map_zero]
    · intro s a
      simp only [Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply, cancelBaseChange_tmul]
    · intro y y' hy hy'
      simp only [TensorProduct.tmul_add, map_add, hy, hy']
  · intro x y hx hy
    simp only [map_add, hx, hy]

end Bialgebra.TensorProduct
