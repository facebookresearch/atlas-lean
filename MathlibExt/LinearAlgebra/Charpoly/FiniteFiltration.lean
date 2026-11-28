/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/LinearAlgebra/Determinant.lean` (Mathlib):
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import MathlibExt.LinearAlgebra.Determinant.FiniteFiltration

/-!
# Characteristic polynomials along invariant finite filtrations

Let R be a commutative ring and (M_i,f_i)_(i=0)^n a finite tower of finite free modules with
invariant inclusions M_i→M_(i+1). Assume each quotient Q_i is free; it is finite since M_(i+1)
is finite. Let q_i be the induced quotient endomorphism. The factorization is
χ_(f_n)=χ_(f_0)∏_{i<n}χ_(q_i). If M_0=0, only the quotient factors remain. Freeness of the
successive quotients is part of the hypotheses.
-/

@[expose] public section

open scoped BigOperators
open Polynomial

universe u v w

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {V : Type v} {W : Type w}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- **Characteristic polynomial on a zero module.**

Let R be a commutative ring and M a finite free R-module with only the zero element. Every
endomorphism f of M has χ_f=1.

The proof is adapted from Mathlib's `LinearMap.det_eq_one_of_subsingleton` in
`Mathlib/LinearAlgebra/Determinant.lean`.
-/
theorem charpoly_eq_one_of_subsingleton {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] [Subsingleton M]
    (f : M →ₗ[R] M) : f.charpoly = 1 := by
  have b : Module.Basis (Fin 0) R M := Module.Basis.empty M
  rw [← LinearMap.charpoly_toMatrix f b]
  exact Matrix.charpoly_isEmpty

open Module.Basis in
/-- **Characteristic polynomial factors across an invariant submodule.**

Let R be a commutative ring, W a finite free R-module, U⊆W an invariant submodule for f:W→W,
and assume U and W/U are free with U finitely generated. Write f_U,f_Q for the restriction and
quotient endomorphisms. Then χ_f=χ_(f_U)χ_(f_Q).

The proof is adapted from Mathlib's `LinearMap.det_eq_det_mul_det` in
`Mathlib/LinearAlgebra/Determinant.lean`.
-/
theorem charpoly_eq_charpoly_mul_charpoly (e : W →ₗ[R] W) (S : Submodule R W)
    (he : S ≤ S.comap e) [Module.Free R W] [Module.Finite R W]
    [Module.Free R S] [Module.Finite R S] [Module.Free R (W ⧸ S)] :
    e.charpoly = (e.restrict he).charpoly * (S.mapQ S e he).charpoly := by
  let m := Module.Free.ChooseBasisIndex R S
  let bW : Module.Basis m R S := Module.Free.chooseBasis R S
  let n := Module.Free.ChooseBasisIndex R (W ⧸ S)
  let bQ : Module.Basis n R (W ⧸ S) := Module.Free.chooseBasis R (W ⧸ S)
  let b := sumQuot bW bQ
  let A : Matrix m m R := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n R := Matrix.of fun i l ↦
    ((sumQuot bW bQ).repr (e ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n R := LinearMap.toMatrix bQ bQ (S.mapQ S e he)
  suffices LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.charpoly_toMatrix e b, this,
      ← LinearMap.charpoly_toMatrix _ bW, ← LinearMap.charpoly_toMatrix _ bQ,
      Matrix.charpoly_fromBlocks_zero₂₁]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k =>
      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A,
        LinearMap.toMatrix_apply]
      apply sumQuot_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k =>
      suffices S.mkQ (e (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact he (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [← sumQuot_inr bW bQ l, S.mapQ_apply]
      simp

namespace InvariantExtension

variable {f : V →ₗ[R] V} {g : W →ₗ[R] W}

/-- **Characteristic polynomial factorization for an invariant extension.**

Let R be a commutative ring, V,W finite free R-modules with endomorphisms f,g, and E an
invariant extension identifying V with a g-invariant submodule of W and intertwining f with
the restriction. If its quotient Q is free, χ_g=χ_fχ_(E.quotientMap).
-/
theorem charpoly_eq_charpoly_mul_charpoly_quotientMap
    (E : InvariantExtension f g) [Module.Free R V] [Module.Finite R V]
    [Module.Free R W] [Module.Finite R W]
    [Module.Free R (W ⧸ E.submodule)] :
    g.charpoly = f.charpoly * E.quotientMap.charpoly := by
  let _ : Module.Free R E.submodule := Module.Free.of_equiv E.equiv
  let _ : Module.Finite R E.submodule := Module.Finite.equiv E.equiv
  calc
    g.charpoly = (g.restrict E.stable).charpoly * E.quotientMap.charpoly :=
      g.charpoly_eq_charpoly_mul_charpoly E.submodule E.stable
    _ = f.charpoly * E.quotientMap.charpoly := by
      rw [← E.conjugate_eq]
      congr 1
      simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using
        (LinearEquiv.charpoly_conj E.equiv f)

end InvariantExtension

section FiniteTower

variable {n : ℕ} {M : Fin (n + 1) → Type v}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]

/-- **Product formula through an invariant finite tower.**

Let R be a commutative ring and (M_i,f_i)_(i=0)^n a finite tower of finite free modules with
invariant inclusions M_i→M_(i+1). Assume each quotient Q_i is free; it is finite since M_(i+1)
is finite. Let q_i be the induced quotient endomorphism. The final characteristic polynomial
satisfies χ_(f_n)=χ_(f_0)∏_{i<n}χ_(q_i).
-/
theorem charpoly_eq_charpoly_mul_prod_graded
    (endomorphism : ∀ i, M i →ₗ[R] M i)
    (step : ∀ i : Fin n,
      InvariantExtension (endomorphism i.castSucc) (endomorphism i.succ))
    (quotientFree : ∀ i, Module.Free R (M i.succ ⧸ (step i).submodule)) :
    (endomorphism (Fin.last n)).charpoly =
      (endomorphism 0).charpoly * ∏ i, (step i).quotientMap.charpoly := by
  refine Fin.last_eq_first_mul_prod
    (d := fun i ↦ (endomorphism i).charpoly)
    (q := fun i ↦ (step i).quotientMap.charpoly) ?_
  intro i
  let _ : Module.Free R (M i.succ ⧸ (step i).submodule) := quotientFree i
  exact (step i).charpoly_eq_charpoly_mul_charpoly_quotientMap

/-- **Graded characteristic-polynomial product when the bottom factor is one.**

Let R be a commutative ring and (M_i,f_i)_(i=0)^n a finite tower of finite free modules with
invariant inclusions M_i→M_(i+1). Assume each quotient Q_i is free; it is finite since M_(i+1)
is finite. Let q_i be the induced quotient endomorphism. If χ_(f_0)=1, then
χ_(f_n)=∏_{i<n}χ_(q_i).
-/
theorem charpoly_eq_prod_graded_of_bottom_charpoly_eq_one
    (endomorphism : ∀ i, M i →ₗ[R] M i)
    (step : ∀ i : Fin n,
      InvariantExtension (endomorphism i.castSucc) (endomorphism i.succ))
    (quotientFree : ∀ i, Module.Free R (M i.succ ⧸ (step i).submodule))
    (hbottom : (endomorphism 0).charpoly = 1) :
    (endomorphism (Fin.last n)).charpoly =
      ∏ i, (step i).quotientMap.charpoly := by
  rw [charpoly_eq_charpoly_mul_prod_graded endomorphism step quotientFree,
    hbottom, one_mul]

/-- **Graded characteristic-polynomial product from a zero bottom stage.**

Let R be a commutative ring and (M_i,f_i)_(i=0)^n a finite tower of finite free modules with
invariant inclusions M_i→M_(i+1). Assume each quotient Q_i is free; it is finite since M_(i+1)
is finite. Let q_i be the induced quotient endomorphism. If M_0=0, then
χ_(f_n)=∏_{i<n}χ_(q_i).
-/
theorem charpoly_eq_prod_graded_of_bottom_subsingleton
    (endomorphism : ∀ i, M i →ₗ[R] M i)
    (step : ∀ i : Fin n,
      InvariantExtension (endomorphism i.castSucc) (endomorphism i.succ))
    (quotientFree : ∀ i, Module.Free R (M i.succ ⧸ (step i).submodule))
    [Subsingleton (M 0)] :
    (endomorphism (Fin.last n)).charpoly =
      ∏ i, (step i).quotientMap.charpoly :=
  charpoly_eq_prod_graded_of_bottom_charpoly_eq_one endomorphism step
    quotientFree (LinearMap.charpoly_eq_one_of_subsingleton _)

end FiniteTower

end LinearMap
