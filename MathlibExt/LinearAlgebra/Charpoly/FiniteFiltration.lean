/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import MathlibExt.LinearAlgebra.Determinant.FiniteFiltration

/-!
# Characteristic polynomials along finite invariant filtrations

This file is the characteristic-polynomial analogue of
`MathlibExt.LinearAlgebra.Determinant.FiniteFiltration`.  It packages and
iterates the characteristic-polynomial factorization for an endomorphism
preserving a submodule, for finite filtrations whose stages and successive
quotients are finite free modules.

## Main declarations

* `LinearMap.charpoly_eq_one_of_subsingleton` computes the characteristic
  polynomial on a zero module.
* `LinearMap.charpoly_eq_charpoly_mul_charpoly` is the raw one-step
  factorization for an invariant submodule, the characteristic-polynomial
  analogue of Mathlib's `LinearMap.det_eq_det_mul_det`.
* `LinearMap.InvariantExtension.charpoly_eq_charpoly_mul_charpoly_quotientMap`
  is the one-step factorization packaged by an invariant extension.
* `LinearMap.charpoly_eq_charpoly_mul_prod_graded` iterates the factorization
  through a finite tower.
* `LinearMap.charpoly_eq_prod_graded_of_bottom_subsingleton` removes the
  bottom factor when the initial stage is zero.

## Informal proof

For one step, choose a basis of the invariant submodule `S` and a basis of
`W / S`, and combine them into a basis of `W` with `Module.Basis.sumQuot`.
Exactly as in Mathlib's proof of `LinearMap.det_eq_det_mul_det`, the matrix
of the endomorphism in this basis is block upper-triangular, with diagonal
blocks the matrices of the restriction and of the quotient map.  The matrix
characteristic polynomial of a block upper-triangular matrix is the product
of the characteristic polynomials of its diagonal blocks
(`Matrix.charpoly_fromBlocks_zero₂₁`), which gives the raw factorization.

The stored intertwining equality in an invariant extension says that the
restriction is conjugate to the lower-stage endomorphism, and characteristic
polynomials are invariant under conjugation, giving the packaged one-step
formula.  The finite-tower formula is then the same `Fin n` induction as in
the determinant file: if `p_{i+1} = p_i * q_i`, then
`p_n = p_0 * ∏ i, q_i`.  When the bottom stage is a zero module, its
characteristic polynomial is `1` (the empty matrix), leaving only the
product over the graded quotients.

The freeness of every successive quotient is explicit, as in the determinant
file: over an arbitrary commutative ring it does not follow merely from
freeness of the two adjacent stages.  The upper stage is also assumed free;
unlike `LinearMap.det`, the characteristic polynomial is only defined on
finite free modules.
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

/-- The characteristic polynomial of an endomorphism of a zero module is
`1`, paralleling `LinearMap.det_eq_one_of_subsingleton`. -/
theorem charpoly_eq_one_of_subsingleton {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] [Subsingleton M]
    (f : M →ₗ[R] M) : f.charpoly = 1 := by
  have b : Module.Basis (Fin 0) R M := Module.Basis.empty M
  rw [← LinearMap.charpoly_toMatrix f b]
  exact Matrix.charpoly_isEmpty

open Module.Basis in
/-- Characteristic-polynomial factorization for an endomorphism preserving
a submodule: the characteristic polynomial is the product of those of the
restriction and of the induced quotient map.  This is the
characteristic-polynomial analogue of `LinearMap.det_eq_det_mul_det`, with
the same block upper-triangular matrix proof. -/
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

/-- Characteristic-polynomial factorization for one invariant extension.

This is the reusable one-step block-triangular formula, the
characteristic-polynomial analogue of
`LinearMap.InvariantExtension.det_eq_det_mul_det_quotientMap`.  The upper
stage is assumed free because `LinearMap.charpoly`, unlike `LinearMap.det`,
is only defined on finite free modules. -/
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

private theorem charpoly_last_eq_first_mul_prod {n : ℕ}
    (d : Fin (n + 1) → R[X]) (q : Fin n → R[X])
    (h : ∀ i, d i.succ = d i.castSucc * q i) :
    d (Fin.last n) = d 0 * ∏ i, q i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprefix :
          d (Fin.castSucc (Fin.last n)) =
            d 0 * ∏ i : Fin n, q i.castSucc := by
        apply ih (d := fun i ↦ d i.castSucc) (q := fun i ↦ q i.castSucc)
        intro i
        simpa using h i.castSucc
      calc
        d (Fin.last (n + 1)) =
            d (Fin.castSucc (Fin.last n)) * q (Fin.last n) := by
          simpa using h (Fin.last n)
        _ = (d 0 * ∏ i : Fin n, q i.castSucc) * q (Fin.last n) := by
          rw [hprefix]
        _ = d 0 * ((∏ i : Fin n, q i.castSucc) * q (Fin.last n)) := by
          rw [mul_assoc]
        _ = d 0 * ∏ i, q i := by
          rw [Fin.prod_univ_castSucc]

section FiniteTower

variable {n : ℕ} {M : Fin (n + 1) → Type v}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]

/-- The characteristic polynomial on the final stage of a finite invariant
filtration is the characteristic polynomial on the initial stage times the
product of the characteristic polynomials on all successive graded
quotients.  This is the characteristic-polynomial analogue of
`LinearMap.det_eq_det_mul_prod_graded`, with the same interface: each
`step i` identifies stage `i` with an invariant submodule of stage `i+1`. -/
theorem charpoly_eq_charpoly_mul_prod_graded
    (endomorphism : ∀ i, M i →ₗ[R] M i)
    (step : ∀ i : Fin n,
      InvariantExtension (endomorphism i.castSucc) (endomorphism i.succ))
    (quotientFree : ∀ i, Module.Free R (M i.succ ⧸ (step i).submodule)) :
    (endomorphism (Fin.last n)).charpoly =
      (endomorphism 0).charpoly * ∏ i, (step i).quotientMap.charpoly := by
  refine charpoly_last_eq_first_mul_prod
    (d := fun i ↦ (endomorphism i).charpoly)
    (q := fun i ↦ (step i).quotientMap.charpoly) ?_
  intro i
  let _ : Module.Free R (M i.succ ⧸ (step i).submodule) := quotientFree i
  exact (step i).charpoly_eq_charpoly_mul_charpoly_quotientMap

/-- Version of `LinearMap.charpoly_eq_charpoly_mul_prod_graded` for a
filtration whose bottom characteristic polynomial has already been
identified with one. -/
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

/-- Characteristic-polynomial product formula for a finite invariant
filtration starting at a zero module. -/
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
