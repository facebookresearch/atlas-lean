/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import MathlibExt.LinearAlgebra.Charpoly.FiniteFiltration

/-!
# Characteristic polynomials of dependent componentwise endomorphisms

Mathlib's `LinearMap.charpoly_prodMap` computes the characteristic
polynomial of a binary product endomorphism.  This file proves the
dependent-family version over a finite index type: the modules `M i` may
have different ranks, and the characteristic polynomial of the
componentwise endomorphism of `∀ i, M i` is the product of the component
characteristic polynomials.  It is the characteristic-polynomial analogue
of `LinearMap.det_pi_dependent` in
`MathlibExt.LinearAlgebra.Determinant.DependentPi`.

## Main results

* `LinearMap.charpoly_pi_dependent`: the characteristic polynomial of a
  componentwise endomorphism of a finite dependent product is the product
  of the component characteristic polynomials.
* `Algebra.lmul_charpoly_eq_of_algEquiv`: the characteristic polynomial of
  left multiplication is invariant under algebra equivalence, paralleling
  `Algebra.norm_eq_of_algEquiv`.
* `Algebra.lmul_charpoly_pi_apply`: the characteristic polynomial of left
  multiplication by an element of a finite dependent product of algebras
  is the product of the component characteristic polynomials.

## Informal proof

The proof follows the pattern of `Algebra.norm_pi_apply` in
`MathlibExt.RingTheory.Norm.FiniteProduct`, rather than the block-diagonal
matrix computation used for determinants: `Matrix.charpoly`, unlike
`Matrix.det`, takes `DecidableEq` and `Fintype` instance arguments, and
the block-triangular route produces diagonal-block characteristic
polynomials whose fiber instances mix two different `DecidableEq`
sources, which do not unify with synthesized instances.  The induction
route only ever uses the ambient module instances.

For a product indexed by `Fin n`, induct on `n`.  The empty product is a
zero module, so its characteristic polynomial is `1`.  At the successor
step, split a dependent function into its zeroth coordinate and its tail.
Conjugating the componentwise endomorphism by this linear equivalence
gives the binary product of the head endomorphism and the componentwise
tail endomorphism; `LinearMap.charpoly_prodMap`, conjugation invariance,
and the induction hypothesis give the result.  Finally, reindex an
arbitrary finite type by `Fin (Fintype.card ι)`; conjugation invariance
of the characteristic polynomial and invariance of a finite product under
reindexing finish the proof.  Left multiplication on a product algebra
is componentwise by definition, and an algebra equivalence conjugates
left multiplication by `x` to left multiplication by its image, giving
the two algebra corollaries.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Polynomial

universe uR uI uM uK

namespace LinearMap

variable {R : Type uR} [CommRing R]

/-- Split a dependent product over `Fin (n + 1)` into its head and tail
factors, as a linear equivalence. -/
private def piFinSuccLinearEquiv {n : ℕ} (M : Fin (n + 1) → Type uM)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    (∀ i, M i) ≃ₗ[R] M 0 × (∀ i : Fin n, M (Fin.succ i)) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by
    ext
    · exact Fin.cons_zero p.1 p.2
    · exact Fin.cons_succ p.1 p.2 _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Conjugating a componentwise endomorphism over `Fin (n + 1)` by the
head-tail equivalence gives the binary product of the head endomorphism
and the componentwise tail endomorphism. -/
private theorem piFinSuccLinearEquiv_conj_pi {n : ℕ}
    {M : Fin (n + 1) → Type uM} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (f : ∀ i, M i →ₗ[R] M i) :
    (piFinSuccLinearEquiv (R := R) M).conj
        (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))) =
      (f 0).prodMap
        (LinearMap.pi (fun i : Fin n => (f i.succ).comp
          (LinearMap.proj i))) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext
  · rfl
  · funext i
    rfl

/-- The characteristic polynomial of a componentwise endomorphism of a
`Fin n`-indexed dependent product is the product of the component
characteristic polynomials. -/
private theorem charpoly_pi_dependent_fin {n : ℕ} {M : Fin n → Type uM}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
    (f : ∀ i, M i →ₗ[R] M i) :
    (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))).charpoly =
      ∏ i, (f i).charpoly := by
  induction n with
  | zero =>
    have : Subsingleton (∀ i, M i) :=
      ⟨fun _ _ => funext fun i => i.elim0⟩
    rw [LinearMap.charpoly_eq_one_of_subsingleton]
    simp
  | succ n ih =>
    calc
      (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))).charpoly =
          ((piFinSuccLinearEquiv (R := R) M).conj
            (LinearMap.pi (fun i => (f i).comp
              (LinearMap.proj i)))).charpoly :=
        (LinearEquiv.charpoly_conj _ _).symm
      _ = (f 0).charpoly *
            (LinearMap.pi (fun i : Fin n => (f i.succ).comp
              (LinearMap.proj i))).charpoly := by
        rw [piFinSuccLinearEquiv_conj_pi, LinearMap.charpoly_prodMap]
      _ = (f 0).charpoly * ∏ i : Fin n, (f i.succ).charpoly := by
        rw [ih (fun i => f i.succ)]
      _ = ∏ i, (f i).charpoly := by
        rw [Fin.prod_univ_succ]

variable {ι : Type uI} [Fintype ι]
variable {M : ι → Type uM}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]

/-- Characteristic polynomial of a componentwise endomorphism of a finite
dependent product. The component modules may have unequal ranks. -/
theorem charpoly_pi_dependent (f : ∀ i, M i →ₗ[R] M i) :
    (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))).charpoly =
      ∏ i, (f i).charpoly := by
  classical
  let e := Fintype.equivFin ι
  have hconj : (LinearEquiv.piCongrLeft' R M e).conj
        (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))) =
      LinearMap.pi (fun j => (f (e.symm j)).comp (LinearMap.proj j)) := by
    apply LinearMap.ext
    intro g
    obtain ⟨x, rfl⟩ := (LinearEquiv.piCongrLeft' R M e).surjective g
    funext j
    simp [e]
  calc
    (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))).charpoly =
        ((LinearEquiv.piCongrLeft' R M e).conj
          (LinearMap.pi (fun i => (f i).comp
            (LinearMap.proj i)))).charpoly :=
      (LinearEquiv.charpoly_conj _ _).symm
    _ = ∏ j, (f (e.symm j)).charpoly := by
      rw [hconj, charpoly_pi_dependent_fin]
    _ = ∏ i, (f i).charpoly :=
      Fintype.prod_equiv e.symm _ _ (fun _ => rfl)

end LinearMap

namespace Algebra

variable {R : Type uR} [CommRing R]
variable {S : Type uM} {T : Type uK} [Ring S] [Ring T]
variable [Algebra R S] [Algebra R T]
variable [Module.Free R S] [Module.Finite R S]
variable [Module.Free R T] [Module.Finite R T]

/-- The characteristic polynomial of left multiplication is invariant under
algebra equivalence: an algebra equivalence conjugates left multiplication
by `x` to left multiplication by the image of `x`.  This parallels
`Algebra.norm_eq_of_algEquiv`. -/
theorem lmul_charpoly_eq_of_algEquiv (e : S ≃ₐ[R] T) (x : S) :
    (Algebra.lmul R T (e x)).charpoly =
      (Algebra.lmul R S x).charpoly := by
  rw [← LinearEquiv.charpoly_conj e.toLinearEquiv (Algebra.lmul R S x)]
  congr 1
  ext y
  simp [Algebra.coe_lmul_eq_mul]

variable {ι : Type uI} [Fintype ι] {A : ι → Type uM}
variable [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
variable [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]

/-- The characteristic polynomial of left multiplication by an element of a
finite dependent product of algebras is the product of the characteristic
polynomials of left multiplication by its components. -/
theorem lmul_charpoly_pi_apply (q : ∀ i, A i) :
    (Algebra.lmul R (∀ i, A i) q).charpoly =
      ∏ i, (Algebra.lmul R (A i) (q i)).charpoly := by
  classical
  have hmul : Algebra.lmul R (∀ i, A i) q =
      LinearMap.pi (fun i => (Algebra.lmul R (A i) (q i)).comp
        (LinearMap.proj i)) := by
    apply LinearMap.ext
    intro y
    funext i
    rfl
  rw [hmul, LinearMap.charpoly_pi_dependent]

end Algebra

end
