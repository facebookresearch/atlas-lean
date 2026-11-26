/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Discriminant.JacobianSquarePresentation
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.AdjoinRoot

@[expose] public section

open scoped TensorProduct

/-- Consumer with the original binders. -/
example
    {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {A : Type} [CommRing A]
    [Algebra R A] [Module.Free R A] [Module.Finite R A]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A)
    {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    (e : (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) ≃ₐ[R] A) :
    Associated (Algebra.discr R b) (Algebra.norm R (e (Ideal.Quotient.mk _
      (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i)))))) :=
  Algebra.associated_discr_norm_jacobianDet_of_square_presentation b f e

universe u v w in
/-- Consumer in arbitrary universes. -/
example
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] {A : Type v} [CommRing A]
    [Algebra R A] [Module.Free R A] [Module.Finite R A]
    {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A)
    {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    (e : (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) ≃ₐ[R] A) :
    Associated (Algebra.discr R b) (Algebra.norm R (e (Ideal.Quotient.mk _
      (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i)))))) :=
  Algebra.associated_discr_norm_jacobianDet_of_square_presentation b f e

namespace JacobianSquarePresentationTest

open Polynomial

/-- The monic polynomial `X ^ 2 - 2` over `ℤ`. -/
private noncomputable abbrev g : ℤ[X] := X ^ 2 - C 2

private theorem g_monic : g.Monic := monic_X_pow_sub_C 2 two_ne_zero

/-- The one-variable square presentation `X₀ ^ 2 - 2`. -/
private noncomputable abbrev f : Fin 1 → MvPolynomial (Fin 1) ℤ :=
  ![MvPolynomial.X 0 ^ 2 - MvPolynomial.C 2]

/-- `ℤ[X₀] ≃ ℤ[X]`, sending `X₀` to `X`. -/
private noncomputable abbrev φ : MvPolynomial (Fin 1) ℤ ≃ₐ[ℤ] ℤ[X] :=
  MvPolynomial.uniqueAlgEquiv ℤ (Fin 1)

private theorem φ_X : φ (MvPolynomial.X 0) = X := by simp [φ]

private theorem φ_f : φ (f 0) = g := by simp [φ, f, g]

/-- The presentation of `ℤ[X] ⧸ (X ^ 2 - 2)` by `X₀ ^ 2 - 2`. -/
private noncomputable def e :
    (MvPolynomial (Fin 1) ℤ ⧸ Ideal.span (Set.range f)) ≃ₐ[ℤ] AdjoinRoot g :=
  Ideal.quotientEquivAlg _ _ φ (by
    rw [Ideal.map_span, Set.range_unique, Set.image_singleton]
    exact congrArg (fun p => Ideal.span {p}) φ_f.symm)

private theorem e_mk (p : MvPolynomial (Fin 1) ℤ) :
    e (Ideal.Quotient.mk _ p) = AdjoinRoot.mk g (φ p) := rfl

/-- The Jacobian determinant of `X₀ ^ 2 - 2` is `2 X₀`. -/
private theorem jacobian_eq :
    Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i)) = 2 * MvPolynomial.X 0 := by
  rw [Matrix.det_unique, Matrix.of_apply]
  simp only [f, Fin.default_eq_zero, Matrix.cons_val_zero, map_sub, MvPolynomial.pderiv_C,
    sub_zero, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self]
  norm_num

private theorem e_jacobian :
    e (Ideal.Quotient.mk _ (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i)))) =
      2 * AdjoinRoot.root g := by
  rw [jacobian_eq, e_mk, map_mul, map_mul, map_ofNat, map_ofNat, φ_X, AdjoinRoot.mk_X]

/-- A concrete instance meeting every hypothesis: `ℤ[X] ⧸ (X ^ 2 - 2)` over `ℤ`, presented by
`X₀ ^ 2 - 2`, with its power basis `1, X`. The discriminant is associated to the norm of
`2 X`. -/
example : Associated (Algebra.discr ℤ (AdjoinRoot.powerBasis' g_monic).basis)
    (Algebra.norm ℤ (2 * AdjoinRoot.root g)) := by
  have := Module.Free.of_basis (AdjoinRoot.powerBasis' g_monic).basis
  have := (AdjoinRoot.powerBasis' g_monic).finite
  rw [← e_jacobian]
  exact Algebra.associated_discr_norm_jacobianDet_of_square_presentation _ f e

end JacobianSquarePresentationTest
