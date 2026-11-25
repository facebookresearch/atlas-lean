/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Discriminant.JacobianSquarePresentation

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
