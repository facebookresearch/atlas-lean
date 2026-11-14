/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Affine Zariski tangent and addition geometry

Vanishing ideals are intersections of actual evaluation kernels. The
tangent module is the common kernel of the differentials of its defining
polynomials. These definitions retain the scheme-theoretic ideal in
`tangentIdeal`, and use the reduced vanishing ideal in `tangentSet`.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffineTangent

variable {k σ : Type*} [Field k]

/-- The ideal of all polynomials vanishing on the specified point set. -/
def vanishingIdeal (S : Set (σ → k)) : Ideal (MvPolynomial σ k) :=
  ⨅ p : S, RingHom.ker (MvPolynomial.eval p.val)

/-- The actual common zero locus of a polynomial ideal. -/
def zeroLocus (I : Ideal (MvPolynomial σ k)) : Set (σ → k) :=
  {p | ∀ f ∈ I, MvPolynomial.eval p f = 0}

/-- Coordinate definition of Zariski closure over an algebraically closed field. -/
def algebraicClosure (S : Set (σ → k)) : Set (σ → k) :=
  zeroLocus (vanishingIdeal S)

variable [Fintype σ]

/-- The linear differential of a polynomial at an actual affine point. -/
def differential (f : MvPolynomial σ k) (p : σ → k) : (σ → k) →ₗ[k] k where
  toFun v := ∑ i : σ, MvPolynomial.eval p (MvPolynomial.pderiv i f) * v i
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    simp [Finset.mul_sum, mul_left_comm]

/-- The scheme-theoretic tangent module of the specified equations. -/
def tangentIdeal (I : Ideal (MvPolynomial σ k)) (p : σ → k) :
    Submodule k (σ → k) :=
  ⨅ f : I, LinearMap.ker (differential f.val p)

/-- Tangent module of the reduced closed point set. -/
def tangentSet (S : Set (σ → k)) (p : σ → k) : Submodule k (σ → k) :=
  tangentIdeal (vanishingIdeal S) p

/-- Closure of the image of actual vector addition on `X × Y`. -/
def additionImageClosure (X Y : Set (σ → k)) : Set (σ → k) :=
  algebraicClosure {z | ∃ x ∈ X, ∃ y ∈ Y, x + y = z}

end MathlibExt.AlgebraicGeometry.AffineTangent
