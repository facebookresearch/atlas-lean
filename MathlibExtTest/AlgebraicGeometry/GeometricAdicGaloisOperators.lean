/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators

/-! # Tests for Galois and Frobenius operators

The automorphism `id_X × Spec σ` of `X_K` fixes the projection to `X`, is the identity for
`σ = 1`, is compatible with products in the order that makes inverse image a left action, and is
an isomorphism with inverse given by `σ⁻¹`. The geometric Frobenius of `X_K` is the geometric
Frobenius of `X` on the first factor and fixes the second.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.GeometricAdicGaloisOperators

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FrobeniusGeometry
open MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators

universe u

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (K : Type u) [Field K] [Algebra k K]

example (σ : K ≃ₐ[k] K) :
    galoisSchemeOperator X K σ ≫ pullback.fst X.hom (fieldMap k K) =
      pullback.fst X.hom (fieldMap k K) := by
  simp

example : galoisSchemeOperator X K (1 : K ≃ₐ[k] K) = 𝟙 _ := galoisSchemeOperator_one X K

example (σ τ : K ≃ₐ[k] K) :
    galoisSchemeOperator X K (σ * τ) =
      galoisSchemeOperator X K σ ≫ galoisSchemeOperator X K τ :=
  galoisSchemeOperator_mul X K σ τ

example (σ : K ≃ₐ[k] K) :
    (galoisSchemeIso X K σ).hom = galoisSchemeOperator X K σ ∧
      (galoisSchemeIso X K σ).inv = galoisSchemeOperator X K σ⁻¹ :=
  ⟨rfl, rfl⟩

example [Fintype k] (p f : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ f) :
    geometricFrobeniusSchemeOperator X K p f hcard ≫ pullback.fst X.hom (fieldMap k K) =
        pullback.fst X.hom (fieldMap k K) ≫ (geometricFrobenius X p f hcard).left ∧
      geometricFrobeniusSchemeOperator X K p f hcard ≫ pullback.snd X.hom (fieldMap k K) =
        pullback.snd X.hom (fieldMap k K) :=
  ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

example (ell : ℕ) [Fact ell.Prime] (σ : K ≃ₐ[k] K) (n : ℕ) :
    galoisCohomologyOperator X K ell σ n =
      MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality.continuousCohomologyPullback
        ℚ_[ell] (RationalCoefficients.{u} ell) (galoisSchemeOperator X K σ) n :=
  rfl

end MathlibExtTest.AlgebraicGeometry.GeometricAdicGaloisOperators
