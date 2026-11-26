/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Algebra.WeilRestriction
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

universe u

open scoped TensorProduct

private theorem exactSource
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B]
    (H : Type u) [CommRing H] [Algebra B H] :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra A W),
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra A T],
          (W →ₐ[A] T) ≃ (H →ₐ[B] (B ⊗[A] T)),
        ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T']
          (u : T →ₐ[A] T') (f : W →ₐ[A] T),
          e T' (u.comp f) =
            (Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f) :=
  Algebra.exists_weilRestriction_points_equiv A B H

-- A concrete consumer over the rationals: the representing algebra
-- exists for the trivial finite free extension.
example : ∃ (W : Type) (_ : CommRing W) (_ : Algebra ℚ W),
    ∃ e : ∀ (T : Type) [CommRing T] [Algebra ℚ T],
        (W →ₐ[ℚ] T) ≃ (Polynomial ℚ →ₐ[ℚ] (ℚ ⊗[ℚ] T)),
      ∀ (T T' : Type) [CommRing T] [Algebra ℚ T] [CommRing T'] [Algebra ℚ T']
        (u : T →ₐ[ℚ] T') (f : W →ₐ[ℚ] T),
        e T' (u.comp f) =
          (Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) u).comp (e T f) :=
  Algebra.exists_weilRestriction_points_equiv ℚ ℚ (Polynomial ℚ)

-- Boundary consumer with a rank-two free extension: `ℚ × ℚ` over `ℚ`.
example : ∃ (W : Type) (_ : CommRing W) (_ : Algebra ℚ W),
    ∃ e : ∀ (T : Type) [CommRing T] [Algebra ℚ T],
        (W →ₐ[ℚ] T) ≃ (Polynomial (ℚ × ℚ) →ₐ[ℚ × ℚ] ((ℚ × ℚ) ⊗[ℚ] T)),
      ∀ (T T' : Type) [CommRing T] [Algebra ℚ T] [CommRing T'] [Algebra ℚ T']
        (u : T →ₐ[ℚ] T') (f : W →ₐ[ℚ] T),
        e T' (u.comp f) =
          (Algebra.TensorProduct.map (AlgHom.id (ℚ × ℚ) (ℚ × ℚ)) u).comp (e T f) :=
  Algebra.exists_weilRestriction_points_equiv ℚ (ℚ × ℚ) (Polynomial (ℚ × ℚ))
