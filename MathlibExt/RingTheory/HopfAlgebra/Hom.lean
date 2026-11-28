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

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Hom

/-!
# Antipode compatibility of bialgebra morphisms

Let R be a commutative semiring and A,B Hopf R-algebras with semiring carriers in independent
universes. Every bialgebra morphism f : A → B satisfies f ∘ S_A = S_B ∘ f.

In the convolution monoid of R-linear maps A → B, f ∘ S_A is a left inverse of f and S_B ∘ f
is a right inverse. The algebra and coalgebra compatibility of f give these equations, and
inverse uniqueness identifies the two maps.
-/

@[expose] public section

open WithConv

namespace BialgHom

universe u v w

variable {R : Type u} [CommSemiring R]
  {A : Type v} [Semiring A] [HopfAlgebra R A]
  {B : Type w} [Semiring B] [HopfAlgebra R B]

/-- Linear-map equation for antipode compatibility.

For a bialgebra morphism f between Hopf algebras over a commutative semiring R, f.toLinearMap
∘ S_A = S_B ∘ f.toLinearMap. The source and target semirings may be noncommutative. -/
theorem comp_antipode (f : A →ₐc[R] B) :
    f.toLinearMap.comp (HopfAlgebra.antipode R (A := A)) =
      (HopfAlgebra.antipode R (A := B)).comp f.toLinearMap := by
  have hleft :
      toConv (f.toLinearMap.comp (HopfAlgebra.antipode R (A := A))) *
          toConv f.toLinearMap = (1 : WithConv (A →ₗ[R] B)) := by
    have h := congrArg (f.toAlgHom.convPostcomp (C := A))
      (LinearMap.antipode_mul_id (R := R) (C := A))
    rw [map_mul, map_one] at h
    change toConv (f.toLinearMap.comp (HopfAlgebra.antipode R (A := A))) *
      toConv (f.toLinearMap.comp LinearMap.id) = 1 at h
    simpa only [LinearMap.comp_id] using h
  have hright :
      toConv f.toLinearMap *
          toConv ((HopfAlgebra.antipode R (A := B)).comp f.toLinearMap) =
        (1 : WithConv (A →ₗ[R] B)) := by
    have h := congrArg (f.toCoalgHom.convPrecomp (A := B))
      (LinearMap.id_mul_antipode (R := R) (C := B))
    rw [map_mul, map_one] at h
    change toConv (LinearMap.id.comp f.toLinearMap) *
      toConv ((HopfAlgebra.antipode R (A := B)).comp f.toLinearMap) = 1 at h
    simpa only [LinearMap.id_comp] using h
  exact toConv_injective (left_inv_eq_right_inv hleft hright)

/-- Element formula for a bialgebra morphism and antipodes.

For f : A →ₐc[R] B and a ∈ A, f(S_A(a)) = S_B(f(a)). The ground semiring R is commutative and
both carriers have Hopf structures. -/
@[simp]
theorem map_antipode (f : A →ₐc[R] B) (a : A) :
    f (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (f a) :=
  LinearMap.congr_fun f.comp_antipode a

end BialgHom
