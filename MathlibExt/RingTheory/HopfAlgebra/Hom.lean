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
# Bialgebra morphisms commute with antipodes

A bialgebra morphism between Hopf algebras carries the source antipode to
the target antipode. Postcomposition as an algebra morphism and
precomposition as a coalgebra morphism give two convolution inverses of
the same underlying linear map. Native inverse uniqueness identifies them.

The ground semiring is commutative; the source and target semirings may
be noncommutative and have independent carrier universes.
-/

@[expose] public section

open WithConv

namespace BialgHom

universe u v w

variable {R : Type u} [CommSemiring R]
  {A : Type v} [Semiring A] [HopfAlgebra R A]
  {B : Type w} [Semiring B] [HopfAlgebra R B]

/-- The underlying linear map of a bialgebra morphism commutes with the two native antipodes. -/
theorem comp_antipode (f : A →ₐc[R] B) :
    f.toLinearMap.comp (HopfAlgebra.antipode R (A := A)) =
      (HopfAlgebra.antipode R (A := B)).comp f.toLinearMap := by
  have hleft :
      toConv (f.toLinearMap.comp (HopfAlgebra.antipode R (A := A))) *
          toConv f.toLinearMap = (1 : WithConv (A →ₗ[R] B)) := by
    have h := congrArg (f.toAlgHom.convPostcomp (C := A))
      (LinearMap.antipode_mul_id (R := R) (C := A))
    simpa only [map_mul, map_one, AlgHom.convPostcomp,
      WithConv.ofConv_toConv, LinearMap.comp_id] using h
  have hright :
      toConv f.toLinearMap *
          toConv ((HopfAlgebra.antipode R (A := B)).comp f.toLinearMap) =
        (1 : WithConv (A →ₗ[R] B)) := by
    have h := congrArg (f.toCoalgHom.convPrecomp (A := B))
      (LinearMap.id_mul_antipode (R := R) (C := B))
    simpa only [map_mul, map_one, CoalgHom.convPrecomp,
      WithConv.ofConv_toConv, LinearMap.id_comp] using h
  exact toConv_injective (left_inv_eq_right_inv hleft hright)

/-- A bialgebra morphism carries the antipode of each element to the antipode of its image. -/
@[simp]
theorem map_antipode (f : A →ₐc[R] B) (a : A) :
    f (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (f a) :=
  LinearMap.congr_fun f.comp_antipode a

end BialgHom
