/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.K0.Product
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for algebraic `K₀` of product rings
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicKTheory.RingK0.ProductTests

variable {R S : Type u} [Ring R] [Ring S]

-- The equivalence itself needs neither commutativity nor noetherianity.
example : RingK0 (R × S) ≃+ RingK0 R × RingK0 S :=
  prodEquiv

-- A concrete nontrivial commutative pair.
example : RingK0 (ℤ × ZMod 5) ≃+ RingK0 ℤ × RingK0 (ZMod 5) :=
  prodEquiv

-- The zero ring is an honest factor, with no nontriviality hypothesis.
example : RingK0 (R × PUnit) ≃+ RingK0 R × RingK0 PUnit :=
  prodEquiv

example (X : FGProjectiveCat.{u} (R × S)) :
    prodEquiv (R := R) (S := S) (K0.mk X) =
      (K0.mk ((ProdIdempotent.eComponentFunctorFGP (R := R) (S := S)).obj X),
       K0.mk ((ProdIdempotent.fComponentFunctorFGP (R := R) (S := S)).obj X)) := by
  simp

example (M : FGProjectiveCat.{u} R) (N : FGProjectiveCat.{u} S) :
    (prodEquiv (R := R) (S := S)).symm (K0.mk M, K0.mk N) =
      K0.mk ((FGProjectiveCat.prodEmbeddingFst (R := R) (S := S)).obj M) +
        K0.mk ((FGProjectiveCat.prodEmbeddingSnd (R := R) (S := S)).obj N) := by
  simp

section Naturality

variable {A B A' B' : Type u} [CommRing A] [CommRing B]
  [CommRing A'] [CommRing B']

example (f : A →+* A') (g : B →+* B') :
    (prodEquiv (R := A') (S := B')).toAddMonoidHom.comp
        (RingK0.functor.map (CommRingCat.ofHom (f.prodMap g))).hom.toAddMonoidHom =
      (AddMonoidHom.prodMap
        (RingK0.functor.map (CommRingCat.ofHom f)).hom.toAddMonoidHom
        (RingK0.functor.map (CommRingCat.ofHom g)).hom.toAddMonoidHom).comp
          (prodEquiv (R := A) (S := B)).toAddMonoidHom :=
  prodEquiv_naturality f g

example (f : A →+* A') (g : B →+* B') (x : RingK0 (A × B)) :
    prodEquiv (R := A') (S := B')
        ((RingK0.functor.map (CommRingCat.ofHom (f.prodMap g))) x) =
      ((RingK0.functor.map (CommRingCat.ofHom f))
          (prodEquiv (R := A) (S := B) x).1,
       (RingK0.functor.map (CommRingCat.ofHom g))
          (prodEquiv (R := A) (S := B) x).2) :=
  prodEquiv_naturality_apply f g x

end Naturality

end AlgebraicKTheory.RingK0.ProductTests

end
