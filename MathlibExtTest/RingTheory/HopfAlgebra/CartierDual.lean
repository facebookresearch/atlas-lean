/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.HopfAlgebra.CartierDual

@[expose] public section

open scoped TensorProduct

universe u v

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A]

/-- Consumer exercising the Cartier dual with its original binders. -/
private theorem cartierDual_exactSource [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
    (φ ψ : CartierDual R A) (a : A) :
    (φ * ψ) a = TensorProduct.dualDistrib R A A
      (CartierDual.toDual R A φ ⊗ₜ[R] CartierDual.toDual R A ψ) (Coalgebra.comul a) :=
  CartierDual.mul_apply φ ψ a

noncomputable example [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
    [Coalgebra.IsCocomm R A] :
    CommRing (CartierDual R (CartierDual R A)) := inferInstance

noncomputable example [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]
    [Coalgebra.IsCocomm R A] :
    HopfAlgebra R (CartierDual R (CartierDual R A)) := inferInstance

example [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
    (f : A →ₐc[R] A) (φ : CartierDual R A) (a : A) :
    CartierDual.map f φ a = φ (f a) :=
  CartierDual.map_apply f φ a

example [Bialgebra R A] [Module.Finite R A] [Module.Free R A] :
    CartierDual.map (BialgHom.id R A) = BialgHom.id R (CartierDual R A) :=
  CartierDual.map_id

example [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
    (φ : CartierDual R A) (a : A) :
    CartierDual.pairing R A φ a = φ a :=
  CartierDual.pairing_apply R A φ a

example [Bialgebra R A] (a : A) : (1 : CartierDual R A) a = Coalgebra.counit (R := R) a :=
  CartierDual.one_apply a

example [Bialgebra R A] [Module.Finite R A] [Module.Free R A] [Nontrivial R] :
    Module.finrank R (CartierDual R A) = Module.finrank R A :=
  CartierDual.finrank_eq R A
