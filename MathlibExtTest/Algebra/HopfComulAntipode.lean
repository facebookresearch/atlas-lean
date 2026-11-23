/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Algebra.HopfAlgebra.ComulAntipode

@[expose] public section

open scoped TensorProduct

example {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [HopfAlgebra R A] (a : A) :
    Coalgebra.comul (HopfAlgebra.antipode R a)
      = TensorProduct.comm R A A
          (TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R)
            (Coalgebra.comul a)) :=
  HopfAlgebra.comul_antipode a

example {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [HopfAlgebra R A]
    (hcocomm : Coalgebra.IsCocomm R A) (a : A) :
    TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R) (Coalgebra.comul a)
      = Coalgebra.comul (HopfAlgebra.antipode R a) :=
  HopfAlgebra.map_antipode_comul_of_isCocomm hcocomm a
