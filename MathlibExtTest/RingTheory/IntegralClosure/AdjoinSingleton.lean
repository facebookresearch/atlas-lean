/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.IntegralClosure.AdjoinSingleton

@[expose] public section

-- `exactSource` consumer with the original binders.
example {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] (x : F)
    (hx : Transcendental k x)
    (hfd : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    Module.Finite (Algebra.adjoin k ({x} : Set F))
      (integralClosure (Algebra.adjoin k ({x} : Set F)) F) :=
  Algebra.finite_integralClosure_adjoin_singleton_of_isAlgClosed x hx hfd

-- Higher-universe consumer: the statement is universe-polymorphic.
example {k F : Type 1} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] (x : F)
    (hx : Transcendental k x)
    (hfd : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    Module.Finite (Algebra.adjoin k ({x} : Set F))
      (integralClosure (Algebra.adjoin k ({x} : Set F)) F) :=
  Algebra.finite_integralClosure_adjoin_singleton_of_isAlgClosed x hx hfd

-- Boundary: without finite-dimensionality the conclusion can fail in
-- general; here a transcendental element alone does not give the
-- finite-dimensional hypothesis, witnessed by taking `F = k(x, y)`-style
-- extensions. The hypothesis is therefore not redundant as a formality:
-- the consumer above cannot be applied without supplying it.
example {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] (x : F)
    (hx : Transcendental k x)
    (hfd : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F := hfd
