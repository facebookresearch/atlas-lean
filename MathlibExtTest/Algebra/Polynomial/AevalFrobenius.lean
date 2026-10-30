/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.AevalFrobenius

@[expose] public section

universe u v

example (F : Type u) [Field F] [Fintype F] (E : Type v) [CommRing E] [Algebra F E]
    (p : Polynomial F) (x : E) :
    Polynomial.aeval (x ^ Fintype.card F) p = (Polynomial.aeval x p) ^ Fintype.card F :=
  Polynomial.aeval_pow_card_eq_pow_card F E p x

example (F : Type (u + 1)) [Field F] [Fintype F] (E : Type) [CommRing E] [Algebra F E]
    (p : Polynomial F) (x : E) :
    Polynomial.aeval (x ^ Fintype.card F) p = (Polynomial.aeval x p) ^ Fintype.card F :=
  Polynomial.aeval_pow_card_eq_pow_card F E p x

example (F : Type) [Field F] [Fintype F] (E : Type (v + 1)) [CommRing E] [Algebra F E]
    (p : Polynomial F) (x : E) :
    Polynomial.aeval (x ^ Fintype.card F) p = (Polynomial.aeval x p) ^ Fintype.card F :=
  Polynomial.aeval_pow_card_eq_pow_card F E p x
