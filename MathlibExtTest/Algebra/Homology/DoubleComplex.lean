/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.DoubleComplex

@[expose] public section

universe u v

-- exactSource consumer with the original binders.
example {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (h : ∀ p q : ℕ, Subsingleton (DoubleComplex.colH D p q)) (n : ℕ) :
    Subsingleton (DoubleComplex.HTot D n) :=
  DoubleComplex.subsingleton_HTot_of_forall_subsingleton_colH D h n

-- Higher-universe consumer.
example {R : Type v} [CommRing R] (D : DoubleComplex.Bounded R)
    (h : ∀ p q : ℕ, Subsingleton (DoubleComplex.colH D p q)) (n : ℕ) :
    Subsingleton (DoubleComplex.HTot D n) :=
  DoubleComplex.subsingleton_HTot_of_forall_subsingleton_colH D h n

-- Boundary: without column vanishing the conclusion can fail; the zero
-- complex shows the hypothesis is sufficient on a concrete instance.
example {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (h : ∀ p q : ℕ, Subsingleton (DoubleComplex.colH D p q)) :
    Subsingleton (DoubleComplex.HTot D 0) :=
  DoubleComplex.subsingleton_HTot_of_forall_subsingleton_colH D h 0
