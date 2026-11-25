/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.KrullDimTranscendenceDegree

@[expose] public section

universe u v

-- Consumer with the original binders.
example (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ringKrullDim A = (Cardinal.toENat (Algebra.trdeg k A) : WithBot ℕ∞) :=
  Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k A

-- A field has Krull dimension and transcendence degree zero over itself.
example (k : Type u) [Field k] :
    ringKrullDim k = (Cardinal.toENat (Algebra.trdeg k k) : WithBot ℕ∞) :=
  Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k k

-- One variable over a field gives dimension and transcendence degree one.
example (k : Type u) [Field k] :
    ringKrullDim (MvPolynomial (Fin 1) k) =
      (Cardinal.toENat (Algebra.trdeg k (MvPolynomial (Fin 1) k)) : WithBot ℕ∞) :=
  Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k (MvPolynomial (Fin 1) k)
