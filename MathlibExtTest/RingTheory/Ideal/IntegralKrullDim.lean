/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

public import MathlibExt.RingTheory.Ideal.IntegralKrullDim

-- Generic API example: the lemma applies to any integral extension.
example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] : ringKrullDim B ≤ ringKrullDim A :=
  ringKrullDim_le_of_integral

-- Standard specialization: finite dimension bounds transfer along integral extensions.
example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] {n : ℕ} (h : ringKrullDim A ≤ n) :
    ringKrullDim B ≤ n :=
  ringKrullDim_le_of_integral.trans h

-- Every finite chain of prime ideals lifts along an injective integral algebra map.
example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B))
    (p : LTSeries (PrimeSpectrum A)) :
    ∃ q : LTSeries (PrimeSpectrum B),
      q.length = p.length ∧
        List.map (PrimeSpectrum.comap (algebraMap A B)) q.toList = p.toList :=
  exists_ltSeries_of_integral_of_injective hinj p

-- Injectivity gives the reverse inequality, hence equality.
example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim A ≤ ringKrullDim B :=
  ringKrullDim_ge_of_integral_of_injective hinj

example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A :=
  ringKrullDim_eq_of_integral_of_injective hinj

-- A nontrivial integral algebra: the diagonal map into a product preserves dimension.
example (A : Type*) [CommRing A] : ringKrullDim (A × A) = ringKrullDim A :=
  ringKrullDim_eq_of_integral_of_injective
    (FaithfulSMul.algebraMap_injective A (A × A))
