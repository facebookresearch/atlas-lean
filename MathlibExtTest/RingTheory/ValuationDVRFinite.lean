/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.DVRFinite

@[expose] public section

example {A K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L]
    (O : ValuationSubring L) (hA : ∀ a : A, algebraMap A L a ∈ O) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O :=
  ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite (K := K) O hA hO
