/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Smooth.NormalDimensionOne

@[expose] public section

universe u v

-- Consumer with the original binders.
example (k : Type u) [Field k] [PerfectField k] (B : Type v) [CommRing B]
    [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsIntegrallyClosed B] [Ring.KrullDimLE 1 B] :
    Algebra.Smooth k B :=
  Algebra.Smooth.of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField k B
