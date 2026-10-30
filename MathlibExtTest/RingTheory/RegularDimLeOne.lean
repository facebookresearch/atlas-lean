/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Regular.DimLeOne

@[expose] public section

example (A : Type*) [CommRing A] [IsRegularLocalRing A] (h : ringKrullDim A ≤ 1) :
    IsDomain A ∧ IsIntegrallyClosed A :=
  IsRegularLocalRing.isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one A h
