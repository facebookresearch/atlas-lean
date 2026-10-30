/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.RegularLocalRing.UFD

@[expose] public section

example (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R ≤ 2) : UniqueFactorizationMonoid R :=
  IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two R hdim
