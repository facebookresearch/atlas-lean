/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.Noetherian

@[expose] public section

universe u

example {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (AdicCompletion I R) :=
  AdicCompletion.isNoetherianRing_of_isNoetherianRing I
