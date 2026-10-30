/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.Nilpotent

@[expose] public section

universe u

example {R : Type u} [CommRing R] {I : Ideal R} (hI : IsNilpotent I) :
    IsAdicComplete I R :=
  IsAdicComplete.of_isNilpotent hI
