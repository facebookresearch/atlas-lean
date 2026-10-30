/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Order.KrullDimension

@[expose] public section

universe u v

example {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : φ.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R :=
  ringKrullDim_le_of_ringHom_isIntegral φ hφ
