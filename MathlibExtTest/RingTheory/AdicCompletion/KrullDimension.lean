/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.KrullDimension

@[expose] public section

/-- Exact-source consumer: the original binders and hypotheses. -/
private theorem exactSource
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R) = ringKrullDim R :=
  IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq R

/-- Boundary instance: the equality for a field, whose maximal ideal is zero. -/
example (K : Type*) [Field K] :
    ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal K) K) = ringKrullDim K :=
  IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq K
