/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FrobeniusDensity

@[expose] public section

open Filter Topology Asymptotics

/-- Exact-source consumer for the degree-one asymptotic statement. -/
theorem exactSource_degOneAsymptotic (L : Type*) [Field L] [NumberField L]
    [IsGalois ℚ L] :
    FrobeniusDensity.DegOneAsymptotic L :=
  FrobeniusDensity.degOneAsymptotic L

/-- Exact-source consumer for the prime-sum logarithmic pole. -/
theorem exactSource_primeSum (K : Type*) [Field K] [NumberField K] :
    (fun s : ℝ => (FrobeniusDensity.primeSum K s).toReal + Real.log (s - 1))
      =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1 : ℝ)) :=
  FrobeniusDensity.primeSum_toReal_add_log_isBigO K
