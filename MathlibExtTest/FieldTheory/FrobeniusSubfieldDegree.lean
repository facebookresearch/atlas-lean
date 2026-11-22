/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.FrobeniusSubfieldDegree

@[expose] public section

set_option autoImplicit false

/-- Exact-source consumer, using the original binders verbatim. -/
example {K M : Type*} [Field K] [Field M] [Algebra K M] [PerfectField K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (t : M) (htr : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set M)) M] :
    haveI : ExpChar M p := expChar_of_injective_algebraMap (algebraMap K M).injective p
    Module.finrank ↥(frobenius M p).fieldRange M = p :=
  finrank_frobeniusSubfield_eq_of_transcendental p t htr

/-- The same consumer in a higher universe. -/
example {K M : Type 1} [Field K] [Field M] [Algebra K M] [PerfectField K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (t : M) (htr : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set M)) M] :
    haveI : ExpChar M p := expChar_of_injective_algebraMap (algebraMap K M).injective p
    Module.finrank ↥(frobenius M p).fieldRange M = p :=
  finrank_frobeniusSubfield_eq_of_transcendental p t htr
