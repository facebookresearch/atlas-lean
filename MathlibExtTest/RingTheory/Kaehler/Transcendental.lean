/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Kaehler.Transcendental

@[expose] public section

example (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    KaehlerDifferential.D K F x ≠ 0 :=
  KaehlerDifferential.D_ne_zero_of_transcendental K x hx

example (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    Submodule.span F
        ({KaehlerDifferential.D K F x} : Set (KaehlerDifferential K F)) = ⊤ :=
  KaehlerDifferential.span_D_eq_top_of_transcendental K x hx

example (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (ω : KaehlerDifferential K F) :
    ∃! c : F, ω = c • KaehlerDifferential.D K F x :=
  KaehlerDifferential.exists_unique_smul_D_of_transcendental K x hx ω
