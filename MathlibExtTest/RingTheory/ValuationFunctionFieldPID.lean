/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.FunctionFieldPID

@[expose] public section

example {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (O : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ O) (hO : O ≠ ⊤) :
    IsPrincipalIdealRing O :=
  ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin x O hK hO
