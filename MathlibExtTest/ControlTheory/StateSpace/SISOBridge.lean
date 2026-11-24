/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.StateSpace.SISOBridge

open ControlTheory

-- The SISO adapter has the same field and output as the SISO system.
example {n : Type*} [Fintype n]
    (S : MathlibExt.Biology.Dynamics.IntegralFeedback.LinearSystem n)
    (x : n → ℝ) (u : ℝ) :
    (StateSpaceCoeffs.ofSISO S).A x + (StateSpaceCoeffs.ofSISO S).B u
        = MathlibExt.Biology.Dynamics.IntegralFeedback.LinearSystem.field S x u ∧
      (StateSpaceCoeffs.ofSISO S).C x + (StateSpaceCoeffs.ofSISO S).D u
        = MathlibExt.Biology.Dynamics.IntegralFeedback.LinearSystem.output S x u :=
  ⟨StateSpaceCoeffs.ofSISO_field S x u, StateSpaceCoeffs.ofSISO_output S x u⟩

#print axioms StateSpaceCoeffs.ofSISO_field
#print axioms StateSpaceCoeffs.ofSISO_output
