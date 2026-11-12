/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.MutualInformation

/-- Boundary check: the mutual information of a product law on a
two-point space is `0`, and nonnegativity instantiates. -/
example (p : PMF (Fin 2)) (q : PMF (Fin 2)) :
    mutualInfo (prodJoint p q) = 0 ∧ 0 ≤ mutualInfo (prodJoint p q) :=
  ⟨mutualInfo_prodJoint p q, mutualInfo_nonneg _⟩
