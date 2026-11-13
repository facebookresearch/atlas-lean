/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.CDCL

@[expose] public section

/-- Boundary check: the empty formula admits the empty learned
set in the initial state, and reachability is reflexive. -/
example : CDCLReach (∅ : Finset (Finset Lit)) ([], ∅) ([], ∅) :=
  CDCLReach.refl _

/-- A decide step extends the trail. -/
example : CDCLStep (∅ : Finset (Finset Lit)) ([], ∅)
    ([(0, true)], ∅) :=
  CDCLStep.decide [] ∅ (0, true) (by decide) (by decide)
