/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosProblem429

/-! # Tests for the refutation of Erdős Problem 429 -/

open MathlibExt.NumberTheory.ErdosProblem429Wanted

-- The refutation applies directly to the stated claim.
example : ¬ erdos429 :=
  erdos429_refuted

-- Any purported witness to the claim is contradictory.
example (h : erdos429) : False :=
  erdos429_refuted h
