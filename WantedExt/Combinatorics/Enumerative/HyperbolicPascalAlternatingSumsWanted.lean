/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Complex.Basic
public import MathlibExt.Combinatorics.Enumerative.HyperbolicPascalAlternatingSums
public import MathlibExt.Combinatorics.Enumerative.LinearRecurrenceInhomogeneous

/-!
# Alternating sums in the generalized hyperbolic Pascal triangle

Statements from Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the
Generalized Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84: the identity
relating a linear recurrence `f` and an inhomogeneous recurrence `G` with the same
coefficients (Theorem 1, Corollary 1, quoted from the authors' earlier paper), and the
weighted alternating row sums of the generalized hyperbolic Pascal triangle linked to the
mosaic `{4, q}` (Corollary 2).

The recurrence (10) for the alternating row sums (Theorem 2), its generating function
(Theorem 3) and explicit formula (Theorem 4) are not stated: they fail for simple leg
sequences (see the audit table).
-/
