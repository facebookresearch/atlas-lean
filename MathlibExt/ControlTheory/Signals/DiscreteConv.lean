/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
public import MathlibExt.Combinatorics.Additive.Convolution

/-!
# Causal finite convolution

For sequences `f g : ℕ → R`, the causal convolution `causalConv`
is the control-theory abbreviation for the canonical sum
convolution `AdditiveCombinatorics.sumConv`. It has no theorem
family of its own: the `sumConv` laws (the range formula
`AdditiveCombinatorics.sumConv_apply`, zero, unit-sample,
commutativity, associativity, and the agreement
`AdditiveCombinatorics.sumConv_eq_addRingConvolution` with
Mathlib's generic discrete convolution) apply to `causalConv`
directly, with the same generality. When rewriting, note that
`rw` does not unfold the abbreviation: use `simp only` with the
`sumConv` lemmas, `exact`, or unfold `causalConv` first.
-/

@[expose] public section

namespace ControlTheory

/-- Causal finite convolution of natural-time sequences: the
control-theory name for the canonical sum convolution
`AdditiveCombinatorics.sumConv`. This is an abbreviation, not a
second definition, and it deliberately has no theorem family of
its own: every `sumConv` law (range formula, zero, unit-sample,
commutativity, associativity, and the agreement with Mathlib's
generic discrete convolution) applies to `causalConv` directly,
with the same generality. -/
abbrev causalConv {R : Type*} [NonUnitalNonAssocSemiring R] (f g : ℕ → R) :
    ℕ → R :=
  AdditiveCombinatorics.sumConv f g

end ControlTheory
