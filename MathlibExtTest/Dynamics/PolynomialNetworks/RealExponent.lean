/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Dynamics.PolynomialNetworks.RealExponent

/-! # Real-exponent networks: a reversible pair

The network `(1/2) A ⇌ (3/2) A` is weakly reversible, its reaction vectors span its
stoichiometric subspace, and its complexes are the two half-integer points. -/

open MathlibExt.Biology.Dynamics

private noncomputable def pair : RealExponentNetwork Unit Bool where
  src := fun b _ => if b then 1 / 2 else 3 / 2
  prod := fun b _ => if b then 3 / 2 else 1 / 2

example : pair.IsWeaklyReversible := by
  intro r
  refine Relation.ReflTransGen.single ⟨!r, ?_, ?_⟩ <;> cases r <;> rfl

example (r : Bool) : pair.reactionVector r ∈ pair.stoichiometricSubspace :=
  Submodule.subset_span ⟨r, rfl⟩

example : pair.src true ∈ pair.complexes := Or.inl ⟨true, rfl⟩
