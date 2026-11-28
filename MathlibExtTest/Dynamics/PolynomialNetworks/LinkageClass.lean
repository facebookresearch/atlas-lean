/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Dynamics.PolynomialNetworks.LinkageClass

/-! # Linkage classes: a network with a single reaction

The network with the single reaction `A → 0` has one linkage class, so the field of that class
is the whole mass-action field, and the class subspace contains the reaction vector. -/

open MathlibExt.Biology.Dynamics.ComplexBalanced

private def single : ReactionNetwork Unit Unit where
  src := fun _ _ => 1
  prod := fun _ _ => 0

example (k x : Unit → ℝ) :
    single.linkageClassField (single.linkageClassOf ()) k x = single.massActionField k x := by
  funext s
  simp [ReactionNetwork.linkageClassField, ReactionNetwork.massActionField]

example : (fun s => (single.prod () s : ℝ) - single.src () s) ∈
    single.linkageClassStoichiometricSubspace (single.linkageClassOf ()) :=
  Submodule.subset_span ⟨⟨(), rfl⟩, rfl⟩
