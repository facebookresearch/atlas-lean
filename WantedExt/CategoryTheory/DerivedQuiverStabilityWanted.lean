/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.DerivedQuiverStability

/-!
# The concrete finite-quiver derived slicing/HN/support comparison

Bridgeland, https://arxiv.org/abs/math/0212237, Proposition2.4,
Proposition5.3 and Example5.5. Positive vertex imaginary parts make this
an actual finite-length-heart stability function. Slicing, numerical
charge and all triangle towers are already fixed constructions, not
freely named predicates. The requested laws include a concrete support
bound and a uniform short window contained in one actual heart shift.
-/

@[expose] public noncomputable section

namespace WantedExt.CategoryTheory.DerivedQuiverStabilityWanted

open MathlibExt.CategoryTheory.DerivedQuiverStability

/-- Vertex charges in the upper half-plane give the stated candidate's HN, phase and support
laws. -/
public theorem_wanted finite_quiver_slicing (k V : Type) [Field k] [Quiver V] [Fintype V]
    (Z : VertexCharges V) : SlicingLaws k Z

end WantedExt.CategoryTheory.DerivedQuiverStabilityWanted
