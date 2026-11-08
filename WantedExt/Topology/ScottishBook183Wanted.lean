/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace MathlibExt.Topology.ScottishBook183Wanted

/-- Bogolyubov's Problem 183 from the Scottish Book, in its original
form: for every compact, connected, locally connected group of continuous
transformations of `n`-dimensional Euclidean space, coordinates can be
introduced making all the transformations of the group linear, i.e. there
is a homeomorphism `φ` of the space conjugating every group element to a
linear map. -/
def ScottishBookProblem183Claim : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [CompactSpace G] [ConnectedSpace G] [LocallyConnectedSpace G]
    [IsTopologicalGroup G]
    [MulAction G (Fin n → ℝ)] [ContinuousSMul G (Fin n → ℝ)],
    ∃ φ : (Fin n → ℝ) ≃ₜ (Fin n → ℝ), ∀ g : G,
      ∃ L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ), ∀ x, φ (g • x) = L (φ x)

/--
Bogolyubov's Problem 183 is false: a compact, connected, locally
connected group of merely continuous transformations of Euclidean space
need not be linearizable. Linearization (Bochner) requires
differentiability, which is not assumed here. Source: N. N. Bogolyubov,
Problem 183 of the Scottish Book; see the commentary in R. D. Mauldin
(ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted bogolyubov183_refuted : ¬ ScottishBookProblem183Claim

end MathlibExt.Topology.ScottishBook183Wanted
