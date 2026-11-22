/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

namespace MathlibExt.Geometry.ScottishBook3Wanted

/--
No compact set is congruent to a proper subset of itself. Congruence is rendered
as a distance-preserving map sending the set onto a proper subset of itself;
an isometric embedding of a compact set into itself is surjective, so no such
map exists. Source: S. Banach and S. Ulam, Problem 3 of the Scottish Book,
stated and proved in the Scottish Book typescript.
-/
theorem_wanted noCompactSetCongruentToProperSubset :
    ∀ (α : Type) [MetricSpace α] {K : Set α}, IsCompact K →
      ¬ ∃ (f : α → α), (∀ x y, dist (f x) (f y) = dist x y) ∧ f '' K ⊆ K ∧ f '' K ≠ K

end MathlibExt.Geometry.ScottishBook3Wanted
