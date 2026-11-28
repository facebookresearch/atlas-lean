/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Connectedness of the Chabauty space of a group containing ℝ (Kourovka Notebook Problem 8.61)

Kourovka Notebook, Archive of Solved Problems, Problem 8.61 (I. V. Protasov): suppose that a locally
compact group `G` contains a subgroup that is topologically isomorphic to the additive group of the
field of real numbers with natural topology. Is the space of all closed subgroups of `G` connected
in the Chabauty topology?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.Topology.ChabautySpaceDisconnectedRealSubgroup

@[expose] public section

namespace MathlibExt.Topology.ChabautySpaceConnectedRealSubgroupKourovka8Problem61Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.61 (I. V.
Protasov). UnsolvedMath record UM-00700510 (`KOU-8.61`), dataset ulamai/UnsolvedMath v1.8.0.

`G` is a Hausdorff locally compact topological group. The Chabauty topology on the closed subgroups
has the subbase `{H | H ∩ K = ∅}`, `K` compact, and `{H | H ∩ U ≠ ∅}`, `U` open (Protasov's survey,
§1.1). A subgroup topologically isomorphic to `ℝ` is the image of a homomorphism `Multiplicative ℝ
→* G` that is a topological embedding.
-/

end MathlibExt.Topology.ChabautySpaceConnectedRealSubgroupKourovka8Problem61Wanted
