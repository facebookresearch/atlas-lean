/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Constructions

namespace Equiv.Perm

@[expose] public section

/-- **Pointwise convergence topology on permutations.** For a type $\alpha$, the pointwise
convergence topology on the group of permutations of $\alpha$ is the topology induced by the map
sending a permutation $\sigma$ to the underlying function $\sigma \colon \alpha \to \alpha$, where
$\alpha$ carries the discrete topology and the space of functions $\alpha \to \alpha$ carries the
product topology. -/
noncomputable abbrev pointwiseTopology {α : Type*} : TopologicalSpace (Equiv.Perm α) :=
  letI : TopologicalSpace α := ⊥
  TopologicalSpace.induced (fun σ : Equiv.Perm α => ⇑σ) inferInstance

end

end Equiv.Perm
