/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosure
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice

/-!
# The discrete Jordan separation property

`StatMech.Percolation.DiscreteJordanSeparation` states that in the face-boundary graph of a
finite set of sites of `ℤ²`, any face reachable from a face `a` lies on a cycle through `a`. It is
false, already for an isolated face (`StatMech.Percolation.djsf_djs_is_false`); the corrected
variant `StatMech.Percolation.djfx_DiscreteJordanSeparation'` is false as well
(`StatMech.Percolation.not_djfx_DiscreteJordanSeparation'`). The definition is kept as the subject
of these refutations; no theorem assumes it.

## Main definitions

* `StatMech.Percolation.DiscreteJordanSeparation`: the (false) separation property.
-/

@[expose] public section

namespace StatMech

namespace Percolation

open StatMech.Lattice

/-- In the face-boundary graph of every finite `K ⊆ ℤ²`, every face `b` reachable from a face `a`
lies on a cycle based at `a`. False: see `djsf_djs_is_false`. -/
def DiscreteJordanSeparation : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → ∀ {a b : Site 2},
    (faceBoundaryGraph K).Reachable a b →
      ∃ c : (faceBoundaryGraph K).Walk a a, c.IsCycle ∧ b ∈ c.support

end Percolation

end StatMech
