/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.CompactOpen

/-!
# Discreteness of compact-open maps into discrete spaces

Let X be a compact topological space and Y a discrete topological space,
in independent universes. The compact-open topology on C(X,Y) is discrete.
Empty domains and empty mapping spaces are included.
-/

@[expose] public section

set_option autoImplicit false

open Set TopologicalSpace

universe u v

namespace ContinuousMap

/-- For a compact topological space X and a discrete topological space Y,
the compact-open topology on the continuous mapping space C(X,Y) is discrete. -/
theorem discreteTopology_of_compact_domain
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [DiscreteTopology Y] :
    DiscreteTopology C(X, Y) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro f
  let U : Y → Set C(X, Y) := fun y =>
    {g | MapsTo g (f ⁻¹' {y}) {y}}
  have hrange : (range f).Finite :=
    (isCompact_range f.continuous).finite_of_discrete
  have hU : ∀ y ∈ range f, IsOpen (U y) := by
    intro y _
    exact isOpen_setOfPred_mapsTo
      ((isClosed_singleton.preimage f.continuous).isCompact)
      (isOpen_discrete {y})
  have hopen : IsOpen (⋂ y ∈ range f, U y) :=
    hrange.isOpen_biInter hU
  have heq : (⋂ y ∈ range f, U y) = {f} := by
    ext g
    constructor
    · intro hg
      simp only [mem_iInter] at hg
      have hgf : g = f := by
        ext x
        have hm := hg (f x) ⟨x, rfl⟩ rfl
        simpa using hm
      simp [hgf]
    · intro hgf
      have hgf' : g = f := by simpa using hgf
      subst g
      simp only [mem_iInter]
      intro y _ x hx
      exact hx
  rwa [heq] at hopen

end ContinuousMap
