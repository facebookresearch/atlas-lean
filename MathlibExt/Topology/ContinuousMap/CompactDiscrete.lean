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
# Compact-open maps into a discrete space

The compact-open topology on continuous maps from a compact space to a
discrete space is discrete.  The result is exposed as a theorem returning the
typeclass; this file deliberately installs no global instance.

## Main declaration

* `ContinuousMap.discreteTopology_of_compact_domain`
-/

@[expose] public section

set_option autoImplicit false

open Set TopologicalSpace

universe u v

namespace ContinuousMap

/-- The compact-open topology on maps from a compact space to a discrete
space is discrete. -/
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
