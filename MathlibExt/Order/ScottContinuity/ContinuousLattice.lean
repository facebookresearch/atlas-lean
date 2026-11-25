/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Data.Fintype.Order

/-!
# Scott's way-below relation and continuous lattices

D. Scott, *Continuous Lattices*, Oxford PRG-7 (1971), §2: in a complete lattice `D` with its
induced (Scott) topology, `x ≺ y` holds when `y` lies in the interior of the principal upper set
of `x`, and `D` is a *continuous lattice* when every element is the supremum of the elements
way below it (Definition 2.3). Mathlib has the Scott topology (`Topology.WithScott`) but neither
notion; this file states them with Scott's definitions, and checks the two-element lattice.
-/

@[expose] public section

namespace MathlibExt.Order.ScottContinuity.ContinuousLattice

open Topology Topology.WithScott Set

variable {D : Type*} [CompleteLattice D]

/-- **Scott's way-below relation.** In a complete lattice `D`, `x ≺ y` when `y` lies in the
interior, for the Scott topology, of the principal upper set `{z | x ≤ z}` (D. Scott, *Continuous
Lattices*, Oxford PRG-7 (1971), §2, definition before Proposition 2.2). -/
def WayBelow (x y : D) : Prop :=
  toScott y ∈ interior {z : WithScott D | x ≤ ofScott z}

/-- **Continuous lattice.** A complete lattice `D` is continuous when every `y ∈ D` is the
supremum of the elements way below it, `y = ⨆ {x | x ≺ y}` (D. Scott, *Continuous Lattices*,
Oxford PRG-7 (1971), Definition 2.3). -/
def IsContinuousLattice (D : Type*) [CompleteLattice D] : Prop :=
  ∀ y : D, y = sSup {x | WayBelow x y}

/-- **The two-element lattice is continuous.** `Bool`, ordered by `false < true`, is a continuous
lattice; it is the simplest instance of Scott's remark that every finite lattice is continuous
(D. Scott, *Continuous Lattices*, Oxford PRG-7 (1971), Proposition 2.8). -/
theorem isContinuousLattice_bool : IsContinuousLattice Bool := by
  have hself : ∀ x : Bool, WayBelow x x := by
    intro x
    refine interior_maximal subset_rfl ?_ (show x ≤ x from le_rfl)
    rw [IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ), dirSupInaccOn_univ]
    refine ⟨fun a b hab ha => le_trans (show x ≤ ofScott a from ha) hab, ?_⟩
    intro d hne _ a ha hxa
    by_contra h
    have hub : ∀ z ∈ d, z ≤ toScott false := by
      intro z hz
      cases hz' : ofScott z
      · exact (show ofScott z ≤ false by rw [hz'])
      · exact absurd ⟨z, hz, (show x ≤ ofScott z by rw [hz']; exact le_top)⟩ h
    have ha' : ofScott a ≤ false := ha.2 hub
    cases x
    · obtain ⟨z, hz⟩ := hne
      exact h ⟨z, hz, show (false : Bool) ≤ ofScott z from bot_le⟩
    · exact absurd (le_trans hxa ha') (by decide)
  intro y
  exact le_antisymm (le_sSup (hself y)) (sSup_le fun x hx => by
    have : toScott y ∈ {z : WithScott Bool | x ≤ ofScott z} := interior_subset hx
    exact this)

end MathlibExt.Order.ScottContinuity.ContinuousLattice
