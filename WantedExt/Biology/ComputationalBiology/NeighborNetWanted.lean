/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Consistency of Neighbor-Net on circular distances

A split is a bipartition of the finite taxon set `X`; a split-weight
function `ω` is circular if its support is compatible with one circular
ordering `Θ` of `X`, and induces the distance `d_ω`. A distance `d` is
circular if `d = d_ω` for some circular `ω` (the representation is unique).
Neighbor-Net computes an ordering and then a nonnegative least-squares fit;
modeled here as a relation, a run is valid when its ordering is a permutation,
its weights are nonnegative and circular, and no other such weights fit
better. On circular input every valid run recovers the weights, hence the
splits.

Overlap: none found (no Neighbor-Net or Kalmanson module on main).

Sources: D. Bryant, V. Moulton and A. Spillner, "Consistency of the
Neighbor-Net algorithm", Algorithms for Molecular Biology 2:8, 2007,
doi:10.1186/1748-7188-2-8; uniqueness of the circular representation is
Bandelt-Dress (1992), cited there as reference [10].
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.NeighborNetWanted

open Classical

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A split: two blocks partitioning `X`. -/
abbrev Split (X : Type*) := Finset X × Finset X

/-- First block. -/
def blockA (S : Split X) : Finset X := S.1

/-- Second block. -/
def blockB (S : Split X) : Finset X := S.2

/-- Partition into two nonempty blocks. -/
def IsPartition (S : Split X) : Prop :=
  blockA S ∪ blockB S = Finset.univ ∧ Disjoint (blockA S) (blockB S) ∧
    (blockA S).Nonempty ∧ (blockB S).Nonempty

/-- Compatibility with an ordering: some side is a contiguous segment. -/
def IsCompatible (Θ : List X) (S : Split X) : Prop :=
  ∃ i n : ℕ, blockA S = ((Θ.drop i).take n).toFinset ∨
    blockB S = ((Θ.drop i).take n).toFinset

/-- Orderings are duplicate-free and exhaustive. -/
def IsOrdering (Θ : List X) : Prop :=
  Θ.Nodup ∧ Θ.length = Fintype.card X

/-- Split metric: 1 across the split, 0 within each side. -/
def splitDist (S : Split X) (x y : X) : ℝ :=
  if ((x ∈ blockA S ∧ y ∈ blockB S) ∨ (x ∈ blockB S ∧ y ∈ blockA S))
    then 1 else 0

/-- Distance induced by a weight function. -/
noncomputable def weightDist (ω : Split X → ℝ) (x y : X) : ℝ :=
  Finset.sum Finset.univ fun S => ω S * splitDist S x y

/-- Circular weight function for `Θ`: nonnegative, supported compatibly. -/
def IsCircularWeight (Θ : List X) (ω : Split X → ℝ) : Prop :=
  (∀ S, 0 ≤ ω S) ∧ ∀ S, ω S ≠ 0 → IsCompatible Θ S

/-- Circular distance: induced by some circular weight function. -/
def IsCircularDist (d : X → X → ℝ) : Prop :=
  ∃ Θ : List X, ∃ ω : Split X → ℝ, IsOrdering Θ ∧
    IsCircularWeight Θ ω ∧ ∀ x y, d x y = weightDist ω x y

/-- Squared error of weights `φ` against `d` over all ordered pairs. -/
noncomputable def sqError (d : X → X → ℝ) (φ : Split X → ℝ) : ℝ :=
  Finset.sum Finset.univ fun p : X × X =>
    (d p.1 p.2 - weightDist φ p.1 p.2) ^ 2

/-- A valid Neighbor-Net run: permutation ordering, circular nonnegative
weights, and no other circular nonnegative weights fit better (the
nonnegative least-squares condition). -/
def IsNNRun (d : X → X → ℝ) (Θ : List X) (ω : Split X → ℝ) : Prop :=
  IsOrdering Θ ∧ IsCircularWeight Θ ω ∧
    ∀ φ : Split X → ℝ, IsCircularWeight Θ φ → sqError d ω ≤ sqError d φ

/-- **Neighbor-Net consistency** (Bryant-Moulton-Spillner 2007): hypotheses
are a circular distance `d` with circular witness (`Θ₀`, `ω₀`) with
nonnegative weights (`hω₀`), zero diagonal (`hzero`), symmetry (`hsymm`),
and a valid run (`Θ`, `ω`). Conclusions: the run fits exactly
(`d = d_ω`) and recovers the weights (`ω = ω₀`), hence the splits.

Source: Bryant, Moulton and Spillner (2007). -/
theorem_wanted neighborNet_consistent (d : X → X → ℝ)
    (Θ₀ : List X) (ω₀ : Split X → ℝ)
    (hord₀ : IsOrdering Θ₀)
    (hω₀ : IsCircularWeight Θ₀ ω₀)
    (hcirc : ∀ x y, d x y = weightDist ω₀ x y)
    (hzero : ∀ x, d x x = 0)
    (hsymm : ∀ x y, d x y = d y x)
    (Θ : List X) (ω : Split X → ℝ)
    (hrun : IsNNRun d Θ ω) :
    (∀ x y, d x y = weightDist ω x y) ∧ ω = ω₀

end WantedExt.Biology.ComputationalBiology.NeighborNetWanted
