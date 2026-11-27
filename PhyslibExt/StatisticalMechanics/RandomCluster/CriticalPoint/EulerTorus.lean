/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EulerGeneral

/-!
# Euler's formula with a torus defect

A combinatorial version of Euler's formula on the torus: the face count is the planar face count
minus a defect `δ ≤ 2`.

## i. Overview

On the torus the planar relation `V - E + F = 1 + c` fails by a defect bounded by `2` (the rank of
the first homology). `IsTorusDefect G δ` records `δ ≤ 2` and `δ ≤ nullity G`; with `torusFaceCount G
δ = faceCount G - δ` this gives `V - E + F = c + 1 - δ`. This is a definitional bookkeeping
statement, not a topological theorem: the defect is an input.

## ii. Key results

- `bet_euler_torus`: `V - E + torusFaceCount = c + 1 - δ` for a torus defect `δ`.
- `bet_euler_torus_planar`: `δ = 0` recovers the planar formula.

## iii. Table of contents

- A. Torus face counts
- B. Euler relations

## iv. References

* V. Beffara, H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster model is
  critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012).
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech.BeffaraDC

variable {V : Type*} [Finite V] [DecidableEq V]

open StatMech.Lattice (nullity faceCount euler_general card_le_edgeSet_add_components)

/-! ## A. Torus face counts -/

/-- The torus face count: the planar face count of `G` minus the defect `δ`. -/
noncomputable def torusFaceCount (G : SimpleGraph V) (δ : ℕ) : ℕ := faceCount G - δ

/-- The admissibility conditions on a torus defect: `δ ≤ 2` and `δ ≤ nullity G`. -/
structure IsTorusDefect (G : SimpleGraph V) (δ : ℕ) : Prop where

  le_two : δ ≤ 2

  le_nullity : δ ≤ nullity G

omit [DecidableEq V] [Finite V] in
lemma bet_torusFaceCount_pos {G : SimpleGraph V} {δ : ℕ} (h : IsTorusDefect G δ) :
    1 ≤ torusFaceCount G δ := by
  unfold torusFaceCount faceCount
  have := h.le_nullity
  omega

omit [DecidableEq V] [Finite V] in
lemma bet_torusFaceCount_eq {G : SimpleGraph V} {δ : ℕ} (h : IsTorusDefect G δ) :
    torusFaceCount G δ = (nullity G - δ) + 1 := by
  unfold torusFaceCount faceCount
  have := h.le_nullity
  omega

/-! ## B. Euler relations -/

omit [DecidableEq V] in
lemma bet_euler_torus {G : SimpleGraph V} {δ : ℕ} (h : IsTorusDefect G δ) :
    (Nat.card V : ℤ) - G.edgeSet.ncard + torusFaceCount G δ
      = Nat.card G.ConnectedComponent + 1 - δ := by
  have hplanar := euler_general G
  have hδ : δ ≤ faceCount G := by
    have := h.le_nullity; unfold faceCount; omega
  have hface : (torusFaceCount G δ : ℤ) = (faceCount G : ℤ) - δ := by
    unfold torusFaceCount
    have : (faceCount G - δ : ℕ) + δ = faceCount G := by omega
    have hcast : ((faceCount G - δ : ℕ) : ℤ) + δ = faceCount G := by exact_mod_cast this
    linarith
  rw [hface]
  linarith

omit [DecidableEq V] in
lemma bet_euler_torus_nat {G : SimpleGraph V} {δ : ℕ} (h : IsTorusDefect G δ) :
    Nat.card V + torusFaceCount G δ + δ
      = G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by
  have hplanar :
      Nat.card V + faceCount G = G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by
    have h := euler_general G
    have hcast : (Nat.card V : ℤ) + (faceCount G : ℤ)
        = (G.edgeSet.ncard : ℤ) + (Nat.card G.ConnectedComponent : ℤ) + 1 := by linarith
    exact_mod_cast hcast
  have hδ : δ ≤ faceCount G := by
    have := h.le_nullity; unfold faceCount; omega
  have hface : torusFaceCount G δ + δ = faceCount G := by
    unfold torusFaceCount; omega
  omega

omit [DecidableEq V] in
lemma bet_euler_torus_planar (G : SimpleGraph V) :
    torusFaceCount G 0 = faceCount G ∧
      (Nat.card V : ℤ) - G.edgeSet.ncard + torusFaceCount G 0
        = Nat.card G.ConnectedComponent + 1 := by
  have hzero : torusFaceCount G 0 = faceCount G := by unfold torusFaceCount; omega
  refine ⟨hzero, ?_⟩
  rw [hzero]
  have := euler_general G; linarith

end StatMech.BeffaraDC
