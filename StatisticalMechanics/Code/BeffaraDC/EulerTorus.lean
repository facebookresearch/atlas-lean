/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
import Code.Lattice.EulerGeneral

open SimpleGraph Set

set_option linter.unusedSectionVars false

namespace StatMech.BeffaraDC

variable {V : Type*} [Finite V] [DecidableEq V]

open StatMech.Lattice (nullity faceCount euler_general euler_general_nat card_le_edgeSet_add_components)









noncomputable def torusFaceCount (G : SimpleGraph V) (δ : ℕ) : ℕ := faceCount G - δ












structure IsTorusDefect (G : SimpleGraph V) (δ : ℕ) : Prop where
  
  le_two : δ ≤ 2
  
  le_nullity : δ ≤ nullity G




theorem bet_torus_defect_le_two {G : SimpleGraph V} {δ : ℕ} (h : IsTorusDefect G δ) :
    δ ≤ 2 := h.le_two




theorem bet_torusFaceCount_pos {G : SimpleGraph V} {δ : ℕ} (h : IsTorusDefect G δ) :
    1 ≤ torusFaceCount G δ := by
  unfold torusFaceCount faceCount
  have := h.le_nullity
  omega




theorem bet_torusFaceCount_eq {G : SimpleGraph V} {δ : ℕ} (h : IsTorusDefect G δ) :
    torusFaceCount G δ = (nullity G - δ) + 1 := by
  unfold torusFaceCount faceCount
  have := h.le_nullity
  omega


















theorem bet_euler_torus {G : SimpleGraph V} {δ : ℕ} (h : IsTorusDefect G δ) :
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



theorem bet_euler_torus_nat {G : SimpleGraph V} {δ : ℕ} (h : IsTorusDefect G δ) :
    Nat.card V + torusFaceCount G δ + δ
      = G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by
  
  have hplanar := euler_general_nat G
  have hδ : δ ≤ faceCount G := by
    have := h.le_nullity; unfold faceCount; omega
  have hface : torusFaceCount G δ + δ = faceCount G := by
    unfold torusFaceCount; omega
  omega





theorem bet_euler_torus_planar (G : SimpleGraph V) :
    torusFaceCount G 0 = faceCount G ∧
      (Nat.card V : ℤ) - G.edgeSet.ncard + torusFaceCount G 0
        = Nat.card G.ConnectedComponent + 1 := by
  have hzero : torusFaceCount G 0 = faceCount G := by unfold torusFaceCount; omega
  refine ⟨hzero, ?_⟩
  rw [hzero]
  have := euler_general G; linarith

end StatMech.BeffaraDC
