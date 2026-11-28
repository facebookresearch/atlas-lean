/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.YagitDefs

namespace MetaMathlibExt.Complexity.NPComplete.Yagit

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : YagitInstance) :
    yagitDec (bitEncode i) = true ↔ WellFormed i ∧ YagitFeasible i := by
  simp [yagitDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : yagitDec [true] = false := by
  have h : bitDecode (α := YagitInstance) [true] = none := rfl
  simp [yagitDec, h]

/-- A one-by-two grid with the given squares and no black dots. -/
private abbrev pair (a b : ℕ) : YagitInstance := ([[a, b]], [[false, false, false],
  [false, false, false]])

/-- The vertical line between the two squares. -/
private def split (s : Segment) : Bool := decide (s = (false, 0, 1))

private theorem squares (x : Fin (rows (pair 1 2)) × Fin (cols (pair 1 2))) :
    x.1.val = 0 ∧ (x.2.val = 0 ∨ x.2.val = 1) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := x
  simp [rows, cols] at ha hb ⊢
  omega

/-- After drawing the split line, no two squares are joined within a region. -/
private theorem regions_eq (x y : Fin (rows (pair 1 2)) × Fin (cols (pair 1 2)))
    (h : (Regions (pair 1 2) split).Reachable x y) : x = y := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | @cons _ z _ h _ =>
    exfalso
    simp only [Regions, SimpleGraph.deleteEdges_adj, SimpleGraph.boxProd_adj,
      SimpleGraph.pathGraph_adj, Set.mem_ofPred_eq, not_exists, not_and] at h
    obtain ⟨hadj, hnot⟩ := h
    apply hnot x z rfl
    obtain ⟨hx₁, hx₂⟩ := squares x
    obtain ⟨hz₁, hz₂⟩ := squares z
    simp only [split, wall, decide_eq_true_eq]
    rcases hadj with ⟨hr, -⟩ | ⟨hc, -⟩
    · omega
    · rcases hx₂ with hx₂ | hx₂ <;> rcases hz₂ with hz₂ | hz₂ <;>
        simp_all

/-- A sheep and a wolf side by side are separated by one vertical line from border to border. -/
example : yagitDec (bitEncode (pair 1 2)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed rows cols; decide, split, ?_, ?_, ?_⟩
  · rintro p ⟨h₁, h₂, -⟩
    simp [rows] at h₂
    omega
  · rintro s ⟨-, hs⟩
    simp only [split, decide_eq_true_eq] at hs
    subst hs
    exact ⟨_, .refl, (0, 1), by simp [ends], by simp [IsInnerPoint]⟩
  · intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h x =>
      have hsupp : ∀ y, y ∈ ((Regions (pair 1 2) split).connectedComponentMk x).supp ↔ y = x :=
        fun y => ⟨fun hy => regions_eq y x (SimpleGraph.ConnectedComponent.eq.1 hy),
          fun hy => hy ▸ rfl⟩
      simp only [hsupp, exists_eq_left]
      obtain ⟨hx₁, hx₂⟩ := squares x
      rcases hx₂ with hx₂ | hx₂ <;> simp [animal, hx₁, hx₂]

/-- A grid without animals is rejected: whatever lines are drawn, the region of the first square
contains neither a sheep nor a wolf. -/
example : yagitDec (bitEncode (pair 0 0)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, F, -, -, hregion⟩
  obtain ⟨⟨x, -, hx⟩, -⟩ := hregion ((Regions (pair 0 0) F).connectedComponentMk
    (⟨0, by simp [rows]⟩, ⟨0, by simp [cols]⟩))
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := x
  simp [rows, cols] at ha hb
  subst ha
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp [animal] at hx

/-- The rejected instance is well formed, so the rejection comes from the region rule. -/
example : WellFormed (pair 0 0) := by
  unfold WellFormed rows cols
  decide

end MetaMathlibExt.Complexity.NPComplete.Yagit
