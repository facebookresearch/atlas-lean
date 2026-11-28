/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CreekDefs

namespace MetaMathlibExt.Complexity.NPComplete.Creek

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : CreekInstance) :
    creekDec (bitEncode i) = true ↔ WellFormed i ∧ CreekFeasible i := by
  simp [creekDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : creekDec [true] = false := by
  have h : bitDecode (α := CreekInstance) [true] = none := rfl
  simp [creekDec, h]

/-- The decidable `Touches` instance evaluates: the lattice point `(1, 1)` is the lower right
corner of the square `(0, 0)`. -/
example : decide (Touches 1 1 ((⟨0, Nat.one_pos⟩, ⟨0, Nat.one_pos⟩) : Fin 1 × Fin 1)) = true :=
  rfl

/-- The decidable `Touches` instance evaluates: the lattice point `(0, 2)` is not a corner of
the square `(0, 0)`. -/
example :
    decide (Touches 0 2 ((⟨0, Nat.one_pos⟩, ⟨0, Nat.one_pos⟩) : Fin 1 × Fin 1)) = false :=
  rfl

/-- A board of one row and two columns of squares, with a circle numbered `1` on the upper left
lattice point. -/
private abbrev yesBoard : CreekInstance := [[2, 0, 0], [0, 0, 0]]

/-- Coloring the left square blue meets the circle and leaves the right square, a connected
region. -/
example : creekDec (bitEncode yesBoard) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide,
    ({(0, 0)} : Finset (Fin 1 × Fin 2)), by decide, ?_⟩
  show ((SimpleGraph.pathGraph 1 □ SimpleGraph.pathGraph 2).induce
    {x : Fin 1 × Fin 2 | x ∉ ({(0, 0)} : Finset (Fin 1 × Fin 2))}).Connected
  have hv : ∀ u : {x : Fin 1 × Fin 2 | x ∉ ({(0, 0)} : Finset (Fin 1 × Fin 2))},
      u = ⟨(0, 1), by decide⟩ := by
    rintro ⟨⟨a, ⟨_ | _ | b, hb⟩⟩, hu⟩
    · obtain rfl : a = 0 := Subsingleton.elim _ _
      exact absurd (Finset.mem_singleton_self _) hu
    · obtain rfl : a = 0 := Subsingleton.elim _ _
      rfl
    · omega
  have : Nonempty {x : Fin 1 × Fin 2 | x ∉ ({(0, 0)} : Finset (Fin 1 × Fin 2))} :=
    ⟨⟨(0, 1), by decide⟩⟩
  exact ⟨fun u v => by rw [hv u, hv v]⟩

/-- A board of one row and three columns of squares: circles numbered `0` at both upper ends
keep the end squares uncolored, and a circle numbered `1` between them forces the middle square
blue, which cuts the uncolored region in two. -/
private abbrev noBoard : CreekInstance := [[1, 2, 0, 1], [0, 0, 0, 0]]

/-- The circles of `noBoard` force exactly the middle square blue. -/
private theorem forced (blue : Finset (Fin 1 × Fin 3))
    (h : ∀ a < noBoard.length, ∀ b < (noBoard.headD []).length, entry noBoard a b ≠ 0 →
      (blue.filter (Touches a b)).card = entry noBoard a b - 1) :
    blue = {(0, 1)} := by
  revert blue
  decide

/-- Uncolored squares reachable from the left end square stay in the left column. -/
private theorem stuck (u v : {x : Fin 1 × Fin 3 | x ∉ ({(0, 1)} : Finset (Fin 1 × Fin 3))})
    (h : ((SimpleGraph.pathGraph 1 □ SimpleGraph.pathGraph 3).induce
      {x | x ∉ ({(0, 1)} : Finset (Fin 1 × Fin 3))}).Reachable u v)
    (hu : (u.1.2 : ℕ) = 0) : (v.1.2 : ℕ) = 0 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | cons hadj _ ih =>
    apply ih
    rename_i a b _ _
    have hb := b.2
    simp only [SimpleGraph.induce_adj, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]
      at hadj
    rcases hadj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have := a.1.1.isLt; have := b.1.1.isLt; omega
    · have := b.1.2.isLt
      rcases h₁ with h₁ | h₁
      · exfalso; apply hb
        have : b.1 = (0, 1) := Prod.ext (Subsingleton.elim _ _) (Fin.ext (by simp; omega))
        simp [this]
      · omega

/-- The circles of `noBoard` are met only by coloring the middle square, which disconnects
the two end squares. -/
example : creekDec (bitEncode noBoard) = false := by
  cases h : creekDec (bitEncode noBoard) with
  | false => rfl
  | true =>
    obtain ⟨-, blue, hcount, hconn⟩ := (accepts_encoding _).1 h
    have hb := forced blue hcount
    subst hb
    have := stuck ⟨(0, 0), by decide⟩ ⟨(0, 2), by decide⟩ (hconn.preconnected _ _) rfl
    simp at this

end MetaMathlibExt.Complexity.NPComplete.Creek
