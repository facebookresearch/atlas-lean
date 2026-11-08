/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Max
public import MathlibExt.GameTheory.SpragueGrundy

/-!
# Smith's remoteness function

Smith's remoteness of a position of a finite impartial game (`SpragueGrundy.ImpartialGame`):
the length of play when the winner hurries and the loser delays. It is `0` at terminal
positions; otherwise one more than the least even remoteness of an option, if some option has
even remoteness, and one more than the largest remoteness of an option otherwise.
-/

@[expose] public section

namespace MetaMathlibExt.SpragueGrundy

/-- Smith's remoteness function of an impartial game: `0` at terminal positions; otherwise one
more than the least even remoteness of an option, if an option has even remoteness, and one more
than the largest remoteness of an option if every option has odd remoteness.

Source: C. A. B. Smith, *Graphs and composite games*, J. Combin. Theory 1 (1966), 51–81; as
recalled in Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 1.3. -/
noncomputable def smithRemoteness (G : ImpartialGame) : G.Pos → ℕ :=
  (wfRel G).fix fun p ih =>
    let V := (G.moves p).attach.image fun q => ih q.1 q.2
    if hE : (V.filter Even).Nonempty then 1 + (V.filter Even).min' hE
    else if hV : V.Nonempty then 1 + V.max' hV else 0

/-- The defining recursion of `smithRemoteness`.

Source: C. A. B. Smith, *Graphs and composite games*, J. Combin. Theory 1 (1966), 51–81. -/
theorem smithRemoteness_eq (G : ImpartialGame) (p : G.Pos) :
    smithRemoteness G p =
      if hE : (((G.moves p).image (smithRemoteness G)).filter Even).Nonempty then
        1 + (((G.moves p).image (smithRemoteness G)).filter Even).min' hE
      else if hV : ((G.moves p).image (smithRemoteness G)).Nonempty then
        1 + ((G.moves p).image (smithRemoteness G)).max' hV
      else 0 := by
  have key : ∀ f : G.Pos → ℕ,
      ((G.moves p).attach.image fun q => f q.1) = (G.moves p).image f := by
    intro f
    ext v
    simp
  rw [smithRemoteness, WellFounded.fix_eq, key]

/-- A terminal position has remoteness `0`.

Source: C. A. B. Smith, *Graphs and composite games*, J. Combin. Theory 1 (1966), 51–81. -/
theorem smithRemoteness_of_moves_eq_empty (G : ImpartialGame) (p : G.Pos)
    (h : G.moves p = ∅) : smithRemoteness G p = 0 := by
  rw [smithRemoteness_eq]
  simp [h]

end MetaMathlibExt.SpragueGrundy
