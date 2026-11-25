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

/-- **Smith's remoteness function.** For an impartial game $G$, the remoteness $R(p)$ of a
position $p$ of $G$ is defined by well-founded recursion along moves; the options of $p$ are the
positions reachable from $p$ in one move. If $p$ has no options, then $R(p) = 0$. Otherwise, if
some option $q$ of $p$ has $R(q)$ even, then $R(p)$ is $1$ plus the least even value of $R(q)$
over the options $q$ of $p$; if every option $q$ of $p$ has $R(q)$ odd, then $R(p)$ is $1$ plus
the largest value of $R(q)$ over the options $q$ of $p$.

Source: C. A. B. Smith, *Graphs and composite games*, J. Combin. Theory 1 (1966), 51–81; as
recalled in Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 1.3. -/
noncomputable def smithRemoteness (G : ImpartialGame) : G.Pos → ℕ :=
  (wfRel G).fix fun p ih =>
    let V := (G.moves p).attach.image fun q => ih q.1 q.2
    if hE : (V.filter Even).Nonempty then 1 + (V.filter Even).min' hE
    else if hV : V.Nonempty then 1 + V.max' hV else 0

/-- **Recursion for Smith's remoteness.** Let $G$ be an impartial game, $p$ a position of $G$, and
$R$ the set of remotenesses of the options of $p$ (the positions reachable from $p$ in one move).
If $R$ contains an even number, the remoteness of $p$ is $1$ plus the least even element of $R$;
otherwise, if $R$ is nonempty, it is $1$ plus the largest element of $R$; and if $R$ is empty,
it is $0$.

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

/-- **Smith's remoteness vanishes at terminal positions.** In an impartial game, the remoteness
of a terminal position (a position with no moves) is $0$.

Source: C. A. B. Smith, *Graphs and composite games*, J. Combin. Theory 1 (1966), 51–81. -/
theorem smithRemoteness_of_moves_eq_empty (G : ImpartialGame) (p : G.Pos)
    (h : G.moves p = ∅) : smithRemoteness G p = 0 := by
  rw [smithRemoteness_eq]
  simp [h]

end MetaMathlibExt.SpragueGrundy
