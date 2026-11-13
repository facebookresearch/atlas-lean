/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Positional determinacy of finite parity games (Zielonka)
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Games.Parity

@[expose] public section

namespace Cslib.ParityDeterminacyWanted

open Cslib.Games
open Cslib.Games.ParityGame

/-!
# Positional determinacy of finite parity games (Zielonka)

In a finite parity game with bounded priorities, every position is won by
exactly one player by a positional (memoryless) strategy: the winning regions
of the two players partition the arena. Disjointness of the two winning
regions is proved in `CSLibExt.Computability.Games.Parity`
(`ParityGame.disjoint_winningRegion`); the covering direction, that every
position lies in one of the two regions, is the missing content. It is proved
by Zielonka's induction on priorities, using attractors and traps
(`CSLibExt.Computability.Games.Attractor`).
-/

/-- Source: W. Zielonka, "Infinite games on finitely coloured graphs with
applications to automata on infinite trees", *Theoretical Computer Science*
200 (1998), 135-183 (positional determinacy by induction on priorities). -/
public theorem_wanted parity_positional_determinacy_wanted :
    ∀ {Pos : Type} [Finite Pos] (G : ParityGame Pos) (d : ℕ)
      (hd : ∀ v, G.priority v ≤ d) (v : Pos) (p : Player),
      v ∈ G.WinningRegion p ∨ v ∈ G.WinningRegion p.opponent

end Cslib.ParityDeterminacyWanted
