/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Zielonka's recursive solver for finite parity games
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Games.Encoded
public import CSLibExt.Computability.Games.Parity

@[expose] public section

namespace Cslib.ZielonkaSolverWanted

open Cslib.Games

/-!
# Zielonka's recursive solver for finite parity games

Zielonka's algorithm solves a finite parity game by recursion on the live
arena `U` (initially the whole arena). Let `d` be the maximal priority on `U`,
let `p` be the player who wins parity `d` (`false` for even, `true` for
odd), let `M` be the positions of `U` with priority `d`, and let `A` be the
attractor of `M` for `p` inside `U`. Solve the subgame on `U' = U \ A`
recursively. If the opponent wins nothing in the subgame, `p` wins all of
`U`. Otherwise, let `B` be the attractor of the opponent's subgame winning
region inside `U`, solve the subgame on `U'' = U \ B` recursively, and give
`B` to the opponent. The recursive calls are on strictly smaller arenas
(`U' ⊂ U` always, since `M` is nonempty; `U'' ⊂ U` in the second case),
so the recurrence is well-founded.

The solver is specified by this recurrence together with the facts that its
outputs lie in `U` and partition `U` — not merely by its correctness. A
function defined as "the winning regions" would satisfy correctness
trivially; the recurrence is what makes this a specification of the
algorithm. Correctness is the final conjunct: on the full arena of a serial
game, the solver's outputs (as `Finset`s, computational data) are exactly
the positional winning regions.

The games are encoded (`EncodedParityGame`: owner as a `Bool`, moves as a
`Bool` matrix), so the solver operates on decidable data and returns
computable `Finset` outputs, unlike the earlier `Set`-valued version.
Subgames keep the same index type `Fin n` with a shrinking live set `U`,
so no subtype juggling is needed.
-/

/-- The Zielonka recursive solver: the pair of winning regions (even, odd)
within the live arena `U`. -/
public def_wanted zielonkaSolve {n : ℕ} (G : EncodedParityGame n)
    (U : Finset (Fin n)) : Finset (Fin n) × Finset (Fin n)

/-- Source: W. Zielonka, "Infinite games on finitely coloured graphs with
applications to automata on infinite trees", *Theoretical Computer Science*
200 (1998), 135-183 (the recursive solver and its correctness). -/
public theorem_wanted zielonka_solver_wanted :
    (∀ {n : ℕ} (G : EncodedParityGame n) (U : Finset (Fin n)),
      (❰zielonkaSolve❱ G U).1 ⊆ U ∧ (❰zielonkaSolve❱ G U).2 ⊆ U) ∧
    (∀ {n : ℕ} (G : EncodedParityGame n) (U : Finset (Fin n)),
      (❰zielonkaSolve❱ G U).1 ∪ (❰zielonkaSolve❱ G U).2 = U ∧
        ((❰zielonkaSolve❱ G U).1 ∩ (❰zielonkaSolve❱ G U).2) = ∅) ∧
    (∀ {n : ℕ} (G : EncodedParityGame n) (U : Finset (Fin n)) (hU : U.Nonempty),
      let d := G.maxPriorityIn U
      let p := decide (d % 2 = 1)
      let M := G.maxPositionsIn U
      let A := G.attractorIn p M U
      let U' := U \ A
      let W' := ❰zielonkaSolve❱ G U'
      let Opp := if p then W'.1 else W'.2
      let B := G.attractorIn (!p) Opp U
      let U'' := U \ B
      let W'' := ❰zielonkaSolve❱ G U''
      (U' ⊂ U) ∧ (Opp ≠ ∅ → U'' ⊂ U) ∧
      (Opp = ∅ → ❰zielonkaSolve❱ G U = (if p then (∅, U) else (U, ∅))) ∧
      (Opp ≠ ∅ → ❰zielonkaSolve❱ G U =
        (W''.1 ∪ (if p then B else ∅), W''.2 ∪ (if p then ∅ else B)))) ∧
    (∀ {n : ℕ} (G : EncodedParityGame n) (hser : ∀ v, ∃ w, G.move v w = true)
      (v : Fin n),
      (v ∈ (❰zielonkaSolve❱ G Finset.univ).1 ↔
        v ∈ (G.toParityGame hser).WinningRegion Player.even) ∧
      (v ∈ (❰zielonkaSolve❱ G Finset.univ).2 ↔
        v ∈ (G.toParityGame hser).WinningRegion Player.odd))

end Cslib.ZielonkaSolverWanted
