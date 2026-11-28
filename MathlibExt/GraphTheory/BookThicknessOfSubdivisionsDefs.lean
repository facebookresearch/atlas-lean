/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Book embeddings: definitions
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Book embeddings: definitions

Crossing of two edges along a spine order (`IsCrossing`) and `k`-page book embeddings of a simple
graph (`HasBookEmbedding`): the definitions that the statements of
`WantedExt.GraphTheory.BookThicknessOfSubdivisionsWanted`, and of the wanted modules built on it,
use, moved here unchanged (names included) so that their proofs can import them.

Source: F. Bernhart and P. C. Kainen, "The book thickness of a graph", J. Combin. Theory Ser. B 27
(1979), 320-331.
-/

@[expose] public section

namespace MathlibExt.GraphTheory.BookThicknessOfSubdivisionsWanted

/-- Two unordered pairs `e₁ e₂` cross with respect to the spine relation `r`:
    some two distinct endpoints `v ≺ x ≺ w ≺ y` interleave, i.e. `e₁ = {v, w}`
    and `e₂ = {x, y}` with `r v x ∧ r x w ∧ r w y` (or the symmetric pattern
    with the roles of the edges exchanged). -/
def IsCrossing {V : Type} (r : V → V → Prop) (e₁ e₂ : Sym2 V) : Prop :=
  ∃ v w x y : V, v ∈ e₁ ∧ w ∈ e₁ ∧ v ≠ w ∧ x ∈ e₂ ∧ y ∈ e₂ ∧ x ≠ y ∧
    ((r v x ∧ r x w ∧ r w y) ∨ (r x v ∧ r v y ∧ r y w))

/-- A `k`-page book embedding of `G`: a spine embedding plus a (non-proper)
    `k`-colouring of the edges such that same-colour edges never cross. -/
def HasBookEmbedding {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (pos : V → ℕ) (_ : Function.Injective pos) (color : ↥G.edgeSet → Fin k),
    ∀ e₁ e₂ : ↥G.edgeSet,
      IsCrossing (fun a b => pos a < pos b) (↑e₁ : Sym2 V) (↑e₂ : Sym2 V) →
        color e₁ ≠ color e₂

end MathlibExt.GraphTheory.BookThicknessOfSubdivisionsWanted
