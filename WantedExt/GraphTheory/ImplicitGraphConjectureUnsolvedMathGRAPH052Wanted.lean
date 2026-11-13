/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The implicit graph conjecture

UnsolvedMath seed problem GRAPH-052 (Implicit Graph Conjecture): do slowly-growing hereditary graph
families admit implicit representations? The implicit graph conjecture asserts that every hereditary
family of labeled graphs with at most factorial speed of growth has an implicit representation with
codes of `O(log n)` bits.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Nat.Log
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GraphTheory.ImplicitGraphConjectureUnsolvedMathGRAPH052Wanted

/-!
Source: UnsolvedMath seed problem GRAPH-052 (Implicit Graph Conjecture); the implicit graph
conjecture of S. Kannan, M. Naor and S. Rudich (1988) and J. P. Spinrad (2003), Conjecture 1.3 in H.
Hatami and P. Hatami, arXiv:2111.13198. UnsolvedMath record UM-00001439 (`GRAPH-052`), dataset
ulamai/UnsolvedMath v1.8.0.

Definitions follow Hatami and Hatami, Section 1. A graph family is given by its labeled members `Fₙ`
on the vertex set `Fin n`. Hereditary: closed under the induced subgraph on any injection `Fin m →
Fin n` (this includes isomorphism). At most factorial speed: `|Fₙ| ≤ 2 ^ O(n log n)`, written `|Fₙ|
≤ 2 ^ (c n (⌊log₂ n⌋ + 1))` for all `n`. An efficient implicit representation assigns to the
vertices of each member codes of `O(log n)` bits, here exactly `c (⌊log₂ n⌋ + 1)` bits (shorter
codes can be padded), with a decoder that may depend on the family but not on the graph and that
decides adjacency of two distinct vertices from their codes. The decoder is allowed to depend on
`n`, which only weakens the conjecture, so its refutation is the stronger statement; Hatami and
Hatami's lower bound is proved for this per-`n` notion (no universal graph of the needed size exists
for infinitely many `n`). Polynomial-time computability of the decoder, required in the original
definitions, is dropped, as in Hatami and Hatami. The record's slowly-growing families are those of
at most factorial speed, as in the paper's abstract.
-/

/-- A family of labeled finite graphs: `F n G` says that the graph `G` on the vertex set `Fin n`
belongs to the family (so `F n` is the set `Fₙ` of its `n`-vertex members). -/
abbrev GraphFamily : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

/-- Hereditary: for every injection `σ : Fin m → Fin n` and every member `G` on `Fin n`, the graph
on `Fin m` with `i ~ j` iff `σ i ~ σ j` in `G` is a member (with `m = n` this includes closure
under isomorphism). -/
def IsHereditary (F : GraphFamily) : Prop :=
  ∀ (m n : ℕ) (σ : Fin m ↪ Fin n) (G : SimpleGraph (Fin n)), F n G → F m (G.comap σ)

/-- At most factorial speed of growth: `|Fₙ| ≤ 2 ^ O(n log n)`. -/
def HasFactorialSpeed (F : GraphFamily) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, Nat.card {G : SimpleGraph (Fin n) // F n G} ≤ 2 ^ (c * n * (Nat.log 2 n + 1))

/-- An efficient implicit representation: codes of `O(log n)` bits, here exactly
`c (⌊log₂ n⌋ + 1)` bits, assigned to the vertices of each member, and a decoder that depends on the
family (and on `n`) but not on the graph and decides adjacency of two distinct vertices from their
codes. -/
def HasEfficientImplicitRepresentation (F : GraphFamily) : Prop :=
  ∃ c : ℕ, ∃ decode : ∀ n : ℕ, (Fin (c * (Nat.log 2 n + 1)) → Bool) →
      (Fin (c * (Nat.log 2 n + 1)) → Bool) → Bool,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), F n G →
      ∃ code : Fin n → Fin (c * (Nat.log 2 n + 1)) → Bool,
        ∀ u v : Fin n, u ≠ v → (G.Adj u v ↔ decode n (code u) (code v) = true)

/-- The implicit graph conjecture (Kannan-Naor-Rudich; Spinrad): every hereditary graph family of at
most factorial speed has an efficient implicit representation. -/
def implicitGraphConjecture : Prop :=
  ∀ F : GraphFamily, IsHereditary F → HasFactorialSpeed F → HasEfficientImplicitRepresentation F

/--
Resolved false: Hatami and Hatami (Theorem 1.4) construct, for every `δ > 0`, a hereditary graph
family of at most factorial speed every implicit representation of which needs codes of length
`Ω(n^(1/2 - δ))`, so it has no implicit representation with `O(log n)`-bit codes. Source:
UnsolvedMath seed problem GRAPH-052 (Implicit Graph Conjecture); the implicit graph conjecture of S.
Kannan, M. Naor and S. Rudich (1988) and J. P. Spinrad (2003), Conjecture 1.3 in H. Hatami and P.
Hatami, arXiv:2111.13198; resolution: H. Hatami and P. Hatami, The implicit graph conjecture is
false, 2022 IEEE 63rd Annual Symposium on Foundations of Computer Science (FOCS 2022), 1134-1137;
arXiv:2111.13198, Theorem 1.4: for every δ > 0 there is a hereditary graph family of at most
factorial speed every implicit representation of which needs codes of length Ω(n^(1/2 - δ)),
refuting Conjecture 1.3 (the implicit graph conjecture), https://arxiv.org/abs/2111.13198.
-/
public theorem_wanted implicitGraphConjecture_refuted : ¬ implicitGraphConjecture

end MathlibExt.GraphTheory.ImplicitGraphConjectureUnsolvedMathGRAPH052Wanted
