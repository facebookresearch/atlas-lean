/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-!
# Karp reductions on the canonical classes: CLIQUE, INDEPENDENT-SET, VERTEX-COVER

Specification module for SAT ≤ CLIQUE ≤ INDEPENDENT-SET ≤ VERTEX-COVER (Karp 1972) on
`MetaMathlibExt.ComplexityTheory`. It fixes the instance encoding, the languages (through
Mathlib's `SimpleGraph.IsNClique`, `IsNIndepSet`, `IsVertexCover`) and the pure reductions; the
correctness proofs, the machines, and NP membership are separate components.

* Instances `(k, G)` with `G` on `Fin n`: `encodeKG k n bits` is `k` and `n` in unary, then one
  adjacency bit per vertex pair. The pairs are listed by `pairs n`: rows `i` ascending, and within
  a row `j` descending from `n - 1` to `i + 1`, the order in which a machine walking a list of
  vertices backwards meets them. `toGraph n bits` reads the graph off the bits; an instance is
  valid when it has exactly `(pairs n).length` bits.
* `cliqueDec`, `indSetDec`, `vertexCoverDec`: `G` has a clique, an independent set, a vertex cover
  of exactly `k` vertices. These are Sipser's CLIQUE, INDEPENDENT-SET and VERTEX-COVER
  (*Introduction to the Theory of Computation*, 3rd ed., §7.5: "a `k`-node vertex cover").
  Karp's NODE COVER asks for a cover of at most `k` vertices; the two agree when `k ≤ n` (add
  vertices to a smaller cover) and differ only for `k > n`, where the exact form has no cover.
* `toClique φ` (Karp's reduction from SAT): one vertex per literal occurrence (`occs φ`, in
  formula order), two occurrences adjacent when they lie in different clauses and are not
  complementary (`occAdj`), and `k` the number of clauses. `reduceClique` is the reduction on bit
  strings; undecodable input goes to `noKG`, a fixed no-instance.
* `flipKG` complements every pair bit (CLIQUE to INDEPENDENT-SET) and `isToVc` replaces `k` by
  `n - k` (INDEPENDENT-SET to VERTEX-COVER); both parse only the two unary numbers, so they keep
  the bit count and hence validity.
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL

/-- The vertex pairs `(i, j)`, `i < j < n`, in encoding order: rows `i` ascending, within a row
`j` descending. -/
def pairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i => ((List.range n).reverse.filter (i < ·)).map (i, ·)

/-- The bit of the pair `{i, j}` (`false` for pairs without a bit). -/
def adjBits (n : ℕ) (bits : List Bool) (i j : ℕ) : Bool :=
  (((pairs n).zip bits).lookup (min i j, max i j)).getD false

/-- The graph on `Fin n` given by pair bits. -/
def toGraph (n : ℕ) (bits : List Bool) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ adjBits n bits i j = true
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [adjBits, min_comm, max_comm]; exact h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- An instance `(k, G)`: `k` and `n` in unary, then the pair bits. -/
def encodeKG (k n : ℕ) (bits : List Bool) : List Bool :=
  List.replicate k true ++ false :: (List.replicate n true ++ false :: bits)

/-- Parse the two unary numbers; the rest is taken as the pair bits. -/
def decodeKG (x : List Bool) : Option (ℕ × ℕ × List Bool) := do
  let (k, r) ← readUnaryLength x
  let (n, bits) ← readUnaryLength r
  pure (k, n, bits)

/-- A fixed no-instance of all three (exact-size) languages: `k = 1` on the empty graph. -/
def noKG : List Bool := encodeKG 1 0 []

open Classical in
/-- The language of valid instances `(k, G)` satisfying `P k G`. -/
noncomputable def kgDec (P : ∀ n : ℕ, ℕ → SimpleGraph (Fin n) → Prop) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  decide (∃ k n bits, encodeKG k n bits = x ∧ bits.length = (pairs n).length ∧
    P n k (toGraph n bits))

/-- CLIQUE: `G` has a clique of `k` vertices. -/
noncomputable def cliqueDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  kgDec fun _ k G => ∃ s, G.IsNClique k s

/-- INDEPENDENT-SET: `G` has an independent set of `k` vertices. -/
noncomputable def indSetDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  kgDec fun _ k G => ∃ s, G.IsNIndepSet k s

/-- VERTEX-COVER: `G` has a vertex cover of exactly `k` vertices (Sipser's `k`-node vertex
cover; for `k ≤ n` the same as one of at most `k` vertices). -/
noncomputable def vertexCoverDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  kgDec fun n k G => ∃ s : Finset (Fin n), s.card = k ∧ G.IsVertexCover (s : Set (Fin n))

/-- The literal occurrences of a formula in order: clause index, variable, polarity. -/
def occs (φ : CNF) : List (ℕ × ℕ × Bool) :=
  φ.zipIdx.flatMap fun p => p.1.map fun l => (p.2, l.1, l.2)

/-- Two occurrences are adjacent when they lie in different clauses and are not complementary. -/
def occAdj (o o' : ℕ × ℕ × Bool) : Bool :=
  o.1 != o'.1 && !(o.2.1 == o'.2.1 && o.2.2 != o'.2.2)

/-- The pair bits of Karp's graph. -/
def cliqueBits (φ : CNF) : List Bool :=
  (pairs (occs φ).length).map fun p => occAdj ((occs φ).getD p.1 (0, 0, false))
    ((occs φ).getD p.2 (0, 0, false))

/-- Karp's CLIQUE instance of a formula: `k` is the number of clauses. -/
def toClique (φ : CNF) : List Bool := encodeKG φ.length (occs φ).length (cliqueBits φ)

/-- SAT ≤ CLIQUE on bit strings. -/
def reduceClique (x : List Bool) : List Bool :=
  match decodeCNF x with
  | some φ => toClique φ
  | none => noKG

/-- CLIQUE ≤ INDEPENDENT-SET on bit strings: complement every pair bit. -/
def flipKG (x : List Bool) : List Bool :=
  match decodeKG x with
  | some (k, n, bits) => encodeKG k n (bits.map not)
  | none => noKG

/-- INDEPENDENT-SET ≤ VERTEX-COVER on bit strings: `k` becomes `n - k`. -/
def isToVc (x : List Bool) : List Bool :=
  match decodeKG x with
  | some (k, n, bits) => if k ≤ n then encodeKG (n - k) n bits else noKG
  | none => noKG

end Cslib.Complexity.Karp
