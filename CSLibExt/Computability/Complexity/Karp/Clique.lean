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

/-- **Vertex pairs in encoding order.** For a natural number $n$, the list of all pairs $(i, j)$ of
natural numbers with $i < j < n$, ordered by $i$ ascending and, for each $i$, by $j$ descending
from $n - 1$ to $i + 1$. -/
def pairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i => ((List.range n).reverse.filter (i < ·)).map (i, ·)

/-- **Adjacency bit of a vertex pair.** Let $n$, $i$, $j$ be natural numbers and $b$ a list of
bits. List the pairs $(i', j')$ with $i' < j' < n$ in encoding order ($i'$ ascending and, for
each $i'$, $j'$ descending) and match the $t$-th pair with the $t$-th bit of $b$, for as many
positions as both lists have. The adjacency bit of $\{i, j\}$ is the bit matched with
$(\min(i, j), \max(i, j))$, and false when that pair has no matched bit (for instance when
$i = j$, when $\max(i, j) \ge n$, or when $b$ is too short). -/
def adjBits (n : ℕ) (bits : List Bool) (i j : ℕ) : Bool :=
  (((pairs n).zip bits).lookup (min i j, max i j)).getD false

/-- **The graph encoded by pair bits.** List the pairs $(i, j)$ of natural numbers with
$i < j < n$ by $i$ ascending and, for each $i$, by $j$ descending, and give the $t$-th pair the
$t$-th bit of a list of bits. The simple graph on the vertex set $\{0, \dots, n - 1\}$ given by
the list makes two vertices $i < j$ adjacent when the bit of $(i, j)$ is true; a pair left
without a bit because the list is too short is not an edge, and bits beyond the last pair are
ignored. -/
def toGraph (n : ℕ) (bits : List Bool) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ adjBits n bits i j = true
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [adjBits, min_comm, max_comm]; exact h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- **Encoding of a graph instance.** For natural numbers $k$, $n$ and a list of bits $b$, the
encoding is $1^k\,0\,1^n\,0\,b$, writing $1$ for true and $0$ for false: $k$ ones, a zero,
$n$ ones, a zero, and then $b$. Here $k$ is the target size and $b$ lists the pair bits of a
graph on $n$ vertices. -/
def encodeKG (k n : ℕ) (bits : List Bool) : List Bool :=
  List.replicate k true ++ false :: (List.replicate n true ++ false :: bits)

/-- **Decoding a graph instance.** Writing $1$ for true and $0$ for false, a bit string of the
form $1^k\,0\,1^n\,0\,b$ with natural numbers $k$, $n$ and a list of bits $b$ decodes to the
triple $(k, n, b)$. A bit string with fewer than two zeros does not decode. -/
def decodeKG (x : List Bool) : Option (ℕ × ℕ × List Bool) := do
  let (k, r) ← readUnaryLength x
  let (n, bits) ← readUnaryLength r
  pure (k, n, bits)

/-- **Fixed no-instance.** The bit string $1\,0\,0$ (writing $1$ for true and $0$ for false),
which encodes $k = 1$ together with the graph with no vertices ($n = 0$ and no pair bits).

A graph with no vertices has no clique, independent set or vertex cover of exactly one vertex,
so this string lies in none of CLIQUE, INDEPENDENT-SET and VERTEX-COVER. -/
def noKG : List Bool := encodeKG 1 0 []

open Classical in
/-- **Language of graph instances with a property.** Let $P$ be a property of a natural number
$n$, a natural number $k$ and a simple graph on $\{0, \dots, n-1\}$. The decision problem accepts
a bit string $x$ exactly when, writing $1$ for true and $0$ for false, $x = 1^k\,0\,1^n\,0\,b$
for some natural numbers $k$, $n$ and a list of bits $b$ with one entry for each pair
$i < j < n$, such that $P$ holds of $n$, $k$ and the graph on $\{0, \dots, n-1\}$ given by $b$.
In that graph, distinct $i$ and $j$ are adjacent when the bit of the pair $\{i, j\}$ is true,
the pairs being listed with $i$ ascending and, for each $i$, $j$ descending. -/
noncomputable def kgDec (P : ∀ n : ℕ, ℕ → SimpleGraph (Fin n) → Prop) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  decide (∃ k n bits, encodeKG k n bits = x ∧ bits.length = (pairs n).length ∧
    P n k (toGraph n bits))

/-- **CLIQUE.** The decision problem CLIQUE accepts a bit string $x$ exactly when, writing $1$
for true and $0$ for false, $x = 1^k\,0\,1^n\,0\,b$ for some natural numbers $k$, $n$ and a list
of bits $b$ with one entry for each pair $i < j < n$, such that the graph on
$\{0, \dots, n-1\}$ given by $b$ has a clique of exactly $k$ vertices. In that graph, distinct
$i$ and $j$ are adjacent when the bit of the pair $\{i, j\}$ is true, the pairs being listed
with $i$ ascending and, for each $i$, $j$ descending. -/
noncomputable def cliqueDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  kgDec fun _ k G => ∃ s, G.IsNClique k s

/-- **INDEPENDENT-SET.** The decision problem INDEPENDENT-SET accepts a bit string $x$ exactly
when, writing $1$ for true and $0$ for false, $x = 1^k\,0\,1^n\,0\,b$ for some natural numbers
$k$, $n$ and a list of bits $b$ with one entry for each pair $i < j < n$, such that the graph on
$\{0, \dots, n-1\}$ given by $b$ has an independent set of exactly $k$ vertices. In that graph,
distinct $i$ and $j$ are adjacent when the bit of the pair $\{i, j\}$ is true, the pairs being
listed with $i$ ascending and, for each $i$, $j$ descending. -/
noncomputable def indSetDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  kgDec fun _ k G => ∃ s, G.IsNIndepSet k s

/-- **The VERTEX-COVER problem.** The decision problem that accepts a bit string exactly when it
encodes an instance $(k, G)$, where $G$ is a simple graph on $n$ vertices, and $G$ has a vertex
cover of exactly $k$ vertices. The encoding is $k$ ones, a zero, $n$ ones, a zero, then one bit
for each pair $(i, j)$ with $i < j < n$, listed by $i$ ascending and, for each $i$, by $j$
descending, a true bit meaning that $i$ and $j$ are adjacent; a string with any other number of
pair bits is rejected.

This is Sipser's $k$-node vertex cover; for $k \le n$ it is the same as a cover of at most $k$
vertices. -/
noncomputable def vertexCoverDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  kgDec fun n k G => ∃ s : Finset (Fin n), s.card = k ∧ G.IsVertexCover (s : Set (Fin n))

/-- **Literal occurrences of a CNF formula.** For a CNF formula $\varphi$ with clauses
$C_0, \dots, C_{m-1}$, the list of triples $(i, x, b)$, one for each literal $(x, b)$ of each
clause $C_i$, where $x$ is the variable index and $b$ the polarity. The triples are listed clause
by clause in order of $i$, and within a clause in the order of its literals. -/
def occs (φ : CNF) : List (ℕ × ℕ × Bool) :=
  φ.zipIdx.flatMap fun p => p.1.map fun l => (p.2, l.1, l.2)

/-- **Adjacency of literal occurrences in Karp's clique graph.** A literal occurrence is a triple
$(c, x, b)$ of a clause index $c$, a variable index $x$ and a polarity $b$. Two occurrences
$(c, x, b)$ and $(c', x', b')$ are adjacent when $c \ne c'$ and they are not complementary, that
is, it is not the case that $x = x'$ and $b \ne b'$. -/
def occAdj (o o' : ℕ × ℕ × Bool) : Bool :=
  o.1 != o'.1 && !(o.2.1 == o'.2.1 && o.2.2 != o'.2.2)

/-- **Adjacency bits of Karp's clique graph.** For a CNF formula $\varphi$, list its literal
occurrences $o_0, \dots, o_{m-1}$ in formula order, each recorded by its clause index, its
variable and its polarity. The result has one bit for each pair $(i, j)$ with $i < j < m$, the
pairs taken in encoding order ($i$ ascending and, for each $i$, $j$ descending). The bit of
$(i, j)$ is true exactly when $o_i$ and $o_j$ lie in different clauses and are not
complementary, that is, are not occurrences of the same variable with opposite polarities. -/
def cliqueBits (φ : CNF) : List Bool :=
  (pairs (occs φ).length).map fun p => occAdj ((occs φ).getD p.1 (0, 0, false))
    ((occs φ).getD p.2 (0, 0, false))

/-- **Karp's CLIQUE instance of a CNF formula.** For a CNF formula $\varphi$ with $m$ clauses and
$N$ literal occurrences, the bit string encoding the instance $(m, G)$: $m$ ones, a zero, $N$
ones, a zero, then one adjacency bit for each pair $(i, j)$ with $i < j < N$, listed by $i$
ascending and, for each $i$, by $j$ descending, a true bit meaning that $i$ and $j$ are adjacent.
The graph $G$ has the literal occurrences of $\varphi$, in order, as its vertices
$0, \dots, N - 1$, and two occurrences are adjacent when they lie in different clauses and are
not complementary (the same variable with opposite polarities). -/
def toClique (φ : CNF) : List Bool := encodeKG φ.length (occs φ).length (cliqueBits φ)

/-- **Karp's SAT-to-CLIQUE map on bit strings.** The map on bit strings that decodes its input as
a CNF formula $\varphi$ (rejecting missing or trailing bits) and returns Karp's CLIQUE instance of
$\varphi$; an input that does not decode is sent to the fixed no-instance $k = 1$ on the graph
with no vertices. -/
def reduceClique (x : List Bool) : List Bool :=
  match decodeCNF x with
  | some φ => toClique φ
  | none => noKG

/-- **Complementing map from CLIQUE to INDEPENDENT-SET instances.** Writing $1$ for true and $0$
for false, the map sends a bit string $1^k\,0\,1^n\,0\,b$ to $1^k\,0\,1^n\,0\,\bar b$, where
$\bar b$ is $b$ with every bit complemented. A bit string with fewer than two zeros goes to the
fixed no-instance $1\,0\,0$. -/
def flipKG (x : List Bool) : List Bool :=
  match decodeKG x with
  | some (k, n, bits) => encodeKG k n (bits.map not)
  | none => noKG

/-- **Map from INDEPENDENT-SET to VERTEX-COVER instances.** Writing $1$ for true and $0$ for
false, the map sends a bit string $1^k\,0\,1^n\,0\,b$ with $k \le n$ to $1^{n-k}\,0\,1^n\,0\,b$.
Every other bit string, namely one of this form with $k > n$ or one with fewer than two zeros,
goes to the fixed no-instance $1\,0\,0$. -/
def isToVc (x : List Bool) : List Bool :=
  match decodeKG x with
  | some (k, n, bits) => if k ≤ n then encodeKG (n - k) n bits else noKG
  | none => noKG

end Cslib.Complexity.Karp
