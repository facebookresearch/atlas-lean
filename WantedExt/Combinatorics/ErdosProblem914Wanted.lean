/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 914
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem914Wanted

/-! Source record `FC-ErdosProblem914`, ported from FormalConjectures
`ErdosProblems/914.lean` (`theorem erdos_914`,
`theorem erdos_914.variants.equitable_colouring`) and checked against
erdosproblems.com/914. The two claims are conjoined into one `conjecture`.
Status: resolved true (Corrádi–Hajnal for `r = 3`, Hajnal–Szemerédi for
`r ≥ 4`); the registry links a proof-bearing external Lean development. -/

/-- **Erdős Problem 914 on clique factors and equitable colourings.** The proposition asserts
that for all integers $r \ge 2$ and $m \ge 1$ and every finite simple graph $G$ with exactly $rm$
vertices, (a) if every vertex of $G$ has degree at least $m(r - 1)$, then $G$ contains $m$
pairwise disjoint cliques of $r$ vertices each, and (b) if every vertex of $G$ has degree at most
$m - 1$, then $G$ has a proper colouring with $m$ colours in which every colour class has exactly
$r$ vertices. -/
def conjecture : Prop :=
  (∀ {r m : ℕ}, 2 ≤ r → 1 ≤ m → ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj], Fintype.card V = r * m → m * (r - 1) ≤ G.minDegree →
    ∃ K : Fin m → Finset V, (∀ i, G.IsNClique r (K i)) ∧
      Pairwise fun i j => Disjoint (K i) (K j)) ∧
  (∀ {r m : ℕ}, 2 ≤ r → 1 ≤ m → ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj], Fintype.card V = r * m → G.maxDegree ≤ m - 1 →
    ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r)

/--
**Hajnal–Szemerédi theorem in clique-factor and equitable-colouring form.** For all integers
$r \ge 2$ and $m \ge 1$ and every finite simple graph $G$ with exactly $rm$ vertices, (a) if every
vertex of $G$ has degree at least $m(r - 1)$, then $G$ contains $m$ pairwise disjoint cliques of
$r$ vertices each, and (b) if every vertex of $G$ has degree at most $m - 1$, then $G$ has a
proper colouring with $m$ colours in which every colour class has exactly $r$ vertices.

This resolves Erdős Problem 914 affirmatively: part (a) was proved by Corrádi and Hajnal for
$r = 3$ and by Hajnal and Szemerédi for all $r$, and part (b) is its equitable-colouring
reformulation, obtained by applying (a) to the complement of $G$.

Source: A. Hajnal and E. Szemerédi, Proof of a conjecture of P. Erdős
(1970), 601–623, https://mathscinet.ams.org/mathscinet-getitem?mr=297607; External Lean proof of
Erdős Problem 914, plby/lean-proofs at commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos914.lean.
Moved from `OpenConjectures/Combinatorics/ErdosProblem914`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem914Wanted
