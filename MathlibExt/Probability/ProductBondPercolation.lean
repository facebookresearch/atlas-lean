/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Set.Card
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProductMeasure

universe u

@[expose] public section

open MeasureTheory

namespace MathlibExt.Probability.ProductBondPercolation

/-- **The integer line graph.** The integer line is the simple graph on $\mathbb{Z}$ in which
$m$ and $n$ are adjacent exactly when $|m - n| = 1$. -/
def intLine : SimpleGraph ℤ where
  Adj a b := b = a + 1 ∨ a = b + 1
  symm := ⟨by
    intro a b h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h⟩
  loopless := ⟨by
    intro a h
    rcases h with h | h <;> omega⟩

/-- **The product graph $G \times \mathbb{Z}$.** For a simple graph $G$ on $V$, the graph
$G \times \mathbb{Z}$ is the box product of $G$ with the integer line: its vertex set is
$V \times \mathbb{Z}$, and $(v, m)$ and $(w, n)$ are adjacent exactly when either $v$ and $w$
are adjacent in $G$ and $m = n$, or $v = w$ and $|m - n| = 1$. -/
def prodGraph {V : Type u} (G : SimpleGraph V) : SimpleGraph (V × ℤ) :=
  G □ intLine

/-- **Open subgraph of the product graph.** Let $G$ be a simple graph on $V$, let
$G \times \mathbb{Z}$ denote the box product of $G$ with the integer line, and let $\omega$
assign true or false to every unordered pair of points of $V \times \mathbb{Z}$. The open
subgraph of $G \times \mathbb{Z}$ determined by $\omega$ is the simple graph on
$V \times \mathbb{Z}$ in which $a$ and $b$ are adjacent exactly when they are adjacent in
$G \times \mathbb{Z}$ and $\omega(\{a, b\})$ is true. -/
def configGraph {V : Type u} (G : SimpleGraph V) (ω : Sym2 (V × ℤ) → Bool) :
    SimpleGraph (V × ℤ) :=
  SimpleGraph.fromEdgeSet {e | ω e = true} ⊓ prodGraph G

theorem configGraph_adj {V : Type u} (G : SimpleGraph V) (ω : Sym2 (V × ℤ) → Bool)
    (a b : V × ℤ) :
    (configGraph G ω).Adj a b ↔ (prodGraph G).Adj a b ∧ ω s(a, b) = true := by
  simp only [configGraph, SimpleGraph.inf_adj, SimpleGraph.fromEdgeSet_adj,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hω, -⟩, hG⟩
    exact ⟨hG, hω⟩
  · rintro ⟨hG, hω⟩
    exact ⟨⟨hω, (prodGraph G).ne_of_adj hG⟩, hG⟩

theorem configGraph_le_prodGraph {V : Type u} (G : SimpleGraph V)
    (ω : Sym2 (V × ℤ) → Bool) :
    configGraph G ω ≤ prodGraph G := inf_le_right

/-- **Open cluster in the product graph.** Let $G$ be a simple graph on $V$, let
$G \times \mathbb{Z}$ denote the box product of $G$ with the integer line, let $\omega$ assign
true or false to every unordered pair of points of $V \times \mathbb{Z}$, and let
$x \in V \times \mathbb{Z}$. The open cluster of $x$ is the set of points
$y \in V \times \mathbb{Z}$ that are reachable from $x$ (including $x$ itself) in the open
subgraph of $G \times \mathbb{Z}$ determined by $\omega$, that is, joined to $x$ by a path whose
edges $e$ are edges of $G \times \mathbb{Z}$ with $\omega(e)$ true. -/
def cluster {V : Type u} (G : SimpleGraph V) (ω : Sym2 (V × ℤ) → Bool)
    (x : V × ℤ) : Set (V × ℤ) :=
  {y | (configGraph G ω).Reachable x y}

theorem self_mem_cluster {V : Type u} (G : SimpleGraph V) (ω : Sym2 (V × ℤ) → Bool)
    (x : V × ℤ) : x ∈ cluster G ω x := by
  change (configGraph G ω).Reachable x x
  exact SimpleGraph.Reachable.refl x

/-- **Bernoulli bond law on $V \times \mathbb{Z}$.** For a type $V$ and $0 \le p \le 1$, the
Bernoulli($p$) bond law on $V \times \mathbb{Z}$ is the product measure on configurations
$\omega$, which assign true (open) or false (closed) to every unordered pair $\{a, b\}$ of
points of $V \times \mathbb{Z}$ (with $a = b$ allowed), under which the values $\omega(e)$ are
independent and each is true with probability $p$ and false with probability $1 - p$. -/
noncomputable def bernoulliLaw {V : Type u} (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure (Sym2 (V × ℤ) → Bool) :=
  Measure.infinitePi fun _ => ProbabilityTheory.bernoulliMeasure true false ⟨p, hp0, hp1⟩

/-- **Almost-sure properties under the Bernoulli bond law.** Let $V$ be a type, let $p$ be a real
number with $0 \le p \le 1$, and let $P$ be a property of configurations $\omega$, that is, of
functions assigning true or false to every unordered pair $\{a, b\}$ of points of
$V \times \mathbb{Z}$ (with $a = b$ allowed). We say that $P$ holds almost surely if $P(\omega)$
holds for almost every $\omega$ with respect to the Bernoulli($p$) bond law on
$V \times \mathbb{Z}$. -/
def AlmostSurely {V : Type u} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : (Sym2 (V × ℤ) → Bool) → Prop) : Prop :=
  ∀ᵐ ω ∂(bernoulliLaw p hp0 hp1), P ω

section GeneralGraph

variable {V : Type u} (G : SimpleGraph V)

/-- **Open subgraph of a graph.** Let $G$ be a simple graph on $V$ and let $\omega$ assign true or
false to every unordered pair of elements of $V$. The open subgraph of $G$ determined by
$\omega$ is the simple graph on $V$ in which $a$ and $b$ are adjacent exactly when they are
adjacent in $G$ and $\omega(\{a, b\})$ is true. -/
def openSubgraph (ω : Sym2 V → Bool) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ω e = true} ⊓ G

theorem openSubgraph_le (ω : Sym2 V → Bool) : openSubgraph G ω ≤ G :=
  inf_le_right

/-- **Open cluster in a graph.** Let $G$ be a simple graph on $V$, let $\omega$ assign true or
false to every unordered pair of elements of $V$, and let $x \in V$. The open cluster of $x$ is
the set of vertices $y \in V$ that are reachable from $x$ (including $x$ itself) in the open
subgraph of $G$ determined by $\omega$, that is, joined to $x$ by a path whose edges $e$ are
edges of $G$ with $\omega(e)$ true. -/
def gcluster (ω : Sym2 V → Bool) (x : V) : Set V :=
  {y | (openSubgraph G ω).Reachable x y}

theorem self_mem_gcluster (ω : Sym2 V → Bool) (x : V) : x ∈ gcluster G ω x := by
  change (openSubgraph G ω).Reachable x x
  exact SimpleGraph.Reachable.refl x

/-- **Bernoulli bond law on $V$.** For a type $V$ and $0 \le p \le 1$, the Bernoulli($p$) bond
law on $V$ is the product measure on configurations $\omega$, which assign true (open) or false
(closed) to every unordered pair $\{a, b\}$ of elements of $V$ (with $a = b$ allowed), under
which the values $\omega(e)$ are independent and each is true with probability $p$ and false
with probability $1 - p$. -/
noncomputable def gbernoulliLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Measure (Sym2 V → Bool) :=
  Measure.infinitePi fun _ => ProbabilityTheory.bernoulliMeasure true false ⟨p, hp0, hp1⟩

end GeneralGraph

/-- **Critical probability for bond percolation.** For a simple graph $G$ on a countable vertex
set $V$, the critical probability $p_c(G)$ is the infimum of the set consisting of $1$ together
with every $p \in [0, 1]$ for which, under the Bernoulli($p$) bond law on $V$, the event that
the open cluster in $G$ of some vertex is infinite has positive probability. In particular
$p_c(G) = 1$ when no such $p$ exists.

Countability of $V$ makes the event that some open cluster is infinite measurable for the
product law. -/
noncomputable def criticalProb {V : Type u} [Countable V] (G : SimpleGraph V) : ℝ :=
  sInf (insert 1 {p : ℝ | ∃ hp0 : 0 ≤ p, ∃ hp1 : p ≤ 1,
    0 < gbernoulliLaw p hp0 hp1 {ω | ∃ x : V, (gcluster G ω x).Infinite}})

end MathlibExt.Probability.ProductBondPercolation
