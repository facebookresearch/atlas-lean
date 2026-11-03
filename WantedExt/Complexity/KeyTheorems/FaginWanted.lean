/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fagin's theorem: NP is existential second-order logic

Source:
R. Fagin, "Generalized first-order spectra and polynomial-time recognizable sets", in
Complexity of Computation, SIAM-AMS Proceedings 7 (1974), 43-73.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Fagin

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Fagin's theorem: NP is existential second-order logic

A class `K` of finite graphs is in `NP` (the set of its bitstring encodings is in `NP`)
iff it is definable by an existential second-order (`∃SO`) sentence, provided `K` is
closed under graph isomorphism (definable classes are isomorphism-closed, so the
hypothesis is necessary). An `∃SO` sentence is a first-order formula `φ` together with a
number `k` of second-order relations it may use: the graph satisfies it if there are `k`
relations making `φ` true. The first-order part uses relation symbol `0` for the edge
relation, and symbols `≥ 1` for the second-order relations. Graphs are `(domain size,
row-major edge table)`; the sentence may in particular existentially quantify a linear
order, which is how the computation of an `NP` machine is described. Encodings are canonical:
the edge table has length exactly `n * n`; without this, `(n, [])` would be a
logarithmic-size representation of an `n`-vertex empty graph, and an `∃SO` spectrum could
induce an exponentially succinct language rather than the canonical adjacency-table
language Fagin applies to. The empty graph is handled by a separate Boolean in the
definability clause.
-/

/-- **Finite graphs as edge tables.** A finite graph is a pair $(n, t)$ of a natural number $n$,
the number of vertices, and a finite list $t$ of booleans, read as a row-major edge table. The
length of $t$ is not required to be $n^2$. -/
abbrev FaginGraph := ℕ × List Bool

/-- **Edge relation of a graph.** Let $G$ be a graph with vertices $0, \dots, n-1$ and edge table
$t$, a finite list of booleans. For vertices $a, b < n$, there is an edge from $a$ to $b$ exactly
when the entry of $t$ at position $an + b$ (counting from $0$) is true; a position beyond the end
of $t$ counts as false. -/
def faginEdge (G : FaginGraph) (a b : Fin G.1) : Prop :=
  G.2.getD (a.val * G.1 + b.val) false = true

/-- **First-order formulas over graphs.** Variables and relation symbols are indexed by natural
numbers. Formulas are built from equations $x_a = x_b$ between variables and atomic formulas
applying a relation symbol $i$ to a finite list of variables, by negation, conjunction,
disjunction and existential quantification $\exists \varphi$, which binds variable $0$ of
$\varphi$ (de Bruijn indexing). -/
inductive FaginFO where
  | eq : ℕ → ℕ → FaginFO
  | rel : ℕ → List ℕ → FaginFO
  | not : FaginFO → FaginFO
  | and : FaginFO → FaginFO → FaginFO
  | or : FaginFO → FaginFO → FaginFO
  | exists : FaginFO → FaginFO

/-- **Evaluation of a first-order formula in a graph.** Let $G$ be a graph, let $\rho$ assign a
vertex $\rho(j)$ of $G$ to each variable $x_j$ ($j \in \mathbb{N}$), and let $S$ assign to each
relation symbol $i \in \mathbb{N}$ a predicate $S_i$ on finite lists of vertices of $G$. Truth of a
formula is defined by recursion: $x_a = x_b$ holds when $\rho(a) = \rho(b)$; relation symbol $i$
applied to the variables $x_{a_1}, \dots, x_{a_m}$ holds when $S_i$ holds of the list
$[\rho(a_1), \dots, \rho(a_m)]$; negation, conjunction and disjunction are interpreted as usual;
and $\exists \varphi$ holds when there is a vertex $v$ such that $\varphi$ holds under the
assignment sending $x_0$ to $v$ and $x_{j+1}$ to $\rho(j)$ for each $j$, with $S$ unchanged. -/
def faginEval (G : FaginGraph) (ρ : ℕ → Fin G.1)
    (S : ℕ → List (Fin G.1) → Prop) : FaginFO → Prop
  | .eq a b => ρ a = ρ b
  | .rel i args => S i (args.map ρ)
  | .not φ => ¬ faginEval G ρ S φ
  | .and φ ψ => faginEval G ρ S φ ∧ faginEval G ρ S ψ
  | .or φ ψ => faginEval G ρ S φ ∨ faginEval G ρ S ψ
  | .exists φ => ∃ a : Fin G.1,
      faginEval G (fun j => match j with | 0 => a | j + 1 => ρ j) S φ

/-- **Interpretation of relation symbols in a graph.** Let $G$ be a graph and let
$(E_j)_{j \in \mathbb{N}}$ be a family of relations, each a predicate on finite lists of vertices
of $G$. Relation symbol $0$ is interpreted as the edge relation of $G$: it holds of a list exactly
when the list is $[a, b]$ for vertices $a, b$ with an edge from $a$ to $b$. For $i \ge 1$, relation
symbol $i$ is interpreted as $E_{i-1}$. -/
def faginBase (G : FaginGraph) (extra : ℕ → List (Fin G.1) → Prop)
    (i : ℕ) : List (Fin G.1) → Prop :=
  if i = 0 then fun args => match args with
    | [a, b] => faginEdge G a b
    | _ => False
  else extra (i - 1)

/-- **Satisfaction of an existential second-order sentence.** Let $G$ be a graph with $n > 0$
vertices, $k$ a natural number and $\varphi$ a first-order formula. Then $G$ satisfies the
existential second-order sentence $(k, \varphi)$ if there are relations $R_0, \dots, R_{k-1}$,
each a predicate on finite lists of vertices of $G$, such that $\varphi$ holds in $G$ when
relation symbol $0$ is interpreted as the edge relation (holding exactly of the lists $[a, b]$
with an edge from $a$ to $b$), relation symbol $j + 1$ as $R_j$ for each $j < k$, every relation
symbol above $k$ as the empty relation, and every variable as vertex $0$. -/
def faginESOSat (G : FaginGraph) (h : 0 < G.1) (k : ℕ) (φ : FaginFO) : Prop :=
  ∃ R : (j : Fin k) → List (Fin G.1) → Prop,
    faginEval G (fun _ => ⟨0, h⟩)
      (faginBase G (fun j => if h' : j < k then R ⟨j, h'⟩ else fun _ => False)) φ

open Classical in
/-- **Encodings of a graph class as a decision problem.** For a class $K$ of graphs, this is the
decision problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding of pairs of a natural number and a list of booleans, to a graph $G \in K$ with
$n$ vertices whose edge table has length exactly $n^2$. -/
noncomputable def faginEncodings (K : Set FaginGraph) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x => decide (∃ G ∈ K,
    MetaMathlibExt.BitstringEncoding.bitDecode x = some G ∧ G.2.length = G.1 * G.1)

/-- **Isomorphic graphs.** Graphs $G_1$ and $G_2$ are isomorphic if they have the same number of
vertices and there is a bijection $\sigma$ from the vertices of $G_1$ to the vertices of $G_2$
such that for all vertices $a, b$ of $G_1$, there is an edge from $a$ to $b$ in $G_1$ if and only
if there is an edge from $\sigma(a)$ to $\sigma(b)$ in $G_2$. -/
def faginIso (G₁ G₂ : FaginGraph) : Prop :=
  G₁.1 = G₂.1 ∧ ∃ σ : Fin G₁.1 ≃ Fin G₂.1,
    ∀ a b : Fin G₁.1, faginEdge G₁ a b ↔ faginEdge G₂ (σ a) (σ b)

/-- **Isomorphism-closed graph classes.** A class $K$ of graphs is isomorphism-closed if for every
$G_1 \in K$, every graph $G_2$ isomorphic to $G_1$ also belongs to $K$. -/
def faginIsoClosed (K : Set FaginGraph) : Prop :=
  ∀ G₁ ∈ K, ∀ G₂ : FaginGraph, faginIso G₁ G₂ → G₂ ∈ K

/-- **Existential second-order definable graph classes.** A class $K$ of graphs is existential
second-order definable if there are a natural number $k$, a first-order formula $\varphi$ and a
boolean $e$ such that every graph $G$ with $n$ vertices whose edge table has length exactly $n^2$
satisfies the following: if $n > 0$, then $G \in K$ if and only if $G$ satisfies the existential
second-order sentence $(k, \varphi)$; if $n = 0$, then $G \in K$ if and only if $e$ is true. -/
def faginESODefinable (K : Set FaginGraph) : Prop :=
  ∃ k φ, ∃ emptyIn : Bool, ∀ G : FaginGraph, G.2.length = G.1 * G.1 →
    (G ∈ K ↔ (if h : 0 < G.1 then faginESOSat G h k φ else emptyIn = true))

/-- **Fagin's theorem: NP is existential second-order logic.** Let $K$ be a class of finite
graphs, each given as a pair $(n, t)$ of a number $n$ of vertices and a row-major edge table $t$
(a list of booleans), and suppose that $K$ is closed under graph isomorphism. Then the decision
problem that accepts exactly the bitstrings decoding to a member $(n, t)$ of $K$ whose edge table
has length $n^2$ is in NP if and only if $K$ is definable in existential second-order logic:
there are a first-order formula $\varphi$, a number $k$ and a boolean $b$ such that a graph
$(n, t)$ whose edge table has length $n^2$ belongs to $K$ exactly when either $n > 0$ and some
$k$ relations on its vertices, together with its edge relation, make $\varphi$ true (with every
free variable of $\varphi$ denoting vertex $0$), or $n = 0$ and $b$ is true.

Source: R. Fagin,
"Generalized first-order spectra and polynomial-time recognizable sets", in Complexity of
Computation, SIAM-AMS Proceedings 7 (1974), 43-73. -/
public theorem_wanted fagin :
    ∀ K : Set FaginGraph, faginIsoClosed K →
      (faginEncodings K ∈ MetaMathlibExt.ComplexityTheory.NP ↔ faginESODefinable K)

end MetaMathlibExt.Complexity.KeyTheorems.Fagin
