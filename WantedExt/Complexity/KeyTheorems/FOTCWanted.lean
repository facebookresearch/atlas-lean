/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Immerman: FO + transitive closure is NL on ordered structures

Source:
N. Immerman, "Languages that capture complexity classes", SIAM Journal on Computing 16
(1987), 760-778 (STOC 1983).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.FOTC

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Immerman: FO + transitive closure is NL on ordered structures

A class `K` of finite ordered graphs is in `NL` (the set of its bitstring encodings is in
`NL`) iff it is definable in first-order logic with the transitive-closure operator
(`FO + TC`). Ordered graphs are graphs on the domain `Fin n` with the numeric order as a
distinguished relation: relation symbol `0` is `<`, symbol `1` is the edge relation.
`TC φ (xs, ys)` holds when the tuple `ys` is reachable from the tuple `xs` along
`φ`-steps, where `φ` defines a binary relation on tuples of arity `a = |xs| = |ys|`:
in the body, de Bruijn variables `0, …, a - 1` are the source-tuple components,
variables `a, …, 2 * a - 1` are the target-tuple components, and variables
`≥ 2 * a` are outer variables shifted by `2 * a` (index `j` in the body is outer
variable `j - 2 * a`). Reachability includes the length-zero path, and
mismatched endpoint-tuple lengths evaluate to `False`. Tuple closure is
essential for the `NL` characterization: configurations with `n ^ d` states
are represented by `d`-tuples, so a binary relation on single domain elements
(with paths of at most `n` vertices) would give only a restricted unary-arity
fragment, and the order does not provide an injection of all fixed-length
tuples back into an `n`-element domain. As with `FO + LFP`, the order
rigidifies the structures, so no isomorphism-closure hypothesis is needed.
Encodings are canonical: the edge table has length exactly `n * n`, so
trailing bits cannot encode extra information invisible to `tcEval`; the
empty structure (`n = 0`) is handled by a separate Boolean in the
definability clause.
-/

/-- **Ordered graphs for first-order logic with transitive closure.** An ordered graph is
encoded as a pair $(n, e)$ of a natural number $n$, the domain size, and a finite list $e$ of
booleans of arbitrary length, the edge table in row-major order. It is read as the graph on
$\{0, \dots, n - 1\}$, ordered numerically, with an edge from $a$ to $b$ when the entry of $e$ at
position $an + b$ is true; a missing entry counts as false. -/
abbrev TCOrderedGraph := ℕ × List Bool

/-- **Edge relation of an ordered graph for FO + TC.** For an ordered graph $(n, T)$ with edge
table $T$ and elements $a, b < n$, there is an edge from $a$ to $b$ when the entry of $T$ at
position $a n + b$ is true; positions beyond the end of $T$ count as false. -/
def tcEdge (G : TCOrderedGraph) (a b : Fin G.1) : Prop :=
  G.2.getD (a.val * G.1 + b.val) false = true

/-- **Formulas of first-order logic with transitive closure.** FO + TC formulas, with variables
and relation symbols indexed by natural numbers, are built from equations between two variables
and relation symbols applied to lists of variables by negation, conjunction, disjunction,
existential quantification (which binds variable $0$, de Bruijn style) and transitive closure
$\mathrm{TC}(\varphi; \bar u, \bar v)$ of a formula $\varphi$ applied to two lists $\bar u$,
$\bar v$ of variables. With $a = |\bar u| = |\bar v|$, the body $\varphi$ defines a step
relation on $a$-tuples: its variables $0, \dots, a - 1$ are the source tuple, $a, \dots, 2a - 1$
the target tuple, and each variable $j \ge 2a$ is outer variable $j - 2a$. -/
inductive TCFO where
  | eq : ℕ → ℕ → TCFO
  | rel : ℕ → List ℕ → TCFO
  | not : TCFO → TCFO
  | and : TCFO → TCFO → TCFO
  | or : TCFO → TCFO → TCFO
  | exists : TCFO → TCFO
  | tc : TCFO → List ℕ → List ℕ → TCFO

/-- **Order and edge relations as FO + TC relation symbols.** In an ordered graph with domain
$\{0, \dots, n - 1\}$, relation symbol $0$ holds of a list of elements exactly when the list is
$[a, b]$ with $a < b$, relation symbol $1$ holds exactly when the list is $[a, b]$ and there is
an edge from $a$ to $b$, and every other relation symbol holds of no list. -/
def tcBase (G : TCOrderedGraph) (i : ℕ) : List (Fin G.1) → Prop :=
  match i with
  | 0 => fun args => match args with
    | [a, b] => a.val < b.val
    | _ => False
  | 1 => fun args => match args with
    | [a, b] => tcEdge G a b
    | _ => False
  | _ => fun _ => False

/-- **Evaluation of FO + TC formulas.** Fix an ordered graph with domain
$D = \{0, \dots, n - 1\}$, an assignment $\rho$ of an element of $D$ to each variable index and
an assignment $S$ of a relation on lists of elements of $D$ to each relation symbol. The truth
value of a formula is defined by recursion. The equation between variables $i$ and $j$ holds
when $\rho(i) = \rho(j)$. Relation symbol $i$ applied to variables $j_1, \dots, j_k$ holds when
$S_i$ holds of the list $[\rho(j_1), \dots, \rho(j_k)]$. Negation, conjunction and disjunction
are interpreted as usual. An existential formula $\exists \varphi$ holds when $\varphi$ holds
under the assignment sending $0$ to some $d \in D$ and $j + 1$ to $\rho(j)$. A transitive
closure $\mathrm{TC}(\varphi; \bar u, \bar v)$ is false when the index lists $\bar u$ and
$\bar v$ have different lengths. Otherwise, with $a$ their common length, it holds when the
tuple $(\rho(v_0), \dots, \rho(v_{a-1}))$ is reachable from $(\rho(u_0), \dots, \rho(u_{a-1}))$
in zero or more steps, where a step from $s \in D^a$ to $t \in D^a$ means that $\varphi$ holds
under the assignment sending $j < a$ to $s_j$, $a \le j < 2a$ to $t_{j - a}$, and $j \ge 2a$ to
$\rho(j - 2a)$. -/
def tcEval (G : TCOrderedGraph) (ρ : ℕ → Fin G.1)
    (S : ℕ → List (Fin G.1) → Prop) : TCFO → Prop
  | .eq a b => ρ a = ρ b
  | .rel i args => S i (args.map ρ)
  | .not φ => ¬ tcEval G ρ S φ
  | .and φ ψ => tcEval G ρ S φ ∧ tcEval G ρ S ψ
  | .or φ ψ => tcEval G ρ S φ ∨ tcEval G ρ S ψ
  | .exists φ => ∃ a : Fin G.1,
      tcEval G (fun j => match j with | 0 => a | j + 1 => ρ j) S φ
  | .tc φ xs ys =>
      if h : xs.length = ys.length then
        Relation.ReflTransGen (fun s t : Fin xs.length → Fin G.1 =>
          tcEval G (fun j =>
            if hj : j < xs.length then s ⟨j, hj⟩
            else if hj2 : j < 2 * xs.length then t ⟨j - xs.length, by omega⟩
            else ρ (j - 2 * xs.length)) S φ)
          (fun i => ρ (xs.getD i.val 0)) (fun i => ρ (ys.getD i.val 0))
      else False

/-- **Example: parameterized transitive closure in FO + TC.** The FO + TC formula
$\mathrm{TC}(\varphi; (1), (2))$ of arity $1$ whose body $\varphi$ is
$E(0, 1) \lor (E(0, 2) \land E(2, 1))$, where $E$ is relation symbol $1$ (the edge relation).
In the body, variable $0$ is the source, variable $1$ the target, and variable $2$ is outer
variable $0$, shifted by $2$; the endpoint arguments $1$ and $2$ are outer variables, not
shifted. So the formula expresses that outer variable $2$ is reachable from outer variable $1$
by steps that are either an edge or a path of two edges through outer variable $0$. -/
def tcParamExample : TCFO :=
  .tc (.or (.rel 1 [0, 1])
    (.and (.rel 1 [0, 2]) (.rel 1 [2, 1]))) [1] [2]

/-- **Example: simultaneous reachability of pairs in FO + TC.** The FO + TC formula
$\mathrm{TC}(\varphi; (0, 1), (2, 3))$ of arity $2$ whose body $\varphi$ states that relation
symbol $1$ (the edge relation) holds of variables $0, 2$ and of variables $1, 3$. In the body,
variables $0, 1$ are the source pair and $2, 3$ the target pair, so a step moves both components
along an edge at the same time, and the formula expresses that the pair of outer variables
$(2, 3)$ is reachable from the pair $(0, 1)$ by such steps. -/
def tcPairExample : TCFO :=
  .tc (.and (.rel 1 [0, 2]) (.rel 1 [1, 3])) [0, 1] [2, 3]

/-- **Satisfaction of an FO + TC formula in an ordered graph.** An ordered graph with nonempty
domain $\{0, \dots, n - 1\}$ satisfies an FO + TC formula $\varphi$ when $\varphi$ evaluates to
true with every variable assigned the element $0$, relation symbol $0$ interpreted as the order
$<$ and relation symbol $1$ as the edge relation (both only on two-element lists), and every
other relation symbol interpreted as the empty relation. -/
def tcSat (G : TCOrderedGraph) (h : 0 < G.1) (φ : TCFO) : Prop :=
  tcEval G (fun _ => ⟨0, h⟩) (tcBase G) φ

open Classical in
/-- **Encodings of a class of ordered graphs.** For a set $K$ of ordered graphs, this is the
decision problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding of pairs of a natural number and a list of booleans, to some ordered graph
$(n, T) \in K$ whose edge table $T$ has length exactly $n^2$. -/
noncomputable def tcEncodings (K : Set TCOrderedGraph) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x => decide (∃ G ∈ K,
    MetaMathlibExt.BitstringEncoding.bitDecode x = some G ∧ G.2.length = G.1 * G.1)

/-- **Definability in FO + TC.** A set $K$ of ordered graphs is FO + TC-definable when there
are an FO + TC formula $\varphi$ and a boolean $b$ such that for every ordered graph $(n, T)$
whose edge table $T$ has length exactly $n^2$: if $n > 0$, then $(n, T) \in K$ exactly when
$(n, T)$ satisfies $\varphi$, and if $n = 0$, then $(n, T) \in K$ exactly when $b$ is true. -/
def tcDefinable (K : Set TCOrderedGraph) : Prop :=
  ∃ φ, ∃ emptyIn : Bool, ∀ G : TCOrderedGraph, G.2.length = G.1 * G.1 →
    (G ∈ K ↔ (if h : 0 < G.1 then tcSat G h φ else emptyIn = true))

/-- **Immerman: FO + transitive closure is NL on ordered structures.** For every set $K$ of
finite ordered graphs, the decision problem of the encodings of $K$ (the bitstrings that decode
to a member $(n, T)$ of $K$ whose edge table $T$ has length exactly $n^2$) belongs to
$\mathrm{NL}$ if and only if $K$ is definable in first-order logic with transitive closure.

Source: N.
Immerman, "Languages that capture complexity classes", SIAM Journal on Computing 16
(1987), 760-778 (STOC 1983). -/
public theorem_wanted fo_tc_eq_nl :
    ∀ K : Set TCOrderedGraph,
      (tcEncodings K ∈ NL ↔ tcDefinable K)

end MetaMathlibExt.Complexity.KeyTheorems.FOTC
