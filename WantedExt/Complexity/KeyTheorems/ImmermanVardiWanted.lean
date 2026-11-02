/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Immerman-Vardi: FO + least fixed point is P on ordered structures

Source:
N. Immerman, "Relational queries definable in polynomial time", Information and Control 68
(1986), 193-243 (STOC 1983); M. Y. Vardi, "The complexity of relational query languages",
Proceedings of the Fourteenth Annual ACM Symposium on Theory of Computing (STOC 1982),
137-146.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.ImmermanVardi

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Immerman-Vardi: FO + least fixed point is P on ordered structures

A class `K` of finite ordered graphs is in `P` (the set of its bitstring encodings is in
`P`) iff it is definable in first-order logic with the least-fixed-point operator
(`FO + LFP`). Ordered graphs are graphs on the domain `Fin n` with the numeric order as a
distinguished relation: relation symbol `0` is `<`, symbol `1` is the edge relation, and
the least-fixed-point operator binds fresh symbols `≥ 2`. The order rigidifies the
structures (the only order-preserving bijection is the identity), so no
isomorphism-closure hypothesis is needed. The `LFP` operator is evaluated by inflationary
iteration from `∅` for `n ^ arity` stages, which is the least fixed point on positive
formulas; `LFP` nodes are required to be positive in their bound relation. Encodings are
canonical: the edge table has length exactly `n * n`, so trailing bits cannot encode
extra information invisible to `ogEval`; the empty structure (`n = 0`) is handled by a
separate Boolean in the definability clause.
-/

/-- **Finite ordered graphs.** A finite ordered graph is a pair $(n, t)$ of a natural number $n$
and a finite list $t$ of booleans of any length. Here $n$ is the size of the domain
$\{0, \dots, n - 1\}$, ordered numerically, and $t$ is read as a row-major edge table. -/
abbrev OrderedGraph := ℕ × List Bool

/-- **Edge relation of an ordered graph.** Let $G$ be an ordered graph with vertices
$0, \dots, n - 1$ and edge table $t$, a list of booleans. There is an edge from $a$ to $b$ when
the entry of $t$ at position $a n + b$ is true; positions beyond the end of $t$ count as false. -/
def ogEdge (G : OrderedGraph) (a b : Fin G.1) : Prop :=
  G.2.getD (a.val * G.1 + b.val) false = true

/-- **Formulas of first-order logic with least fixed points.** Variables and relation symbols are
natural numbers. Formulas are built from equalities $x_a = x_b$ and atoms
$R_i(x_{a_1}, \dots, x_{a_k})$ by negation, conjunction, disjunction, existential quantification
and least-fixed-point formulas $\mathrm{lfp}(R, k, \varphi, (a_1, \dots, a_m))$, the least fixed
point of the operator defined by $\varphi$ (with $R$ as the recursive relation, of arity $k$)
applied to the tuple of variables $(a_1, \dots, a_m)$. -/
inductive OGFO where
  | eq : ℕ → ℕ → OGFO
  | rel : ℕ → List ℕ → OGFO
  | not : OGFO → OGFO
  | and : OGFO → OGFO → OGFO
  | or : OGFO → OGFO → OGFO
  | exists : OGFO → OGFO
  | lfp : ℕ → ℕ → OGFO → List ℕ → OGFO

mutual
/-- **Positive occurrence of a relation symbol.** A relation symbol $R$ occurs only positively in
a first-order formula with least fixed points over ordered graphs when every atomic formula with
relation symbol $R$ in it, including those inside least-fixed-point subformulas whatever symbol
they bind, lies under an even number of negations. -/
def PositiveIn (R : ℕ) : OGFO → Prop
  | .eq _ _ => True
  | .rel _ _ => True
  | .not φ => NegativeIn R φ
  | .and φ ψ => PositiveIn R φ ∧ PositiveIn R ψ
  | .or φ ψ => PositiveIn R φ ∧ PositiveIn R ψ
  | .exists φ => PositiveIn R φ
  | .lfp _ _ φ _ => PositiveIn R φ

/-- **Negative occurrence of a relation symbol.** A relation symbol $R$ occurs only negatively
in a formula $\varphi$ of first-order logic with least fixed points when every atomic formula
$R(x_{a_1}, \dots, x_{a_k})$ in $\varphi$, including those inside least-fixed-point subformulas,
lies under an odd number of negations. -/
def NegativeIn (R : ℕ) : OGFO → Prop
  | .eq _ _ => True
  | .rel i _ => if i = R then False else True
  | .not φ => PositiveIn R φ
  | .and φ ψ => NegativeIn R φ ∧ NegativeIn R ψ
  | .or φ ψ => NegativeIn R φ ∧ NegativeIn R ψ
  | .exists φ => NegativeIn R φ
  | .lfp _ _ φ _ => NegativeIn R φ
end

/-- **Formulas whose fixed points are all positive.** Let $\varphi$ be a formula of first-order
logic with least fixed points, whose relation symbols are natural numbers. All fixed points of
$\varphi$ are positive when every least-fixed-point subformula of $\varphi$, nested ones included,
binds a relation symbol $R \ge 2$ (so neither the order symbol $0$ nor the edge symbol $1$) and
$R$ occurs only positively in the body of that subformula. -/
def AllLFPPositive : OGFO → Prop
  | .eq _ _ => True
  | .rel _ _ => True
  | .not φ => AllLFPPositive φ
  | .and φ ψ => AllLFPPositive φ ∧ AllLFPPositive ψ
  | .or φ ψ => AllLFPPositive φ ∧ AllLFPPositive ψ
  | .exists φ => AllLFPPositive φ
  | .lfp R _ φ _ => 2 ≤ R ∧ PositiveIn R φ ∧ AllLFPPositive φ

/-- **Interpretation of relation symbols in an ordered graph.** Let $G$ be an ordered graph with
vertices $0, \dots, n - 1$ and let $(E_i)_{i \in \mathbb{N}}$ be predicates on lists of vertices.
Relation symbol $0$ holds of a list exactly when it is a pair $(a, b)$ with $a < b$, relation
symbol $1$ holds of a list exactly when it is a pair $(a, b)$ with an edge from $a$ to $b$ in $G$,
and relation symbol $i + 2$ is interpreted as $E_i$. -/
def ogBase (G : OrderedGraph) (extra : ℕ → List (Fin G.1) → Prop)
    (i : ℕ) : List (Fin G.1) → Prop :=
  match i with
  | 0 => fun args => match args with
    | [a, b] => a.val < b.val
    | _ => False
  | 1 => fun args => match args with
    | [a, b] => ogEdge G a b
    | _ => False
  | i + 2 => extra i

/-- **Well-formed FO + LFP formulas.** Let $e$ assign to each relation symbol (a natural number)
either an arity or nothing. Whether a first-order formula with least fixed points over ordered
graphs is well-formed relative to $e$ is defined by recursion on the formula. An equality of two
variables is well-formed. An atomic formula $R(x_1, \dots, x_k)$ is well-formed when $k = a$ if
$e(R) = a$; when $k = 2$ if $e$ assigns nothing to $R$ and $R$ is $0$ (the order) or $1$ (the edge
relation); and always otherwise. A negation or an existential quantification is well-formed when
its body is, and a conjunction or a disjunction when both of its parts are. A least-fixed-point
formula that binds the symbol $R$ with arity $a$, has body $\varphi$ and is applied to the
variables $y_1, \dots, y_k$ is well-formed when $R \ge 2$, $k = a$, and $\varphi$ is well-formed
relative to the assignment that agrees with $e$ except that it gives $R$ the arity $a$. -/
def OGWellFormed (env : ℕ → Option ℕ) : OGFO → Prop
  | .eq _ _ => True
  | .rel i args => match env i with
    | some a => args.length = a
    | none => if i = 0 ∨ i = 1 then args.length = 2 else True
  | .not φ => OGWellFormed env φ
  | .and φ ψ => OGWellFormed env φ ∧ OGWellFormed env ψ
  | .or φ ψ => OGWellFormed env φ ∧ OGWellFormed env ψ
  | .exists φ => OGWellFormed env φ
  | .lfp R arity φ args => 2 ≤ R ∧ args.length = arity ∧
      OGWellFormed (Function.update env R (some arity)) φ

/-- **Evaluation of FO + LFP formulas in an ordered graph.** Let $G$ be an ordered graph with
vertex set $V = \{0, \dots, n - 1\}$, let $\rho$ assign a vertex to each variable
$0, 1, 2, \dots$, and let $S$ assign to each relation symbol $i$ a predicate $S_i$ on lists of
vertices. The truth of a formula is defined by recursion: $x_a = x_b$ holds when
$\rho(a) = \rho(b)$; the atom $R_i(x_{a_1}, \dots, x_{a_k})$ holds when $S_i$ holds of
$(\rho(a_1), \dots, \rho(a_k))$; negation, conjunction and disjunction are evaluated as usual;
$\exists \varphi$ holds when $\varphi$ holds for some $v \in V$ under the assignment sending
variable $0$ to $v$ and variable $j + 1$ to $\rho(j)$. The least-fixed-point formula with bound
symbol $R$, arity $k$, body $\varphi$ and argument variables $a_1, \dots, a_m$ holds when
$(\rho(a_1), \dots, \rho(a_m))$ lies in $X_{n^k}$, where $X_0$ is empty and a list $t$ lies in
$X_{s+1}$ when $\varphi$ holds with $R$ reinterpreted as $X_s$ (the other symbols keeping their
interpretation under $S$) and with variable $j$ assigned the $j$-th entry of $t$ (or $\rho(0)$
if $t$ has no such entry) for $j < k$ and $\rho(j - k)$ for $j \ge k$. -/
def ogEval (G : OrderedGraph) (ρ : ℕ → Fin G.1)
    (S : ℕ → List (Fin G.1) → Prop) : OGFO → Prop
  | .eq a b => ρ a = ρ b
  | .rel i args => S i (args.map ρ)
  | .not φ => ¬ ogEval G ρ S φ
  | .and φ ψ => ogEval G ρ S φ ∧ ogEval G ρ S ψ
  | .or φ ψ => ogEval G ρ S φ ∨ ogEval G ρ S ψ
  | .exists φ => ∃ a : Fin G.1,
      ogEval G (fun j => match j with | 0 => a | j + 1 => ρ j) S φ
  | .lfp R arity φ args => ogLFPIter G ρ S R arity φ (G.1 ^ arity) (args.map ρ)
where
  /-- Inflationary iteration of the `LFP` operator, from `∅`, for a bounded number of
  stages. -/
  ogLFPIter (G : OrderedGraph) (ρ : ℕ → Fin G.1)
      (S : ℕ → List (Fin G.1) → Prop) (R arity : ℕ) (φ : OGFO) : ℕ →
      List (Fin G.1) → Prop
    | 0 => fun _ => False
    | t + 1 => fun tuple =>
        ogEval G (fun j => if j < arity then tuple.getD j (ρ 0) else ρ (j - arity))
          (Function.update S R (ogLFPIter G ρ S R arity φ t)) φ

/-- **Satisfaction of an FO + LFP formula by an ordered graph.** An ordered graph $G$ with $n > 0$
vertices satisfies a formula $\varphi$ of first-order logic with least fixed points when $\varphi$
is well-formed in the environment where no relation symbol is bound, all fixed points of
$\varphi$ are positive, and $\varphi$ is true in $G$ with every variable assigned the vertex $0$,
relation symbol $0$ interpreted as the order $<$, relation symbol $1$ as the edge relation, and
every other relation symbol as the empty relation. -/
def ogLFPSat (G : OrderedGraph) (h : 0 < G.1) (φ : OGFO) : Prop :=
  OGWellFormed (fun _ => none) φ ∧ AllLFPPositive φ ∧
    ogEval G (fun _ => ⟨0, h⟩) (ogBase G (fun _ => fun _ => False)) φ

open Classical in
/-- **Encodings of a class of ordered graphs.** For a class $K$ of ordered graphs, this is the
decision problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding of pairs of a natural number and a list of booleans, to some $G \in K$ whose
edge table has length exactly $n^2$, where $n$ is the number of vertices of $G$. -/
noncomputable def ogEncodings (K : Set OrderedGraph) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x => decide (∃ G ∈ K,
    MetaMathlibExt.BitstringEncoding.bitDecode x = some G ∧ G.2.length = G.1 * G.1)

/-- **Definability in FO + LFP.** A class $K$ of ordered graphs is definable in first-order logic
with least fixed points when there are a formula $\varphi$ and a boolean $b$ such that every
ordered graph $G$ with $n$ vertices whose edge table has length $n^2$ lies in $K$ exactly when
either $n > 0$ and $G$ satisfies $\varphi$, or $n = 0$ and $b$ is true. -/
def ogLFPDefinable (K : Set OrderedGraph) : Prop :=
  ∃ φ, ∃ emptyIn : Bool, ∀ G : OrderedGraph, G.2.length = G.1 * G.1 →
    (G ∈ K ↔ (if h : 0 < G.1 then ogLFPSat G h φ else emptyIn = true))

/-- **Immerman-Vardi: FO + least fixed point is P on ordered structures.** Source: N.
Immerman, "Relational queries definable in polynomial time", Information and Control 68
(1986), 193-243 (STOC 1983); M. Y. Vardi, "The complexity of relational query languages",
Proceedings of the Fourteenth Annual ACM Symposium on Theory of Computing (STOC 1982),
137-146. -/
public theorem_wanted immerman_vardi :
    ∀ K : Set OrderedGraph,
      (ogEncodings K ∈ MetaMathlibExt.ComplexityTheory.P ↔ ogLFPDefinable K)

end MetaMathlibExt.Complexity.KeyTheorems.ImmermanVardi
