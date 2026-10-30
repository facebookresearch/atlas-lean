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

/-- A finite ordered graph: domain size and a row-major edge table; the order is the
numeric order on `Fin n`. -/
abbrev OrderedGraph := ℕ × List Bool

/-- The edge relation of an ordered graph on `Fin n`. -/
def ogEdge (G : OrderedGraph) (a b : Fin G.1) : Prop :=
  G.2.getD (a.val * G.1 + b.val) false = true

/-- First-order formulas with least fixed points over ordered graphs. `lfp R arity φ args`
is the least fixed point of the operator defined by `φ` (with `R` as the recursive
relation, of the given arity) applied to the tuple `args`. -/
inductive OGFO where
  | eq : ℕ → ℕ → OGFO
  | rel : ℕ → List ℕ → OGFO
  | not : OGFO → OGFO
  | and : OGFO → OGFO → OGFO
  | or : OGFO → OGFO → OGFO
  | exists : OGFO → OGFO
  | lfp : ℕ → ℕ → OGFO → List ℕ → OGFO

mutual
/-- `R` occurs only positively in the formula: every occurrence of relation `R` is under an even number of negations. -/
def PositiveIn (R : ℕ) : OGFO → Prop
  | .eq _ _ => True
  | .rel _ _ => True
  | .not φ => NegativeIn R φ
  | .and φ ψ => PositiveIn R φ ∧ PositiveIn R ψ
  | .or φ ψ => PositiveIn R φ ∧ PositiveIn R ψ
  | .exists φ => PositiveIn R φ
  | .lfp _ _ φ _ => PositiveIn R φ

/-- `R` occurs only negatively in the formula: every occurrence of relation `R` is under an odd number of negations. -/
def NegativeIn (R : ℕ) : OGFO → Prop
  | .eq _ _ => True
  | .rel i _ => if i = R then False else True
  | .not φ => PositiveIn R φ
  | .and φ ψ => NegativeIn R φ ∧ NegativeIn R ψ
  | .or φ ψ => NegativeIn R φ ∧ NegativeIn R ψ
  | .exists φ => NegativeIn R φ
  | .lfp _ _ φ _ => NegativeIn R φ
end

/-- Every `LFP` node of `φ` binds a fresh symbol `≥ 2` and is positive in it. -/
def AllLFPPositive : OGFO → Prop
  | .eq _ _ => True
  | .rel _ _ => True
  | .not φ => AllLFPPositive φ
  | .and φ ψ => AllLFPPositive φ ∧ AllLFPPositive ψ
  | .or φ ψ => AllLFPPositive φ ∧ AllLFPPositive ψ
  | .exists φ => AllLFPPositive φ
  | .lfp R _ φ _ => 2 ≤ R ∧ PositiveIn R φ ∧ AllLFPPositive φ

/-- The meaning of relation symbol `i` in an ordered graph: symbol `0` is `<`, symbol
`1` is the edge relation, other symbols are the supplied relations. -/
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

/-- Well-formedness of a formula relative to a relation-arity environment `env`
(`env R = some a` when `R` is bound by an enclosing `LFP` of arity `a`): every
`LFP` node binds a symbol `≥ 2`, is applied to exactly `arity` arguments, and every
occurrence of a bound relation symbol has exactly its bound arity; the built-in
symbols `0` (`<`) and `1` (edge) are binary. Without this, a term would not denote
the advertised arity-specific least fixed point. -/
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

/-- Evaluation of a first-order formula with least fixed points in an ordered graph,
with variable assignment `ρ` and relation assignment `S`. In the `LFP` body, the
first `arity` variables are bound to the tuple and outer variables are shifted past
them (`j ↦ ρ (j - arity)`), exactly as `exists` shifts by one. -/
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

/-- An ordered graph satisfies an `FO + LFP` sentence `φ`: `φ` is well-formed (with
no free relation symbols), positive at every `LFP` node, and evaluates to true. -/
def ogLFPSat (G : OrderedGraph) (h : 0 < G.1) (φ : OGFO) : Prop :=
  OGWellFormed (fun _ => none) φ ∧ AllLFPPositive φ ∧
    ogEval G (fun _ => ⟨0, h⟩) (ogBase G (fun _ => fun _ => False)) φ

open Classical in
/-- The encodings of a class of ordered graphs, as a decision problem: only canonical
encodings (edge table of length `n * n`) count. -/
noncomputable def ogEncodings (K : Set OrderedGraph) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x => decide (∃ G ∈ K,
    MetaMathlibExt.BitstringEncoding.bitDecode x = some G ∧ G.2.length = G.1 * G.1)

/-- `K` is `FO + LFP`-definable if some `FO + LFP` sentence is true exactly on its
canonical members, with the empty structure's membership given by a separate Boolean. -/
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
