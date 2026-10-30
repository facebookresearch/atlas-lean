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

/-- A finite ordered graph: domain size and a row-major edge table; the order is the
numeric order on `Fin n`. -/
abbrev TCOrderedGraph := ℕ × List Bool

/-- The edge relation of an ordered graph on `Fin n`. -/
def tcEdge (G : TCOrderedGraph) (a b : Fin G.1) : Prop :=
  G.2.getD (a.val * G.1 + b.val) false = true

/-- First-order formulas with transitive closure over ordered graphs. `tc φ xs ys`
is the transitive closure of the binary relation on tuples of arity
`|xs| = |ys|` defined by `φ` (body variables `0, …, a - 1` are the source
tuple, `a, …, 2 * a - 1` the target tuple), applied to the variable tuples
`xs` and `ys`. -/
inductive TCFO where
  | eq : ℕ → ℕ → TCFO
  | rel : ℕ → List ℕ → TCFO
  | not : TCFO → TCFO
  | and : TCFO → TCFO → TCFO
  | or : TCFO → TCFO → TCFO
  | exists : TCFO → TCFO
  | tc : TCFO → List ℕ → List ℕ → TCFO

/-- The meaning of relation symbol `i` in an ordered graph: symbol `0` is `<`, symbol
`1` is the edge relation, other symbols are false. -/
def tcBase (G : TCOrderedGraph) (i : ℕ) : List (Fin G.1) → Prop :=
  match i with
  | 0 => fun args => match args with
    | [a, b] => a.val < b.val
    | _ => False
  | 1 => fun args => match args with
    | [a, b] => tcEdge G a b
    | _ => False
  | _ => fun _ => False

/-- Evaluation of a first-order formula with transitive closure in an ordered graph,
with variable assignment `ρ` and relation assignment `S`. -/
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

/-- Parameterized transitive closure, as a focused example: reachability from outer
variable `1` to outer variable `2` where each step is either a direct edge, or a
two-step path through outer variable `0`. In the `TC` body, de Bruijn indices `0`
and `1` are the path endpoints, index `2` is the parameter (outer variable `0`), and
the endpoint args `[1]` and `[2]` at the `TC` node are evaluated as `ρ 1` and `ρ 2`
(the `TC` node's endpoint args are outer variables, not shifted; only variables
inside the body receive the two-position shift, here by `2 * 1 = 2`). -/
def tcParamExample : TCFO :=
  .tc (.or (.rel 1 [0, 1])
    (.and (.rel 1 [0, 2]) (.rel 1 [2, 1]))) [1] [2]

/-- Transitive closure over pairs of domain elements, as a focused example of
tuple closure of arity `2`: a step moves both components along edges
simultaneously (body variables `0, 1` are the source pair, `2, 3` the target
pair), so `TC` over pairs expresses simultaneous reachability. The endpoint
tuples are the outer variables `[0, 1]` and `[2, 3]`. -/
def tcPairExample : TCFO :=
  .tc (.and (.rel 1 [0, 2]) (.rel 1 [1, 3])) [0, 1] [2, 3]

/-- An ordered graph satisfies an `FO + TC` sentence `φ`. -/
def tcSat (G : TCOrderedGraph) (h : 0 < G.1) (φ : TCFO) : Prop :=
  tcEval G (fun _ => ⟨0, h⟩) (tcBase G) φ

open Classical in
/-- The encodings of a class of ordered graphs, as a decision problem. -/
noncomputable def tcEncodings (K : Set TCOrderedGraph) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x => decide (∃ G ∈ K,
    MetaMathlibExt.BitstringEncoding.bitDecode x = some G ∧ G.2.length = G.1 * G.1)

/-- `K` is `FO + TC`-definable if some `FO + TC` sentence is true exactly on its
canonical members, with the empty structure's membership given by a separate Boolean. -/
def tcDefinable (K : Set TCOrderedGraph) : Prop :=
  ∃ φ, ∃ emptyIn : Bool, ∀ G : TCOrderedGraph, G.2.length = G.1 * G.1 →
    (G ∈ K ↔ (if h : 0 < G.1 then tcSat G h φ else emptyIn = true))

/-- **Immerman: FO + transitive closure is NL on ordered structures.** Source: N.
Immerman, "Languages that capture complexity classes", SIAM Journal on Computing 16
(1987), 760-778 (STOC 1983). -/
public theorem_wanted fo_tc_eq_nl :
    ∀ K : Set TCOrderedGraph,
      (tcEncodings K ∈ NL ↔ tcDefinable K)

end MetaMathlibExt.Complexity.KeyTheorems.FOTC
