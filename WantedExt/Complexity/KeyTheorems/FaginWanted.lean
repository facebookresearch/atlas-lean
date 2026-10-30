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

/-- A finite graph: domain size and a row-major edge table. -/
abbrev FaginGraph := ℕ × List Bool

/-- The edge relation of a graph on `Fin n`. -/
def faginEdge (G : FaginGraph) (a b : Fin G.1) : Prop :=
  G.2.getD (a.val * G.1 + b.val) false = true

/-- First-order formulas over finite graphs: variables are naturals (de Bruijn: `exists`
binds variable `0`), relation symbol `i` is applied to a list of variables. -/
inductive FaginFO where
  | eq : ℕ → ℕ → FaginFO
  | rel : ℕ → List ℕ → FaginFO
  | not : FaginFO → FaginFO
  | and : FaginFO → FaginFO → FaginFO
  | or : FaginFO → FaginFO → FaginFO
  | exists : FaginFO → FaginFO

/-- Evaluation of a first-order formula in a graph, with variable assignment `ρ` and
relation assignment `S`. -/
def faginEval (G : FaginGraph) (ρ : ℕ → Fin G.1)
    (S : ℕ → List (Fin G.1) → Prop) : FaginFO → Prop
  | .eq a b => ρ a = ρ b
  | .rel i args => S i (args.map ρ)
  | .not φ => ¬ faginEval G ρ S φ
  | .and φ ψ => faginEval G ρ S φ ∧ faginEval G ρ S ψ
  | .or φ ψ => faginEval G ρ S φ ∨ faginEval G ρ S ψ
  | .exists φ => ∃ a : Fin G.1,
      faginEval G (fun j => match j with | 0 => a | j + 1 => ρ j) S φ

/-- The meaning of relation symbol `i`: symbol `0` is the edge relation, other symbols
are the supplied second-order relations. -/
def faginBase (G : FaginGraph) (extra : ℕ → List (Fin G.1) → Prop)
    (i : ℕ) : List (Fin G.1) → Prop :=
  if i = 0 then fun args => match args with
    | [a, b] => faginEdge G a b
    | _ => False
  else extra (i - 1)

/-- A graph satisfies an `∃SO` sentence `(k, φ)`: there are `k` second-order relations
making `φ` true. -/
def faginESOSat (G : FaginGraph) (h : 0 < G.1) (k : ℕ) (φ : FaginFO) : Prop :=
  ∃ R : (j : Fin k) → List (Fin G.1) → Prop,
    faginEval G (fun _ => ⟨0, h⟩)
      (faginBase G (fun j => if h' : j < k then R ⟨j, h'⟩ else fun _ => False)) φ

open Classical in
/-- The encodings of a class of graphs, as a decision problem: only canonical
encodings (edge table of length `n * n`) count. -/
noncomputable def faginEncodings (K : Set FaginGraph) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x => decide (∃ G ∈ K,
    MetaMathlibExt.BitstringEncoding.bitDecode x = some G ∧ G.2.length = G.1 * G.1)

/-- Graph isomorphism: an edge-preserving bijection of the domains. -/
def faginIso (G₁ G₂ : FaginGraph) : Prop :=
  G₁.1 = G₂.1 ∧ ∃ σ : Fin G₁.1 ≃ Fin G₂.1,
    ∀ a b : Fin G₁.1, faginEdge G₁ a b ↔ faginEdge G₂ (σ a) (σ b)

/-- A class of graphs is isomorphism-closed if it contains all isomorphic copies of its
members. -/
def faginIsoClosed (K : Set FaginGraph) : Prop :=
  ∀ G₁ ∈ K, ∀ G₂ : FaginGraph, faginIso G₁ G₂ → G₂ ∈ K

/-- `K` is `∃SO`-definable if some `∃SO` sentence is true exactly on its canonical
members, with the empty graph's membership given by a separate Boolean. -/
def faginESODefinable (K : Set FaginGraph) : Prop :=
  ∃ k φ, ∃ emptyIn : Bool, ∀ G : FaginGraph, G.2.length = G.1 * G.1 →
    (G ∈ K ↔ (if h : 0 < G.1 then faginESOSat G h k φ else emptyIn = true))

/-- **Fagin's theorem: NP is existential second-order logic.** Source: R. Fagin,
"Generalized first-order spectra and polynomial-time recognizable sets", in Complexity of
Computation, SIAM-AMS Proceedings 7 (1974), 43-73. -/
public theorem_wanted fagin :
    ∀ K : Set FaginGraph, faginIsoClosed K →
      (faginEncodings K ∈ MetaMathlibExt.ComplexityTheory.NP ↔ faginESODefinable K)

end MetaMathlibExt.Complexity.KeyTheorems.Fagin
