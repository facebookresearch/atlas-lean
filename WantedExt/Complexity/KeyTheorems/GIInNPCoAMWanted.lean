/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Graph isomorphism is in NP and coAM

Source:
O. Goldreich, "On the complexity of graph isomorphism" and the Goldreich-Micali-Wigderson
interactive proof for graph non-isomorphism; see J. Köbler, U. Schöning, and J. Torán, The
Graph Isomorphism Problem: Its Structural Complexity, Birkhäuser, 1993.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.GIInNPCoAM

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Graph isomorphism is in NP and coAM

Directed graph isomorphism is in `NP` (the isomorphism is the witness) and its complement is in
`AM`: non-isomorphism has an Arthur-Merlin proof via the set lower-bound protocol. Graphs
decode to `(n, edges₁, edges₂)`; isomorphism is a bijection preserving adjacency in both
directions.
-/

open Classical in
/-- **Directed graph isomorphism as a decision problem.** The decision problem accepts a bitstring
$x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a triple $(n, E_1, E_2)$
of a natural number $n$ and two lists $E_1$ and $E_2$ of pairs of natural numbers for which
there is a bijection $f$ of $\{0, \dots, n - 1\}$ such that for all $a, b < n$, $(a, b) \in E_1$
if and only if $(f(a), f(b)) \in E_2$. Bitstrings that do not decode to such a triple are
rejected.

Pairs in $E_1$ or $E_2$ with an entry at least $n$ play no role. -/
noncomputable def graphIsoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) x with
  | some i => decide (∃ f : Fin i.1 → Fin i.1, Function.Bijective f ∧
      ∀ a b : Fin i.1,
        ((a.val, b.val) ∈ i.2.1 ↔ ((f a).val, (f b).val) ∈ i.2.2))
  | none => false

/-- **Graph isomorphism is in NP and coAM.** The directed graph isomorphism decision problem
belongs to NP and to coAM.

Source: O. Goldreich, "On the complexity of graph
isomorphism" and the Goldreich-Micali-Wigderson interactive proof for graph non-
isomorphism; see J. Köbler, U. Schöning, and J. Torán, The Graph Isomorphism Problem: Its
Structural Complexity, Birkhäuser, 1993. -/
public theorem_wanted graph_iso_in_np_coam :
    graphIsoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧ graphIsoDec ∈ coAM

end MetaMathlibExt.Complexity.KeyTheorems.GIInNPCoAM
