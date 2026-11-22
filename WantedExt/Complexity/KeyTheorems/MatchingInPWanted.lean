/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# General matching is in P (Edmonds' blossom algorithm)

Source:
J. Edmonds, "Paths, trees, and flowers", Canadian Journal of Mathematics 17 (1965), 449-467.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.MatchingInP

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# General matching is in P (Edmonds' blossom algorithm)

The general (non-bipartite) matching decision problem is in `P`, by Edmonds' blossom algorithm.
The instance is a vertex count, an edge list, and a target `K`; the question is whether some
`K` pairwise vertex-disjoint edges exist. Well-formedness requires every edge's endpoints below
`n` and distinct; the matching is `Nodup`, so a duplicated edge in the input cannot be counted
twice.
-/

open Classical in
/-- **General matching decision problem.** The decision problem that accepts a bitstring $x$
exactly when $x$ decodes, under the canonical bitstring encoding, to a triple $(n, E, K)$ of a
natural number $n$, a list $E$ of pairs of natural numbers and a natural number $K$ such that
every pair $(u, v)$ in $E$ has $u < n$, $v < n$ and $u \neq v$, and some sublist $M$ of $E$
(a subsequence, keeping the order of $E$) with no repeated entries and length at least $K$ has
the property that any two different pairs $(u_1, v_1)$ and $(u_2, v_2)$ in $M$ share no
element: $u_1, v_1 \notin \{u_2, v_2\}$. Bitstrings that do not decode are rejected. -/
noncomputable def matchingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List (ℕ × ℕ) × ℕ) x with
  | some i => decide (
      (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧
      ∃ matching : List (ℕ × ℕ), matching.Sublist i.2.1 ∧ matching.Nodup ∧
        matching.length ≥ i.2.2 ∧
        ∀ e₁ ∈ matching, ∀ e₂ ∈ matching, e₁ ≠ e₂ →
          e₁.1 ≠ e₂.1 ∧ e₁.1 ≠ e₂.2 ∧ e₁.2 ≠ e₂.1 ∧ e₁.2 ≠ e₂.2)
  | none => false

/-- **General matching is in P (Edmonds' blossom algorithm).** The general matching decision
problem belongs to the complexity class P. This is the problem of deciding, for a vertex count
$n$, a list $E$ of edges joining distinct vertices below $n$ and a target $K$, encoded as a
bitstring, whether $E$ contains at least $K$ distinct pairwise vertex-disjoint edges.

Source: J. Edmonds, "Paths,
trees, and flowers", Canadian Journal of Mathematics 17 (1965), 449-467. -/
public theorem_wanted matching_in_p :
    matchingDec ∈ MetaMathlibExt.ComplexityTheory.P

end MetaMathlibExt.Complexity.KeyTheorems.MatchingInP
