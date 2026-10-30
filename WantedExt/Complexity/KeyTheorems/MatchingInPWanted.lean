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
/-- General matching decision problem over bitstrings. -/
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

/-- **General matching is in P (Edmonds' blossom algorithm).** Source: J. Edmonds, "Paths,
trees, and flowers", Canadian Journal of Mathematics 17 (1965), 449-467. -/
public theorem_wanted matching_in_p :
    matchingDec ∈ MetaMathlibExt.ComplexityTheory.P

end MetaMathlibExt.Complexity.KeyTheorems.MatchingInP
