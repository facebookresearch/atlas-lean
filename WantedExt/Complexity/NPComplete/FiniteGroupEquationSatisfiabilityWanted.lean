/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EQUATION SATISFIABILITY over a fixed finite nonsolvable group is NP-complete

Source:
M. Goldmann and A. Russell, "The complexity of solving equations over finite groups",
Information and Computation 178 (2002), 253-262, doi:10.1006/inco.2002.3173.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FiniteGroupEquationSatisfiabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FiniteGroupEquationSatisfiability

/-!
# EQUATION SATISFIABILITY over a fixed finite nonsolvable group is NP-complete

Fix a finite group `G` that is not solvable. INSTANCE: an equation `w = 1`, where `w` is a word
over the alphabet `G ∪ X ∪ X⁻¹` of group constants, variables from a set `X`, and formal inverses
of the variables. QUESTION: is there an assignment `σ : X → G` with `σ(w) = 1`, where `σ` is
extended to words by `σ(g) = g` for constants, `σ(x⁻¹) = σ(x)⁻¹`, and multiplication in `G`?

The elements of `G` are numbered by a fixed bijection `e : Fin n ≃ G`, and the variables are
`x₀, x₁, ...`. The word is a list of tokens, read left to right: `(0, c)` is the constant
`e c`, `(1, x)` is the variable `xₓ`, and `(2, x)` is its inverse `xₓ⁻¹`. Solvability is
Mathlib's `Group.IsSolvable`.

Goldmann and Russell prove that deciding whether a single equation over `G` has a solution is
NP-complete for every fixed finite nonsolvable group `G` (and in P for nilpotent `G`).
Changing the numbering `e` changes the instances only by a fixed relabeling of the constants.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EQUATION SATISFIABILITY over a fixed finite nonsolvable group is NP-complete**, for every
numbering `e` of its elements. Source: Goldmann and Russell (2002). -/
public theorem_wanted finiteGroupEquationSatisfiability_npComplete {G : Type*} [Group G] {n : ℕ}
    (hG : ¬ Group.IsSolvable G) (e : Fin n ≃ G) :
    finiteGroupEquationSatisfiabilityDec e ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (finiteGroupEquationSatisfiabilityDec e)

end MetaMathlibExt.Complexity.NPComplete.FiniteGroupEquationSatisfiability
