/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BALANCED MINIMUM EVOLUTION is NP-complete

Source:
S. Fiorini and G. Joret, "Approximating the balanced minimum evolution problem", Operations
Research Letters 40 (2012), 31-35, doi:10.1016/j.orl.2011.10.003 (arXiv:1104.1080), Theorem 3.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.Tree.WeightedLeafDistance

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BalancedMinimumEvolution

open MathlibExt.Biology.Phylogenetics.BalancedMinimumEvolution (UTree)

/-!
# BALANCED MINIMUM EVOLUTION is NP-complete

INSTANCE: a set `[n]` of species and an `n × n` symmetric matrix `(δᵢⱼ)` of nonnegative rationals
with zeroes on the diagonal (the dissimilarities), and a rational bound `L`. QUESTION: is there a
cubic tree `T` (every internal vertex has degree `3`) with `n` leaves, together with a bijection
between the leaves of `T` and the `n` species, whose balanced minimum-evolution length
`∑_{i<j} δᵢⱼ 2^{1 - dᵢⱼ}` is at most `L`, where `dᵢⱼ` is the number of edges between the leaves
of species `i` and `j` in `T`?

Fiorini and Joret minimize `f(T) = ∑_{i≠j} δᵢⱼ 2^{1-dᵢⱼ} = ∑_{i<j} δᵢⱼ 2^{2-dᵢⱼ}`, twice the
length above (their Section 1); the factor `2` rescales `L` and does not change the problem.
Their Theorem 3.1 shows that the problem has no `cⁿ`-approximation unless P = NP, by a
reduction from 3-COLORABILITY whose instances have all `δᵢⱼ ∈ {0, 1}`; in particular the
decision problem is NP-hard.

Trees reuse `MathlibExt.Combinatorics.Tree.WeightedLeafDistance`: a `UTree` is a cubic
tree rooted at an edge (two rooted binary trees joined by an edge); every cubic tree with at
least two leaves arises this way, and its `bmeLength` for a symmetric dissimilarity is
`∑_{i<j} 2^{1-τᵢⱼ} δᵢⱼ`, which depends only on the topology (the edge lengths of the `UTree` are
not read). The bijection is `T.labels ~ [0, …, n - 1]` (each species labels exactly one leaf). A
cubic tree has no vertex of degree `0`, so no cubic tree has exactly one leaf (or none), and
instances with `n ≤ 1` are no-instances, as here. Entries and `L` are pairs `(a, b)` of naturals
meaning `a / b` with `0 < b`; symmetry is compared by cross-multiplication. Numbers use the
binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of species, the rows of the dissimilarity matrix (entry `(a, b)`
meaning `a / b`), and the bound `L` as a pair `(a, b)` meaning `a / b`. -/
abbrev BalancedMinimumEvolutionInstance := ℕ × List (List (ℕ × ℕ)) × (ℕ × ℕ)

/-- The entry `δᵢⱼ` of the matrix, as a pair `(a, b)` meaning `a / b`. -/
def entry (inst : BalancedMinimumEvolutionInstance) (i j : Fin inst.1) : ℕ × ℕ :=
  (inst.2.1.getD i []).getD j (0, 1)

/-- The dissimilarity `δᵢⱼ = a / b` as a real number. -/
noncomputable def dissim (inst : BalancedMinimumEvolutionInstance) (i j : Fin inst.1) : ℝ :=
  ((entry inst i j).1 : ℝ) / (entry inst i j).2

/-- Well-formedness of an instance: the matrix has `n` rows of `n` entries, every entry has a
positive denominator, the diagonal is zero, the matrix is symmetric (`δᵢⱼ = δⱼᵢ`), and `L` has a
positive denominator. -/
def WellFormed (inst : BalancedMinimumEvolutionInstance) : Prop :=
  inst.2.1.length = inst.1 ∧ (∀ r ∈ inst.2.1, r.length = inst.1 ∧ ∀ q ∈ r, 0 < q.2) ∧
    (∀ i, (entry inst i i).1 = 0) ∧
    (∀ i j, (entry inst i j).1 * (entry inst j i).2 = (entry inst j i).1 * (entry inst i j).2) ∧
    0 < inst.2.2.2

/-- Some cubic tree whose leaves are labelled by the `n` species, each exactly once, has balanced
minimum-evolution length at most `L`. -/
def BalancedMinimumEvolutionFeasible (inst : BalancedMinimumEvolutionInstance) : Prop :=
  ∃ T : UTree (Fin inst.1), T.labels.Perm (List.finRange inst.1) ∧
    T.bmeLength (dissim inst) ≤ (inst.2.2.1 : ℝ) / inst.2.2.2

open Classical in
/-- BALANCED MINIMUM EVOLUTION as a decision problem over bitstrings. -/
noncomputable def balancedMinimumEvolutionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BalancedMinimumEvolutionInstance) x with
  | some i => decide (WellFormed i ∧ BalancedMinimumEvolutionFeasible i)
  | none => false

/-- **BALANCED MINIMUM EVOLUTION is NP-complete.** Source: Fiorini and Joret (2012),
Theorem 3.1. -/
public theorem_wanted balancedMinimumEvolution_npComplete :
    balancedMinimumEvolutionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L balancedMinimumEvolutionDec

end MetaMathlibExt.Complexity.NPComplete.BalancedMinimumEvolution
