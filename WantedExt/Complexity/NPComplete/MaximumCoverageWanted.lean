/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM COVERAGE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SET COVER: maximum
coverage with target `M = n` is exactly set cover (at most `K` sets covering all `n` elements).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumCoverage

/-!
# MAXIMUM COVERAGE is NP-complete

A universe of size `n`, a list of subsets, a bound `K` on the number of sets, and a target `M`.
The question is whether at most `K` subsets cover at least `M` universe elements.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A maximum-coverage instance: universe size, list of subsets, set budget K, coverage target
M. -/
abbrev MaximumCoverageInstance := ℕ × List (List ℕ) × ℕ × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : MaximumCoverageInstance) : Prop :=
  ∀ s ∈ i.2.1, s.Nodup ∧ ∀ x ∈ s, x < i.1

/-- At most `K` sets covering at least `M` elements. -/
def MaximumCoverageFeasible
    (i : MaximumCoverageInstance) : Prop :=
  ∃ T : List (List ℕ), T.Sublist i.2.1 ∧ T.length ≤ i.2.2.1 ∧
    ∃ covered : List ℕ, covered.Nodup ∧ i.2.2.2 ≤ covered.length ∧
      ∀ x ∈ covered, x < i.1 ∧ ∃ s ∈ T, x ∈ s

open Classical in
/-- MAXIMUM COVERAGE as a decision problem over bitstrings. -/
noncomputable def maximumCoverageDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumCoverageInstance) x with
  | some i => decide (WellFormed i ∧ MaximumCoverageFeasible i)
  | none => false

/-- **MAXIMUM COVERAGE is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), SET COVER: maximum coverage with target `M = n` is exactly set
cover (at most `K` sets covering all `n` elements). -/
public theorem_wanted maximumCoverage_npComplete :
    maximumCoverageDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumCoverageDec

end MetaMathlibExt.Complexity.NPComplete.MaximumCoverage
