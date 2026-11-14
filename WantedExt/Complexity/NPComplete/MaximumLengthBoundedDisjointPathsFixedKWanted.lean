/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM LENGTH-BOUNDED DISJOINT PATHS with fixed `K ≥ 5` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND41] MAXIMUM
LENGTH-BOUNDED DISJOINT PATHS, p. 217 (comment: "Remains NP-complete for all fixed `K ≥ 5`");
A. Itai, Y. Perl, and Y. Shiloach, "The complexity of finding maximum disjoint
paths with length constraints", Networks 12 (1982), 277-286,
doi:10.1002/net.3230120306.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPathsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPathsFixedK

open MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPaths

/-!
# MAXIMUM LENGTH-BOUNDED DISJOINT PATHS with fixed `K ≥ 5` is NP-complete

For a fixed constant `K ≥ 5`: given a graph `G = (V, E)`, specified vertices `s` and `t`, and a
positive integer `J ≤ |V|`, does `G` contain `J` or more mutually vertex-disjoint paths from `s`
to `t`, none involving more than `K` edges?

Garey and Johnson state that MAXIMUM LENGTH-BOUNDED DISJOINT PATHS remains NP-complete for
every fixed `K ≥ 5` (and is polynomial for `K ≤ 4`). This is the restriction of MAXIMUM
LENGTH-BOUNDED DISJOINT PATHS
(`WantedExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPathsWanted`) in which `K` is no
longer part of the instance. The instance is the graph, `s`, `t` and `J`, and
`withBound i K` appends the fixed `K` to obtain an instance of that problem, whose `WellFormed`
(including the source's `K ≤ |V|`) and `MaximumLengthBoundedDisjointPathsFeasible` are reused
unchanged.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance for a fixed bound: vertex count `n` (vertices `0, ..., n - 1`), edge list,
`s`, `t`, `J`. -/
abbrev FixedBoundInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The MAXIMUM LENGTH-BOUNDED DISJOINT PATHS instance given by `i` and the bound `K`. -/
abbrev withBound (i : FixedBoundInstance) (K : ℕ) : MaximumLengthBoundedDisjointPathsInstance :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2, K)

open Classical in
/-- MAXIMUM LENGTH-BOUNDED DISJOINT PATHS with the bound fixed to `K`, as a decision problem
over bitstrings. -/
noncomputable def fixedBoundDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FixedBoundInstance) x with
  | some i => decide (WellFormed (withBound i K) ∧
      MaximumLengthBoundedDisjointPathsFeasible (withBound i K))
  | none => false

/-- **MAXIMUM LENGTH-BOUNDED DISJOINT PATHS is NP-complete for every fixed `K ≥ 5`.** Source:
Garey and Johnson (1979), [ND41], comment; Itai, Perl, and Shiloach (1982). -/
public theorem_wanted maximumLengthBoundedDisjointPathsFixedK_npComplete (K : ℕ) (hK : 5 ≤ K) :
    fixedBoundDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (fixedBoundDec K)

end MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPathsFixedK
