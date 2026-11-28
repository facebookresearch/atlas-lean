/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEASIBLE BASIS EXTENSION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP4] FEASIBLE BASIS EXTENSION;
K. G. Murty, "A fundamental problem in linear inequalities with applications to the travelling
salesman problem", Mathematical Programming 2 (1972), 296-308, doi:10.1007/BF01584550.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FeasibleBasisExtensionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeasibleBasisExtension

/-!
# FEASIBLE BASIS EXTENSION is NP-complete

Given an `m × n` integer matrix `A` with `m < n`, an integer column vector `a` of length `m`,
and a subset `S` of the columns of `A` with `|S| < m`, is there a feasible basis `B` for
`A x = a, x ≥ 0`, i.e., a nonsingular `m × m` submatrix `B` of `A` such that `B⁻¹ a ≥ 0`, that
contains all the columns in `S`?

A basis is given by an injective choice `σ : Fin m → Fin n` of `m` columns; `B` is the
submatrix of `A` on all rows and the columns `σ`, read over `ℚ`. The order of the chosen
columns only permutes the entries of `B⁻¹ a`, so it does not affect the question. Integers are
encoded as pairs of naturals `(positive part, negative part)`, as in `ZeroOneILPWanted`; all
numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FEASIBLE BASIS EXTENSION is NP-complete.** Source: Garey and Johnson (1979), [MP4];
Murty (1972). -/
public theorem_wanted feasibleBasisExtension_npComplete :
    feasibleBasisExtensionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feasibleBasisExtensionDec

end MetaMathlibExt.Complexity.NPComplete.FeasibleBasisExtension
