/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMULTANEOUS DIVISIBILITY OF LINEAR POLYNOMIALS for fixed n ≥ 5 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN3] SIMULTANEOUS DIVISIBILITY OF
LINEAR POLYNOMIALS, p. 249 ("Reference: [Lipshitz, 1977], [Lipshitz, 1978]. Transformation from
QUADRATIC DIOPHANTINE EQUATIONS. Comment: Not known to be in NP, but belongs to NP for any fixed
n. NP-complete for any fixed n ≥ 5.");
L. Lipshitz, "The Diophantine problem for addition and divisibility", Transactions of the
American Mathematical Society 235 (1978), 271-283, doi:10.1090/S0002-9947-1978-0469886-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SimultaneousDivisibilityOfLinearPolynomialsFixedNDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimultaneousDivisibilityOfLinearPolynomialsFixedN

/-!
# SIMULTANEOUS DIVISIBILITY OF LINEAR POLYNOMIALS for fixed n ≥ 5 is NP-complete

For a fixed number `n ≥ 5` of divisibilities: INSTANCE: vectors
`aᵢ = (aᵢ[0], …, aᵢ[m])` and `bᵢ = (bᵢ[0], …, bᵢ[m])`, `1 ≤ i ≤ n`, with positive integer
entries. QUESTION: do there exist positive integers `x₁, x₂, …, x_m` such that, for
`1 ≤ i ≤ n`, `aᵢ[0] + ∑_{j=1}^{m} aᵢ[j] xⱼ` divides `bᵢ[0] + ∑_{j=1}^{m} bᵢ[j] xⱼ`?

Garey and Johnson record that the problem with `n` part of the instance is not known to be in
NP, that it belongs to NP for every fixed `n`, and that it is NP-complete for every fixed
`n ≥ 5`; the last claim is stated here, with `n` a parameter of the decision problem and of the
theorem, and the number of listed pairs `(aᵢ, bᵢ)` fixed to `n` in `WellFormed n`. The variables
are `x : Fin m → ℕ`, with `x j` standing for `x_{j+1}`. All numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SIMULTANEOUS DIVISIBILITY OF LINEAR POLYNOMIALS is NP-complete for every fixed number
`n ≥ 5` of divisibilities.** Source: Garey and Johnson (1979), [AN3]; Lipshitz (1977, 1978). -/
public theorem_wanted simultaneousDivisibilityFixedN_npComplete (n : ℕ) (hn : 5 ≤ n) :
    simultaneousDivisibilityFixedNDec n ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (simultaneousDivisibilityFixedNDec n)

end MetaMathlibExt.Complexity.NPComplete.SimultaneousDivisibilityOfLinearPolynomialsFixedN
