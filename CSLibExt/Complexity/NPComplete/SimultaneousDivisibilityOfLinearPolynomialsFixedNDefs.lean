/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMULTANEOUS DIVISIBILITY OF LINEAR POLYNOMIALS for fixed n ≥ 5: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimultaneousDivisibilityOfLinearPolynomialsFixedN

/-- An instance: the number `m` of variables and the pairs `(aᵢ, bᵢ)` of coefficient vectors,
each a list `(v[0], …, v[m])`. -/
abbrev SimultaneousDivisibilityInstance := ℕ × List (List ℕ × List ℕ)

/-- Well-formedness of an instance for `n` divisibilities: there are exactly `n` pairs, every
vector has `m + 1` entries, and every entry is positive. -/
def WellFormed (n : ℕ) (i : SimultaneousDivisibilityInstance) : Prop :=
  i.2.length = n ∧ ∀ p ∈ i.2, p.1.length = i.1 + 1 ∧ p.2.length = i.1 + 1 ∧
    (∀ c ∈ p.1, 0 < c) ∧ ∀ c ∈ p.2, 0 < c

/-- The value `v[0] + ∑_{j=1}^{m} v[j] xⱼ` of the linear polynomial with coefficients `v` at
`x : Fin m → ℕ` (`x j` is `x_{j+1}`). -/
def linearValue {m : ℕ} (v : List ℕ) (x : Fin m → ℕ) : ℕ :=
  v.getD 0 0 + ∑ j : Fin m, v.getD (j + 1) 0 * x j

/-- Some positive integers `x₁, …, x_m` make `aᵢ[0] + ∑ aᵢ[j] xⱼ` divide
`bᵢ[0] + ∑ bᵢ[j] xⱼ` for every pair `(aᵢ, bᵢ)`. -/
def SimultaneousDivisibilityFeasible (i : SimultaneousDivisibilityInstance) : Prop :=
  ∃ x : Fin i.1 → ℕ, (∀ j, 0 < x j) ∧ ∀ p ∈ i.2, linearValue p.1 x ∣ linearValue p.2 x

open Classical in
/-- SIMULTANEOUS DIVISIBILITY OF LINEAR POLYNOMIALS with `n` divisibilities as a decision
problem over bitstrings. -/
noncomputable def simultaneousDivisibilityFixedNDec (n : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SimultaneousDivisibilityInstance) x with
  | some i => decide (WellFormed n i ∧ SimultaneousDivisibilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimultaneousDivisibilityOfLinearPolynomialsFixedN
