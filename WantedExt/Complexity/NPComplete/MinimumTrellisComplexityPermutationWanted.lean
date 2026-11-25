/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM TRELLIS COMPLEXITY UNDER COORDINATE PERMUTATION is NP-complete

Source:
N. Kashyap, "Matroid pathwidth and code trellis complexity", SIAM Journal on Discrete
Mathematics 22 (2008), 256-272, doi:10.1137/070691152 (Corollary 3.3 and Section 4; the
problem is "Trellis State-Complexity" of Vardy and "Maximum Partition Rank Permutation" of
G. B. Horn and F. R. Kschischang, IEEE Transactions on Information Theory 42 (1996), 2042-2048,
doi:10.1109/18.556701, who conjectured it NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumTrellisComplexityPermutation

/-!
# MINIMUM TRELLIS COMPLEXITY UNDER COORDINATE PERMUTATION is NP-complete

INSTANCE: a binary linear code `C` of length `n`, given by a generator matrix `G` over `GF(2)`
(a matrix whose row space is `C`), and a positive integer `w`.
QUESTION: is there an ordering `(e₁, …, eₙ)` of the coordinates of `C` such that, for every
`1 ≤ i ≤ n`, the state complexity at depth `i` of the minimal trellis of `C` in that order,
`λ({e₁, …, eᵢ}) = r({e₁, …, eᵢ}) + r({eᵢ₊₁, …, eₙ}) - r(E)`, is at most `w`, i.e. is the
trellis-width of `C` at most `w`?

Kashyap (Section 2) defines the trellis-width of `C` as the pathwidth of its vector matroid
`M(C)`, the minimum over all orderings of the coordinates of the maximum of the connectivity
function `λ(X) = r(X) + r(E - X) - r(E)` over the initial segments `X = {e₁, …, eᵢ}`, where
`r(J) = dim(C|J)` is the rank of the columns of `G` indexed by `J`; Corollary 3.3 and Section 4
show that deciding whether the trellis-width is at most `w` is NP-complete over every fixed
finite field, in particular over `GF(2)`. Here `GF(2)` is `ZMod 2`, the generator matrix is the
list of its `k` rows, each a list of `n` bits (`column`), the coordinates are `Fin n`, `r(J)` is
Mathlib's `Set.finrank` of the columns indexed by `J` (`coordRank`), and an ordering is a
permutation `π` of `Fin n` with `eᵢ = π (i - 1)`. Since `r(X) + r(E - X) ≥ r(E)`, the bound
`λ(X) ≤ w` is written without subtraction as `r(X) + r(E - X) ≤ w + r(E)`. A permutation, with
the ranks it determines (Gaussian elimination), is a polynomial-size certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the length `n` of the code, the rows of the generator matrix `G` (`k` rows, each
a list of `n` bits), and the bound `w`. -/
abbrev MinimumTrellisComplexityPermutationInstance := ℕ × List (List Bool) × ℕ

/-- The column `j` of the generator matrix, a vector in `(ZMod 2)ᵏ` with entry `1` in row `r`
exactly when the bit `G[r][j]` is set. -/
def column (i : MinimumTrellisComplexityPermutationInstance) (j : Fin i.1) :
    Fin i.2.1.length → ZMod 2 :=
  fun r => if (i.2.1.getD r []).getD j false then 1 else 0

/-- The rank `r(J)` of a set `J` of coordinates: the dimension of the span of the columns of `G`
indexed by `J`, i.e. `dim(C|J)`, the rank function of the vector matroid `M(C)`. -/
noncomputable def coordRank (i : MinimumTrellisComplexityPermutationInstance)
    (J : Set (Fin i.1)) : ℕ :=
  Set.finrank (ZMod 2) (column i '' J)

/-- Well-formedness of an instance: every row of `G` has `n` bits, and `w` is positive. -/
def WellFormed (i : MinimumTrellisComplexityPermutationInstance) : Prop :=
  (∀ row ∈ i.2.1, row.length = i.1) ∧ 0 < i.2.2

/-- Some ordering `(e₁, …, eₙ) = (π 0, …, π (n - 1))` of the coordinates has width at most `w`:
for every `1 ≤ t ≤ n`, the initial segment `X = {e₁, …, eₜ}` (the coordinates `j` with
`π⁻¹ j < t`) satisfies `r(X) + r(E - X) ≤ w + r(E)`, i.e. `λ(X) ≤ w`. -/
def MinimumTrellisComplexityPermutationFeasible
    (i : MinimumTrellisComplexityPermutationInstance) : Prop :=
  ∃ π : Equiv.Perm (Fin i.1), ∀ t : ℕ, 1 ≤ t → t ≤ i.1 →
    coordRank i {j | (π.symm j : ℕ) < t} + coordRank i {j | t ≤ (π.symm j : ℕ)} ≤
      i.2.2 + coordRank i Set.univ

open Classical in
/-- MINIMUM TRELLIS COMPLEXITY UNDER COORDINATE PERMUTATION as a decision problem over
bitstrings. -/
noncomputable def minimumTrellisComplexityPermutationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumTrellisComplexityPermutationInstance) x with
  | some i => decide (WellFormed i ∧ MinimumTrellisComplexityPermutationFeasible i)
  | none => false

/-- **MINIMUM TRELLIS COMPLEXITY UNDER COORDINATE PERMUTATION is NP-complete.** Source:
Kashyap (2008), Corollary 3.3 and Section 4. -/
public theorem_wanted minimumTrellisComplexityPermutation_npComplete :
    minimumTrellisComplexityPermutationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumTrellisComplexityPermutationDec

end MetaMathlibExt.Complexity.NPComplete.MinimumTrellisComplexityPermutation
