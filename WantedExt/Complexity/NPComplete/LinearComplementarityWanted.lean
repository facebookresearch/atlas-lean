/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LINEAR COMPLEMENTARITY is NP-complete

Source:
S. J. Chung, "NP-completeness of the linear complementarity problem", Journal of Optimization
Theory and Applications 60 (1989), 393-399, doi:10.1007/BF00940344.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LinearComplementarity

/-!
# LINEAR COMPLEMENTARITY is NP-complete

INSTANCE: an `n × n` integer matrix `M` and an integer vector `q` of length `n`.
QUESTION: are there vectors `w, z` with `w - M z = q`, `w ≥ 0`, `z ≥ 0` and `wᵀ z = 0`?

Chung (1989) proved that deciding whether a linear complementarity problem `LCP(q, M)` has a
solution is NP-complete. Since `w = M z + q` is determined by `z`, the question asks for a
rational `z ≥ 0` with `M z + q ≥ 0` and `zᵀ (M z + q) = 0`. Solutions are sought over `ℚ`; with
integer data this loses nothing: a solution fixes, for each index, which of `zⱼ` and `wⱼ` is zero,
and the remaining linear feasibility system with integer coefficients has a rational solution
whenever it has a real one.

Numbers use the canonical binary encoding; an integer `a` is a pair `(p, n)` of naturals with
`a = p - n`, as in `ZeroOneILPWanted`. The matrix is given as `n` rows of `n` entries each.

Membership in NP: the certificate is the complementary support (which of `zⱼ`, `wⱼ` may be
nonzero for each `j`), and the remaining linear system is solved in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the dimension `n`, the rows of `M` and the vector `q`; every integer is a pair
`(p, n)` of naturals standing for `p - n`. -/
abbrev LinearComplementarityInstance := ℕ × List (List (ℕ × ℕ)) × List (ℕ × ℕ)

/-- Well-formedness of an instance: `M` has `n` rows of `n` entries and `q` has `n` entries. -/
def WellFormed (i : LinearComplementarityInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧ i.2.2.length = i.1

/-- The entry `M r c` of the matrix, as a rational number. -/
def entry (i : LinearComplementarityInstance) (r c : ℕ) : ℚ :=
  (((i.2.1.getD r []).getD c (0, 0)).1 : ℚ) - (((i.2.1.getD r []).getD c (0, 0)).2 : ℚ)

/-- The entry `q r` of the vector, as a rational number. -/
def qEntry (i : LinearComplementarityInstance) (r : ℕ) : ℚ :=
  ((i.2.2.getD r (0, 0)).1 : ℚ) - ((i.2.2.getD r (0, 0)).2 : ℚ)

/-- The vector `w = M z + q`. -/
def slack (i : LinearComplementarityInstance) (z : Fin i.1 → ℚ) (r : Fin i.1) : ℚ :=
  (∑ c : Fin i.1, entry i r c * z c) + qEntry i r

/-- `LCP(q, M)` has a solution: a rational `z ≥ 0` with `w = M z + q ≥ 0` and `zᵀ w = 0`. -/
def LinearComplementarityFeasible (i : LinearComplementarityInstance) : Prop :=
  ∃ z : Fin i.1 → ℚ, (∀ j, 0 ≤ z j) ∧ (∀ r, 0 ≤ slack i z r) ∧
    ∑ r : Fin i.1, z r * slack i z r = 0

open Classical in
/-- LINEAR COMPLEMENTARITY as a decision problem over bitstrings. -/
noncomputable def linearComplementarityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LinearComplementarityInstance) x with
  | some i => decide (WellFormed i ∧ LinearComplementarityFeasible i)
  | none => false

/-- **LINEAR COMPLEMENTARITY is NP-complete.** Source: Chung (1989). -/
public theorem_wanted linearComplementarity_npComplete :
    linearComplementarityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L linearComplementarityDec

end MetaMathlibExt.Complexity.NPComplete.LinearComplementarity
