/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIDE-CHAIN POSITIONING (PROTEIN DESIGN) is NP-complete

Source:
N. A. Pierce and E. Winfree, "Protein design is NP-hard", Protein Engineering 15 (2002),
779-782, doi:10.1093/protein/15.10.779;
B. Chazelle, C. Kingsford and M. Singh, "A semidefinite programming approach to side chain
positioning with new rounding strategies", INFORMS Journal on Computing 16 (2004), 380-392,
doi:10.1287/ijoc.1040.0096.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SideChainPositioning

/-!
# SIDE-CHAIN POSITIONING (PROTEIN DESIGN) is NP-complete

INSTANCE: positions `1, …, p`, each with a finite set `Rᵢ` of rotamers (the sets pairwise
disjoint); an integer self energy `E(r)` for every rotamer `r`; an integer pairwise energy
`E(r, s)` for every pair of rotamers; an integer `K`.
QUESTION: is there a choice of one rotamer `rᵢ ∈ Rᵢ` at each position `i` whose total energy
`∑ᵢ E(rᵢ) + ∑ᵢ ∑_{j < i} E(rᵢ, rⱼ)` is at most `K`?

The pairwise sum is Pierce and Winfree's `E_total = ∑ᵢ ∑_{j < i} E(rᵢ, rⱼ)`, one term per
unordered pair of positions. Pierce and Winfree state the problem with pairwise terms only and
note that the rotamer self energies used in protein design fold into the pairwise terms; their
problem is the case in which every self energy is `0`. Numbers use the binary encoding.

Positions are `0, …, p - 1` and rotamers are `0, …, R - 1`. The instance lists the position of
each rotamer, so `Rᵢ` is the set of rotamers listed at position `i` and the sets are disjoint by
construction. The self energies are a list of `R` integers and the pairwise energies an `R × R`
matrix of integers, entry `(r, s)` being `E(r, s)`; an integer is a pair `(a, b)` of naturals
standing for `a - b`. Well-formed instances give every position at least one rotamer, so
`p ≤ R`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `p` of positions, the position of each rotamer, the self energies,
the pairwise energy matrix (rows and columns indexed by rotamers), and the bound `K`. -/
abbrev SideChainPositioningInstance :=
  ℕ × List ℕ × List (ℕ × ℕ) × List (List (ℕ × ℕ)) × (ℕ × ℕ)

/-- The integer `a - b` encoded by the pair `(a, b)`. -/
def intOf (z : ℕ × ℕ) : ℤ := (z.1 : ℤ) - (z.2 : ℤ)

/-- Well-formedness of an instance: every rotamer is at one of the positions `0, …, p - 1`,
every position has at least one rotamer, there is one self energy per rotamer, and the pairwise
energies form an `R × R` matrix. -/
def WellFormed (i : SideChainPositioningInstance) : Prop :=
  (∀ j ∈ i.2.1, j < i.1) ∧ (∀ j < i.1, j ∈ i.2.1) ∧
    i.2.2.1.length = i.2.1.length ∧ i.2.2.2.1.length = i.2.1.length ∧
    ∀ row ∈ i.2.2.2.1, row.length = i.2.1.length

/-- The self energy `E(r)` of rotamer `r`. -/
def selfEnergy (i : SideChainPositioningInstance) (r : ℕ) : ℤ :=
  intOf (i.2.2.1.getD r (0, 0))

/-- The pairwise energy `E(r, s)` of rotamers `r` and `s`. -/
def pairEnergy (i : SideChainPositioningInstance) (r s : ℕ) : ℤ :=
  intOf ((i.2.2.2.1.getD r []).getD s (0, 0))

/-- The total energy `∑ᵢ E(rᵢ) + ∑ᵢ ∑_{j < i} E(rᵢ, rⱼ)` of the choice `c` of rotamers. -/
def totalEnergy (i : SideChainPositioningInstance) (c : Fin i.1 → ℕ) : ℤ :=
  ∑ a, selfEnergy i (c a) + ∑ a, ∑ b ∈ Finset.Iio a, pairEnergy i (c a) (c b)

/-- There is a choice of one rotamer at each position with total energy at most `K`. -/
def SideChainPositioningFeasible (i : SideChainPositioningInstance) : Prop :=
  ∃ c : Fin i.1 → ℕ, (∀ a, c a < i.2.1.length ∧ i.2.1.getD (c a) 0 = a) ∧
    totalEnergy i c ≤ intOf i.2.2.2.2

open Classical in
/-- SIDE-CHAIN POSITIONING as a decision problem over bitstrings. -/
noncomputable def sideChainPositioningDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SideChainPositioningInstance) x with
  | some i => decide (WellFormed i ∧ SideChainPositioningFeasible i)
  | none => false

/-- **SIDE-CHAIN POSITIONING (PROTEIN DESIGN) is NP-complete.** Source: Pierce and Winfree
(2002); Chazelle, Kingsford and Singh (2004). -/
public theorem_wanted sideChainPositioning_npComplete :
    sideChainPositioningDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sideChainPositioningDec

end MetaMathlibExt.Complexity.NPComplete.SideChainPositioning
