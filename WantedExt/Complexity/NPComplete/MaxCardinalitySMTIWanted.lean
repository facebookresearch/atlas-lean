/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAX CARDINALITY SMTI (maximum stable marriage with ties and incomplete lists) is NP-complete

Source:
D. F. Manlove, R. W. Irving, K. Iwama, S. Miyazaki, and Y. Morita, "Hard variants of stable
marriage", Theoretical Computer Science 276(1-2) (2002), 261-279,
doi:10.1016/S0304-3975(01)00206-7, Section 2 (problem MAX CARDINALITY SMTI; Lemma 2.1 and
Theorem 2.2: NP-complete, even with ties on one side only);
K. Iwama, D. Manlove, S. Miyazaki, and Y. Morita, "Stable marriage with incomplete lists and
ties", Proc. ICALP 1999, Lecture Notes in Computer Science 1644 (1999), 443-452,
doi:10.1007/3-540-48523-6_41.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxCardinalitySMTI

/-!
# MAX CARDINALITY SMTI is NP-complete

INSTANCE: `n` men and `n` women, a preference list of women for each man and a preference list
of men for each woman, each list possibly incomplete and possibly with ties, and an integer
`K ∈ ℤ⁺`. QUESTION: does the instance admit a stable matching `M` with `|M| ≥ K`?

Person `p` is acceptable to `q` if `p` appears on `q`'s list. A matching is a set of
(man, woman) pairs, each person in at most one pair, such that in every pair each finds the
other acceptable. It is (weakly) stable if there is no pair `(m, w)` each of whom is either
unmatched and finds the other acceptable, or strictly prefers the other to their partner.

The men and the women are `Fin n`. A preference list is a list of ties, each tie a list of
people in the tie, best first: `p` is acceptable to `q` iff `p` is in some tie of `q`'s list,
and `q` strictly prefers `p` to `p'` iff `p` is acceptable to `q` and lies in an earlier tie
than `p'`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of men and of women, the men's preference lists, the women's
preference lists (each a list of ties, best first), and the bound `K`. -/
abbrev MaxCardinalitySMTIInstance :=
  ℕ × List (List (List ℕ)) × List (List (List ℕ)) × ℕ

/-- `p` is acceptable on the preference list `L`: it lies in some tie of `L`. -/
def Acceptable (L : List (List ℕ)) (p : ℕ) : Prop :=
  ∃ t ∈ L, p ∈ t

/-- The position of the tie containing `p` on the list `L` (`L.length` if `p` is not on it). -/
def tieIndex (L : List (List ℕ)) (p : ℕ) : ℕ :=
  L.findIdx fun t => p ∈ t

/-- The owner of the list `L` strictly prefers `p` to `p'`: `p` is on `L`, in an earlier tie
than `p'`. -/
def StrictlyPrefers (L : List (List ℕ)) (p p' : ℕ) : Prop :=
  Acceptable L p ∧ tieIndex L p < tieIndex L p'

/-- Man `m`'s preference list. -/
def manList (i : MaxCardinalitySMTIInstance) (m : Fin i.1) : List (List ℕ) :=
  i.2.1.getD m []

/-- Woman `w`'s preference list. -/
def womanList (i : MaxCardinalitySMTIInstance) (w : Fin i.1) : List (List ℕ) :=
  i.2.2.1.getD w []

/-- `M` is a matching: every pair is mutually acceptable, and every man and every woman is in at
most one pair. -/
def IsMatching (i : MaxCardinalitySMTIInstance) (M : Finset (Fin i.1 × Fin i.1)) : Prop :=
  (∀ p ∈ M, Acceptable (manList i p.1) p.2 ∧ Acceptable (womanList i p.2) p.1) ∧
    (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) ∧ (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q)

/-- The pair `(m, w)` blocks `M`: each of `m` and `w` is either unmatched in `M` and finds the
other acceptable, or strictly prefers the other to their partner in `M`. -/
def Blocks (i : MaxCardinalitySMTIInstance) (M : Finset (Fin i.1 × Fin i.1))
    (m w : Fin i.1) : Prop :=
  ((∀ w', (m, w') ∉ M) ∧ Acceptable (manList i m) w ∨
      ∃ w', (m, w') ∈ M ∧ StrictlyPrefers (manList i m) w w') ∧
    ((∀ m', (m', w) ∉ M) ∧ Acceptable (womanList i w) m ∨
      ∃ m', (m', w) ∈ M ∧ StrictlyPrefers (womanList i w) m m')

/-- Well-formedness of an instance: there are `n` lists on each side, every listed person is
among the `n` people of the other sex, no list names anyone twice, and `K` is positive. -/
def WellFormed (i : MaxCardinalitySMTIInstance) : Prop :=
  i.2.1.length = i.1 ∧ i.2.2.1.length = i.1 ∧
    (∀ L ∈ i.2.1 ++ i.2.2.1, L.flatten.Nodup ∧ ∀ p ∈ L.flatten, p < i.1) ∧ 0 < i.2.2.2

/-- Some stable matching has at least `K` pairs. -/
def MaxCardinalitySMTIFeasible (i : MaxCardinalitySMTIInstance) : Prop :=
  ∃ M : Finset (Fin i.1 × Fin i.1), IsMatching i M ∧ (∀ m w, ¬ Blocks i M m w) ∧
    i.2.2.2 ≤ M.card

open Classical in
/-- MAX CARDINALITY SMTI as a decision problem over bitstrings. -/
noncomputable def maxCardinalitySMTIDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCardinalitySMTIInstance) x with
  | some i => decide (WellFormed i ∧ MaxCardinalitySMTIFeasible i)
  | none => false

/-- **MAX CARDINALITY SMTI is NP-complete.** Source: Manlove, Irving, Iwama, Miyazaki, and
Morita (2002), Lemma 2.1; Iwama, Manlove, Miyazaki, and Morita (1999). -/
public theorem_wanted maxCardinalitySMTI_npComplete :
    maxCardinalitySMTIDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxCardinalitySMTIDec

end MetaMathlibExt.Complexity.NPComplete.MaxCardinalitySMTI
