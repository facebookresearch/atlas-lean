/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNWEIGHTED COALITIONAL MANIPULATION under Borda with two manipulators is NP-complete

Source:
N. Betzler, R. Niedermeier and G. J. Woeginger, "Unweighted coalitional manipulation under the
Borda rule is NP-hard", Proceedings of the 22nd International Joint Conference on Artificial
Intelligence (IJCAI 2011), 55-60, doi:10.5591/978-1-57735-516-8/IJCAI11-021 (Section 2,
definition of BORDA MANIPULATION; Theorem 3.1);
J. Davies, G. Katsirelos, N. Narodytska and T. Walsh, "Complexity of and algorithms for Borda
manipulation", Proceedings of the 25th AAAI Conference on Artificial Intelligence (AAAI 2011),
657-662, doi:10.1609/aaai.v25i1.7873.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.CoalitionalManipulationBordaWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BordaManipulationTwoManipulators

/-!
# UNWEIGHTED COALITIONAL MANIPULATION under Borda with two manipulators is NP-complete

INSTANCE: an election `(V, C)`, consisting of a set `C` of candidates and a multiset `V` of
(nonmanipulative) votes, each a linear order on `C`, and a distinguished candidate `c ∈ C`.
QUESTION: is there a multiset `W` (the coalition) of `t = 2` votes over `C` such that `c` is a
Borda winner of `(V ∪ W, C)`?

Under the Borda rule with `m = |C|` candidates, the candidate at position `i` (`1 ≤ i ≤ m`) of a
vote receives `m - i` points from it, and each candidate with the highest total score is a
Borda winner (co-winner model, as in Betzler, Niedermeier and Woeginger). Votes are unweighted.

The candidates are `0, …, m - 1`, and a vote is a list of them in order of preference (a
permutation of `[0, …, m - 1]`, most preferred first). Scores reuse the positional-scoring
`points` and `score` of `WantedExt.Complexity.NPComplete.CoalitionalManipulationBordaWanted`,
with the Borda vector `(m - 1, m - 2, …, 0)` and every vote of weight `1`.

Betzler, Niedermeier and Woeginger prove NP-completeness already for three nonmanipulative
votes and two manipulators (Theorem 3.1); Davies, Katsirelos, Narodytska and Walsh prove
NP-hardness for two manipulators independently. Here the number of nonmanipulative votes is
arbitrary and the number of manipulators is fixed to two.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationBorda (score)

/-- An instance: the number `m` of candidates, the nonmanipulative votes `V` (each a ranking of
`0, …, m - 1`, most preferred first), and the distinguished candidate `c`. -/
abbrev BordaManipulationInstance := ℕ × List (List ℕ) × ℕ

/-- `v` is a vote over the candidates `0, …, m - 1`: it ranks each of them exactly once. -/
def IsVote (m : ℕ) (v : List ℕ) : Prop := v.Perm (List.range m)

/-- The Borda scoring vector for `m` candidates, `(m - 1, m - 2, …, 0)`: the candidate at
position `i` (counting from `1`) receives `m - i` points. -/
def bordaVector (m : ℕ) : List ℕ := (List.range m).reverse

/-- The Borda score `s(V, d)` of candidate `d` under the unweighted votes `V` with `m`
candidates. -/
def bordaScore (m : ℕ) (V : List (List ℕ)) (d : ℕ) : ℕ :=
  score (bordaVector m) (V.map fun v => (v, 1)) d

/-- Well-formedness of an instance: every nonmanipulative vote ranks the `m` candidates, and
`c` is a candidate. -/
def WellFormed (i : BordaManipulationInstance) : Prop :=
  (∀ v ∈ i.2.1, IsVote i.1 v) ∧ i.2.2 < i.1

/-- Two manipulative votes `w₁, w₂` over the candidates make `c` a Borda winner of the election
with votes `V ∪ {w₁, w₂}`: no candidate scores more than `c`. -/
def BordaManipulationFeasible (i : BordaManipulationInstance) : Prop :=
  ∃ w₁ w₂ : List ℕ, IsVote i.1 w₁ ∧ IsVote i.1 w₂ ∧
    ∀ d < i.1, bordaScore i.1 (i.2.1 ++ [w₁, w₂]) d ≤ bordaScore i.1 (i.2.1 ++ [w₁, w₂]) i.2.2

open Classical in
/-- UNWEIGHTED COALITIONAL MANIPULATION under Borda with two manipulators as a decision problem
over bitstrings. -/
noncomputable def bordaManipulationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BordaManipulationInstance) x with
  | some i => decide (WellFormed i ∧ BordaManipulationFeasible i)
  | none => false

/-- **UNWEIGHTED COALITIONAL MANIPULATION under Borda with two manipulators is NP-complete.**
Source: Betzler, Niedermeier and Woeginger (2011), Theorem 3.1; Davies, Katsirelos, Narodytska
and Walsh (2011). -/
public theorem_wanted bordaManipulation_npComplete :
    bordaManipulationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bordaManipulationDec

end MetaMathlibExt.Complexity.NPComplete.BordaManipulationTwoManipulators
