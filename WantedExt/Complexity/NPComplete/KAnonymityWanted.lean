/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# k-ANONYMITY (entry suppression) is NP-complete

Source:
A. Meyerson and R. Williams, "On the complexity of optimal k-anonymity", Proceedings of the
23rd ACM SIGMOD-SIGACT-SIGART Symposium on Principles of Database Systems (PODS 2004),
223-228, doi:10.1145/1055558.1055591, Definition 2.1 and Theorem 3.1 (NP-hard for every
`k ≥ 3` when the alphabet is not bounded).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KAnonymity

/-!
# k-ANONYMITY (entry suppression) is NP-complete

INSTANCE: a set `V = {v₁, …, vₙ} ⊆ Σᵐ` of vectors (the rows of a table with `m` attributes over
an alphabet `Σ`), and natural numbers `k` and `l`. QUESTION: is there a suppressor `t` on `V`,
that is, a map `t : V → (Σ ∪ {*})ᵐ` with `t(v)[a] ∈ {v[a], *}` for every `v ∈ V` and every
coordinate `a`, such that `t(V)` is `k`-anonymous (for every `v ∈ V` there are `k - 1` other
vectors `w ∈ V` with `t(w) = t(v)`) and the total number of coordinates suppressed by `t` is at
most `l`?

The alphabet is `ℕ`; the rows are a duplicate-free list of length-`m` lists, matching
Meyerson and Williams's set `V`. A suppressor is given by the positions it suppresses,
`sup : row → coordinate → Bool`; the suppressed row `t(v)` has `none` (the symbol `*`) at the
suppressed coordinates and `some (v[a])` elsewhere. "There are `k - 1` other vectors with the
same image" is stated as "at least `k` rows, the row itself included, have the same image".

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `m` of attributes, the rows (each a list of `m` alphabet symbols),
the anonymity parameter `k`, and the suppression budget `l`. -/
abbrev KAnonymityInstance := ℕ × List (List ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: the rows are pairwise distinct and each has length `m`. -/
def WellFormed (i : KAnonymityInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ row ∈ i.2.1, row.length = i.1

/-- The image `t(v)` of row `v` under the suppressor that suppresses the positions `sup`:
`none` (the symbol `*`) at a suppressed coordinate, the row's own symbol elsewhere. -/
def suppressed (i : KAnonymityInstance) (sup : Fin i.2.1.length → Fin i.1 → Bool)
    (v : Fin i.2.1.length) (a : Fin i.1) : Option ℕ :=
  if sup v a then none else some ((i.2.1.get v).getD a 0)

/-- Some suppressor suppresses at most `l` coordinates in total and makes every row agree with
at least `k` rows, itself included, after suppression. -/
def KAnonymityFeasible (i : KAnonymityInstance) : Prop :=
  ∃ sup : Fin i.2.1.length → Fin i.1 → Bool,
    (Finset.univ.filter fun p : Fin i.2.1.length × Fin i.1 => sup p.1 p.2 = true).card ≤
        i.2.2.2 ∧
      ∀ v, i.2.2.1 ≤
        (Finset.univ.filter fun w => suppressed i sup w = suppressed i sup v).card

open Classical in
/-- k-ANONYMITY (entry suppression) as a decision problem over bitstrings. -/
noncomputable def kAnonymityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KAnonymityInstance) x with
  | some i => decide (WellFormed i ∧ KAnonymityFeasible i)
  | none => false

/-- **k-ANONYMITY with entry suppression is NP-complete.** Source: Meyerson and Williams
(2004), Theorem 3.1. -/
public theorem_wanted kAnonymity_npComplete :
    kAnonymityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kAnonymityDec

end MetaMathlibExt.Complexity.NPComplete.KAnonymity
