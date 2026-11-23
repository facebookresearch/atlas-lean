/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED SATISFIABILITY, FIXED NON-SCHAEFER RELATIONS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO6] GENERALIZED
SATISFIABILITY (comment: for any fixed sequence `S` the problem is NP-complete
unless one of six alternatives holds);
T. J. Schaefer, "The complexity of satisfiability problems", Proceedings of the
Tenth Annual ACM Symposium on Theory of Computing (STOC 1978), 216-226,
doi:10.1145/800133.804350.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Logics.Propositional.CNF.Semantics
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import WantedExt.Complexity.NPComplete.GeneralizedSatisfiabilityWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiabilityFixed

open Cslib.Logic.PL Matrix

/-!
# GENERALIZED SATISFIABILITY, FIXED NON-SCHAEFER RELATIONS is NP-complete

GENERALIZED SATISFIABILITY
(`MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiability`) with the sequence
`S = ⟨R₁, ..., Rₘ⟩` of relations `Rᵢ ⊆ {T, F}^{kᵢ}` fixed. INSTANCE: a set `U` of variables
and, for `1 ≤ i ≤ m`, a collection `Cᵢ` of `kᵢ`-tuples of variables from `U`. QUESTION: is
there a truth assignment `t : U → {T, F}` such that for all `i` and all
`(u[1], ..., u[kᵢ]) ∈ Cᵢ`, `(t(u[1]), ..., t(u[kᵢ])) ∈ Rᵢ`?

Schaefer's dichotomy, as recorded by Garey and Johnson: for any fixed sequence `S`, the
problem is NP-complete unless one of the following six alternatives holds, in which case it
is solvable in polynomial time: (1) each `Rᵢ` contains `{T}^{kᵢ}`, (2) each `Rᵢ` contains
`{F}^{kᵢ}`, (3) each `Rᵢ` is logically "equivalent" to some conjunctive normal form expression
having at most one negated literal per clause, (4) each `Rᵢ` is logically "equivalent" to
some conjunctive normal form expression having at most one un-negated literal per clause,
(5) each `Rᵢ` is logically "equivalent" to some conjunctive normal form expression having at
most 2 literals per clause, or (6) each `Rᵢ` is the "solution set" for some system of linear
equations over `GF[2]`. This module states the NP-complete half: for every fixed `S` for
which none of (1)-(6) holds, the problem is NP-complete.

A relation is given as in GENERALIZED SATISFIABILITY, by its arity `k` and the list of its
tuples (`true` for `T`). Its coordinates are the variables `0, ..., k - 1`: a CNF expression
(CSLib's `Cslib.Logic.PL.CNF`, literals `(variable, polarity)`, polarity `false` for a negated
literal) or a linear system is equivalent to the relation when it uses only these variables
and its models are exactly the tuples of the relation. The instance carries the number `n` of
variables and the collections `C₁, ..., Cₘ`; it is turned into a GENERALIZED SATISFIABILITY
instance by pairing `Cᵢ` with `Rᵢ`, and the well-formedness and question of that module are
reused unchanged.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A relation `R ⊆ {T, F}^k`: its arity `k` and the list of its tuples. -/
abbrev Relation := ℕ × List (List Bool)

/-- The relations are well formed: every arity is positive and every tuple of a relation has
its arity as length. -/
def RelationsWellFormed (S : List Relation) : Prop :=
  ∀ r ∈ S, 0 < r.1 ∧ ∀ u ∈ r.2, u.length = r.1

/-- The tuple `(t(0), ..., t(k - 1))` of values of the coordinates of `r` belongs to `r`. -/
def Holds (r : Relation) (t : ℕ → Bool) : Prop :=
  (List.range r.1).map t ∈ r.2

/-- `φ` is a CNF expression over the coordinates `0, ..., k - 1` of `r` that is logically
equivalent to `r`. -/
def IsEquivalentCNF (r : Relation) (φ : CNF) : Prop :=
  (∀ C ∈ φ, ∀ l ∈ C, l.1 < r.1) ∧ ∀ t : ℕ → Bool, Holds r t ↔ φ.Satisfies t

/-- `r` is the solution set of a system `A x = b` of linear equations over `GF[2]` in the
coordinates of `r`. -/
def IsAffine (r : Relation) : Prop :=
  ∃ (m : ℕ) (A : Matrix (Fin m) (Fin r.1) (ZMod 2)) (b : Fin m → ZMod 2),
    ∀ t : ℕ → Bool, Holds r t ↔ A *ᵥ (fun j => if t j then 1 else 0) = b

/-- One of Schaefer's six alternatives holds for `S`. -/
def SchaeferCondition (S : List Relation) : Prop :=
  (∀ r ∈ S, List.replicate r.1 true ∈ r.2) ∨
    (∀ r ∈ S, List.replicate r.1 false ∈ r.2) ∨
    (∀ r ∈ S, ∃ φ, IsEquivalentCNF r φ ∧ ∀ C ∈ φ, C.countP (fun l => !l.2) ≤ 1) ∨
    (∀ r ∈ S, ∃ φ, IsEquivalentCNF r φ ∧ ∀ C ∈ φ, C.countP (fun l => l.2) ≤ 1) ∨
    (∀ r ∈ S, ∃ φ, IsEquivalentCNF r φ ∧ ∀ C ∈ φ, C.length ≤ 2) ∨
    ∀ r ∈ S, IsAffine r

/-- An instance for the fixed sequence `S`: the number `n` of variables (variables
`0, ..., n - 1`) and the collections `C₁, ..., Cₘ`, each a list of tuples of variables. -/
abbrev GeneralizedSatisfiabilityFixedInstance := ℕ × List (List (List ℕ))

/-- The GENERALIZED SATISFIABILITY instance obtained by pairing each `Cᵢ` with `Rᵢ`. -/
def toInstance (S : List Relation) (j : GeneralizedSatisfiabilityFixedInstance) :
    GeneralizedSatisfiability.GeneralizedSatisfiabilityInstance :=
  (j.1, List.zipWith (fun r C => (r.1, r.2, C)) S j.2)

/-- Well-formedness of an instance: there is one collection per relation of `S`, and the
paired GENERALIZED SATISFIABILITY instance is well formed. -/
def WellFormed (S : List Relation) (j : GeneralizedSatisfiabilityFixedInstance) : Prop :=
  j.2.length = S.length ∧ GeneralizedSatisfiability.WellFormed (toInstance S j)

open Classical in
/-- GENERALIZED SATISFIABILITY with the relation sequence fixed to `S`, as a decision problem
over bitstrings. -/
noncomputable def generalizedSatisfiabilityFixedDec (S : List Relation) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeneralizedSatisfiabilityFixedInstance) x with
  | some j => decide (WellFormed S j ∧
      GeneralizedSatisfiability.GeneralizedSatisfiabilityFeasible (toInstance S j))
  | none => false

/-- **GENERALIZED SATISFIABILITY, FIXED NON-SCHAEFER RELATIONS is NP-complete.** For every
fixed well-formed sequence `S` of relations satisfying none of Schaefer's six alternatives,
GENERALIZED SATISFIABILITY over `S` is NP-complete. Source: Garey and Johnson (1979), [LO6];
Schaefer (1978). -/
public theorem_wanted generalizedSatisfiabilityFixed_npComplete (S : List Relation)
    (_hS : RelationsWellFormed S) (_hSchaefer : ¬ SchaeferCondition S) :
    generalizedSatisfiabilityFixedDec S ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (generalizedSatisfiabilityFixedDec S)

end MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiabilityFixed
