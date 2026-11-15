/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EQUIVALENCE DELETION is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MINIMUM EQUIVALENCE DELETION;
N. Garg, V. V. Vazirani and M. Yannakakis, "Approximate max-flow min-(multi)cut theorems and
their applications", SIAM J. Comput. 25 (1996), 235-251, doi:10.1137/S0097539793243016 (the
problem as 2CNF≡ clause deletion);
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoret. Comput. Sci. 1 (1976), 237-267, doi:10.1016/0304-3975(76)90059-1 (SIMPLE MAX CUT,
Garey and Johnson (1979), [ND16]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Logics.Propositional.CNF.Semantics
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EquivalenceDeletion

/-!
# EQUIVALENCE DELETION is NP-complete

INSTANCE: a set `U` of variables, a collection `C` of equivalences, i.e., pairs of literals over
`U`, and a positive integer `K`.
QUESTION: is there a truth assignment for `U` such that at most `K` equivalences of `C` are not
satisfied?

This is the decision version of MINIMUM EQUIVALENCE DELETION (an entry of the Crescenzi-Kann
compendium); the bound is a positive integer, following the Garey-Johnson convention for decision
versions. An equivalence `l₁ ≡ l₂` is satisfied when both literals get the same truth value.
NP-hardness, from SIMPLE MAX CUT ([ND16], Garey, Johnson and Stockmeyer): for a graph and a cut
bound `J ≤ |E|`, take the equivalences `x ≡ ¬y`, one for each edge `{x, y}`, and `z ≡ ¬z` for a
fresh variable `z`, which no assignment satisfies. An assignment satisfies exactly the
equivalences of the edges cut by its true variables, so at most `|E| - J + 1` (a positive bound)
equivalences are unsatisfied exactly when some cut has at least `J` edges.

Variables are `0, …, n - 1`. A literal is a pair `(x, b)` of a variable and a polarity, as in
`CSLibExt.Logics.Propositional.CNF` (`b = true` is `x`, `b = false` is `¬x`), and is true under
an assignment exactly when `Cslib.Logic.PL.CNFLiteral.Satisfies` holds. `C` is a list (repeated
equivalences count separately). At most `K` equivalences are unsatisfied exactly when some
sublist of `C` that omits at most `K` of its entries consists of satisfied equivalences.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of variables, the equivalences (pairs of literals) and the
bound `K`. -/
abbrev EquivalenceDeletionInstance := ℕ × List ((ℕ × Bool) × (ℕ × Bool)) × ℕ

/-- Well-formedness of an instance: every literal is over a variable below `n`, and `0 < K`. -/
def WellFormed (i : EquivalenceDeletionInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1.1 < i.1 ∧ e.2.1 < i.1) ∧ 0 < i.2.2

/-- The equivalence `l₁ ≡ l₂` is satisfied: both literals have the same truth value. -/
def EquivSatisfied (assignment : ℕ → Bool) (e : (ℕ × Bool) × (ℕ × Bool)) : Prop :=
  (Cslib.Logic.PL.CNFLiteral.Satisfies assignment e.1 ↔
    Cslib.Logic.PL.CNFLiteral.Satisfies assignment e.2)

/-- Some truth assignment leaves at most `K` equivalences unsatisfied. -/
def EquivalenceDeletionFeasible (i : EquivalenceDeletionInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    ∃ kept : List ((ℕ × Bool) × (ℕ × Bool)), kept.Sublist i.2.1 ∧
      i.2.1.length ≤ kept.length + i.2.2 ∧
        ∀ e ∈ kept, EquivSatisfied (fun x => assign.getD x false) e

open Classical in
/-- EQUIVALENCE DELETION as a decision problem over bitstrings. -/
noncomputable def equivalenceDeletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EquivalenceDeletionInstance) x with
  | some i => decide (WellFormed i ∧ EquivalenceDeletionFeasible i)
  | none => false

/-- **EQUIVALENCE DELETION is NP-complete.** Source: Crescenzi and Kann, MINIMUM EQUIVALENCE
DELETION; Garg, Vazirani and Yannakakis (1996); Garey, Johnson and Stockmeyer (1976). -/
public theorem_wanted equivalenceDeletion_npComplete :
    equivalenceDeletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L equivalenceDeletionDec

end MetaMathlibExt.Complexity.NPComplete.EquivalenceDeletion
