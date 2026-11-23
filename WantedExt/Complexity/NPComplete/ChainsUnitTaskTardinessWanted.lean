/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE TOTAL TARDINESS with chains and unit processing times is NP-complete

Source:
J. Y.-T. Leung and G. H. Young, "Minimizing total tardiness on a single machine with
precedence constraints", ORSA Journal on Computing 2 (1990), 346-352,
doi:10.1287/ijoc.2.4.346 (`1|chains, pⱼ = 1|∑ Tⱼ`);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity results for scheduling chains on a single
machine", European Journal of Operational Research 4 (1980), 270-275,
doi:10.1016/0377-2217(80)90111-3 (the scheduling model and the chain-like precedence relation);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (single machine problems:
`1|chains; pᵢ = 1|∑ Tᵢ`, minimal NP-hard in the strong sense, Leung and Young (1990)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PrecedenceUnitTaskTardinessWanted
public import WantedExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsUnitTaskTardiness

open PrecedenceUnitTaskTardiness (PrecedenceUnitTaskTardinessInstance Prec
  PrecedenceUnitTaskTardinessFeasible)
open SequencingToMinimizeWeightedTardiness (Task)

/-!
# SINGLE-MACHINE TOTAL TARDINESS with chains and unit processing times is NP-complete

INSTANCE: jobs `J₁, …, Jₙ` to be processed on a single machine that executes at most one job at
a time, each requiring one unit of processing time (`pⱼ = 1`) and having a due date `dⱼ`; a
precedence relation `→` on the jobs that is chain-like (each job has at most one immediate
predecessor and at most one immediate successor); and a bound `K`. QUESTION: is there a schedule
respecting the precedence relation (`Jⱼ → Jₖ` requires `Jⱼ` to be completed before `Jₖ` can
start) whose total tardiness `∑ⱼ Tⱼ`, with `Tⱼ = max{0, Cⱼ - dⱼ}` for the completion time `Cⱼ`,
is at most `K`?

This is `1|chains, pⱼ = 1|∑ Tⱼ` (Leung and Young 1990), the restriction of
`1|prec, pⱼ = 1|∑ Tⱼ` (`WantedExt.Complexity.NPComplete.PrecedenceUnitTaskTardinessWanted`) to
chain-like precedence relations. The instance type, the precedence relation `Prec` (the listed
pairs `(t, t')` with `t → t'`), that module's well-formedness condition (unit lengths and unit
weights, positive due dates and positive `K` as in Garey and Johnson's [SS5], listed pairs that
name jobs and form a strict partial order) and its question (a one-processor schedule obeying the
precedence constraints with weighted tardiness at most `K`; with unit weights this is the total
tardiness) are reused unchanged. The chain condition is added to `WellFormed`, in Lenstra and
Rinnooy Kan's words: `t` is an immediate predecessor of `t'` (and `t'` an immediate successor of
`t`) when `t → t'` and no job `c` has `t → c → t'`; each job has at most one immediate
predecessor and at most one immediate successor. Binary encoding of all numbers.

Leung and Young prove NP-hardness. Membership in NP holds because a schedule is a certificate of
polynomial size: removing idle time keeps the job order and never increases a completion time,
so a schedule with total tardiness at most `K` can be taken with all start times below `n`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `t` is an immediate predecessor of `t'` (and `t'` an immediate successor of `t`): `t → t'`,
and no job `c` has `t → c → t'`. -/
def ImmediatePredecessor (i : PrecedenceUnitTaskTardinessInstance) (t t' : Task i.1) : Prop :=
  Prec i t t' ∧ ∀ c, ¬ (Prec i t c ∧ Prec i c t')

/-- The precedence relation is chain-like: no job has more than one immediate predecessor, and
no job has more than one immediate successor. -/
def IsChainLike (i : PrecedenceUnitTaskTardinessInstance) : Prop :=
  (∀ t' a b, ImmediatePredecessor i a t' → ImmediatePredecessor i b t' → a = b) ∧
    ∀ t a b, ImmediatePredecessor i t a → ImmediatePredecessor i t b → a = b

/-- Well-formedness of an instance: it is a well-formed instance of `1|prec, pⱼ = 1|∑ Tⱼ`
(unit lengths and weights, positive due dates and `K`, listed pairs naming jobs and forming a
strict partial order), and the precedence relation is chain-like. -/
def WellFormed (i : PrecedenceUnitTaskTardinessInstance) : Prop :=
  PrecedenceUnitTaskTardiness.WellFormed i ∧ IsChainLike i

open Classical in
/-- SINGLE-MACHINE TOTAL TARDINESS with chains and unit processing times as a decision problem
over bitstrings. -/
noncomputable def chainsUnitTaskTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceUnitTaskTardinessInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceUnitTaskTardinessFeasible i)
  | none => false

/-- **SINGLE-MACHINE TOTAL TARDINESS with chains and unit processing times is NP-complete.**
Source: Leung and Young (1990) (NP-hardness); Lenstra and Rinnooy Kan (1980). -/
public theorem_wanted chainsUnitTaskTardiness_npComplete :
    chainsUnitTaskTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chainsUnitTaskTardinessDec

end MetaMathlibExt.Complexity.NPComplete.ChainsUnitTaskTardiness
