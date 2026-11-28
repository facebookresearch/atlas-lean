/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SEQUENCING WITH DELAYS: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM PRECEDENCE CONSTRAINED SEQUENCING WITH DELAYS (decision version);
D. Bernstein, M. Rodeh and I. Gertner, "Approximation algorithms for scheduling arithmetic
expressions on pipelined machines", J. Algorithms 10 (1989), 120-139,
doi:10.1016/0196-6774(89)90027-8 (the problem);
J. Y.-T. Leung, O. Vornberger and J. D. Witthoff, "On some variants of the bandwidth
minimization problem", SIAM J. Comput. 13 (1984), 650-667, doi:10.1137/0213040 (the case of
equal delays, `1|prec(l); pᵢ = 1|C_max`, recorded as strongly NP-hard by P. Brucker and
S. Knust, *Complexity results for scheduling problems*, class "Single machine problems with
non-negative time-lags").
-/
module

public import Mathlib.Logic.Relation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSequencingWithDelays

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-- An instance: the delays `[d(t₀), …, d(t_{n-1})]` of the tasks, the edges `(i, j)` of the
precedence graph, the bound `D` and the bound `K`. -/
abbrev PrecedenceConstrainedSequencingWithDelaysInstance := List ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- The tasks of the instance, `Fin n` for `n` listed delays. -/
abbrev Task (i : PrecedenceConstrainedSequencingWithDelaysInstance) : Type := Fin i.1.length

/-- The edge relation of the precedence graph: `t → t'` when the pair `(t, t')` is listed. -/
def Edge (i : PrecedenceConstrainedSequencingWithDelaysInstance) (t t' : Task i) : Prop :=
  ((t : ℕ), (t' : ℕ)) ∈ i.2.1

/-- The delay `d(t)` of task `t`. -/
def delay (i : PrecedenceConstrainedSequencingWithDelaysInstance) (t : Task i) : ℕ :=
  i.1.get t

/-- Well-formedness of an instance: every listed edge joins two tasks, the edge relation is
acyclic, `D` is positive, every delay is at most `D`, and `K` is positive. -/
def WellFormed (i : PrecedenceConstrainedSequencingWithDelaysInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1 < i.1.length ∧ e.2 < i.1.length) ∧
    (∀ t : Task i, ¬ Relation.TransGen (Edge i) t t) ∧
    0 < i.2.2.1 ∧ (∀ d ∈ i.1, d ≤ i.2.2.1) ∧ 0 < i.2.2.2

/-- Some one-processor schedule of the unit-time tasks (start times `S(t) = σ(t) + 1`) obeys
every delay (`t → t'` implies `σ(t) + d(t) < σ(t')`) and has finish time at most `K`. -/
def PrecedenceConstrainedSequencingWithDelaysFeasible
    (i : PrecedenceConstrainedSequencingWithDelaysInstance) : Prop :=
  ∃ σ : Task i → ℕ, IsOneProcessorSchedule (fun _ => 1) σ ∧
    (∀ t t', Edge i t t' → σ t + delay i t < σ t') ∧ ∀ t, σ t + 1 ≤ i.2.2.2

open Classical in
/-- PRECEDENCE CONSTRAINED SEQUENCING WITH DELAYS as a decision problem over bitstrings. -/
noncomputable def precedenceConstrainedSequencingWithDelaysDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceConstrainedSequencingWithDelaysInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceConstrainedSequencingWithDelaysFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSequencingWithDelays
