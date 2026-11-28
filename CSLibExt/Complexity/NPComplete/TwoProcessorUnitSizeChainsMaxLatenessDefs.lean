/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR-TASK SCHEDULING `P2|chains;p_i=1;size_i|L_max`: definitions

Source:
P. Brucker, S. Knust, D. Roper and Y. Zinder, "Scheduling UET task systems with concurrency
on two parallel identical processors", Mathematical Methods of Operations Research 52 (2000),
369-387, doi:10.1007/s001860000089;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Multiprocessor task problems with parallel processors" (`P2|chains;p_i=1;size_i|L_max`,
minimal NP-hard in the strong sense, citing Brucker et al. 2000; the class page defines the
model: each task `i` requires `size_i` of the `m` identical processors during its processing).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.F3UnitChainsLateJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitSizeChainsMaxLateness

open MetaMathlibExt.Complexity.NPComplete.F3UnitChainsLateJobs (ChainsWellFormed)

/-- An instance `(T, A, K)`: the tasks `0, …, n - 1` (task `i` listed as its size `size_i` and
its due date `d_i` as a `(positive part, negative part)` pair), the chain arcs `(i, j)` (task `i`
immediately precedes task `j`), and the bound `K` as a `(positive part, negative part)` pair. -/
abbrev TwoProcessorUnitSizeChainsMaxLatenessInstance :=
  List (ℕ × (ℕ × ℕ)) × List (ℕ × ℕ) × (ℕ × ℕ)

/-- The integer `a - b` represented by the pair `(a, b)`. -/
def intOf (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)

/-- Well-formedness of an instance: there is at least one task, every size is `1` or `2`, and
the arcs form chains on the tasks. -/
def WellFormed (i : TwoProcessorUnitSizeChainsMaxLatenessInstance) : Prop :=
  i.1 ≠ [] ∧ (∀ x ∈ i.1, x.1 = 1 ∨ x.1 = 2) ∧ ChainsWellFormed i.1.length i.2.1

/-- Some schedule `S` (start times of the unit tasks) uses at most the `2` processors in every
time slot (the sizes of the tasks starting at `u` sum to at most `2`), obeys the chain arcs, and
has maximum lateness at most `K`: `(S j + 1) - d_j ≤ K` for every task `j`. -/
def TwoProcessorUnitSizeChainsMaxLatenessFeasible
    (i : TwoProcessorUnitSizeChainsMaxLatenessInstance) : Prop :=
  ∃ S : Fin i.1.length → ℕ,
    (∀ u, (∑ j ∈ Finset.univ.filter fun j => S j = u, (i.1.get j).1) ≤ 2) ∧
    (∀ j k : Fin i.1.length, ((j : ℕ), (k : ℕ)) ∈ i.2.1 → S j + 1 ≤ S k) ∧
    ∀ j, ((S j + 1 : ℕ) : ℤ) - intOf (i.1.get j).2 ≤ intOf i.2.2

open Classical in
/-- `P2|chains;p_i=1;size_i|L_max` as a decision problem over bitstrings. -/
noncomputable def twoProcessorUnitSizeChainsMaxLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitSizeChainsMaxLatenessInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorUnitSizeChainsMaxLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitSizeChainsMaxLateness
