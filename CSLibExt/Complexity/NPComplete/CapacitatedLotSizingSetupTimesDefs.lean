/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTI-ITEM CAPACITATED LOT SIZING WITH SETUP TIMES: FEASIBILITY: definitions

Source:
W. W. Trigeiro, L. J. Thomas and J. O. McClain, "Capacitated lot sizing with setup times",
Management Science 35 (1989), 353-366, doi:10.1287/mnsc.35.3.353, p. 359;
I. Fragkos, Z. Degraeve and B. De Reyck, "A horizon decomposition approach for the
capacitated lot-sizing problem with setup times", INFORMS Journal on Computing 28 (2016),
465-482, doi:10.1287/ijoc.2016.0691, Sections 3 and 6.5.1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedLotSizingSetupTimes

/-- An instance: the number `T` of periods, the items as triples
`(a_i, s_i, [d_{i0}, …, d_{i(T-1)}])` of unit processing time, setup time and demands, and
the capacities `[C_0, …, C_{T-1}]`. -/
abbrev CapacitatedLotSizingSetupTimesInstance := ℕ × List (ℕ × ℕ × List ℕ) × List ℕ

/-- Well-formedness of an instance: there are `T` capacities and every item has `T`
demands. -/
def WellFormed (i : CapacitatedLotSizingSetupTimesInstance) : Prop :=
  i.2.2.length = i.1 ∧ ∀ it ∈ i.2.1, it.2.2.length = i.1

/-- There are production quantities `x j t ≥ 0` and setup indicators `y j t`, with
`y j t = true` whenever `x j t > 0`, such that cumulative production covers cumulative
demand and every period's processing and setup times fit its capacity. -/
def CapacitatedLotSizingSetupTimesFeasible (i : CapacitatedLotSizingSetupTimesInstance) :
    Prop :=
  ∃ (x : Fin i.2.1.length → Fin i.1 → ℝ) (y : Fin i.2.1.length → Fin i.1 → Bool),
    (∀ j t, 0 ≤ x j t) ∧ (∀ j t, 0 < x j t → y j t = true) ∧
    (∀ j t, ∑ u ∈ Finset.univ.filter (· ≤ t), (((i.2.1.get j).2.2.getD u.val 0 : ℕ) : ℝ) ≤
      ∑ u ∈ Finset.univ.filter (· ≤ t), x j u) ∧
    ∀ t, ∑ j, (((i.2.1.get j).1 : ℝ) * x j t +
      if y j t then ((i.2.1.get j).2.1 : ℝ) else 0) ≤ ((i.2.2.getD t.val 0 : ℕ) : ℝ)

open Classical in
/-- MULTI-ITEM CAPACITATED LOT SIZING WITH SETUP TIMES: FEASIBILITY as a decision problem over
bitstrings. -/
noncomputable def capacitatedLotSizingSetupTimesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CapacitatedLotSizingSetupTimesInstance) x with
  | some i => decide (WellFormed i ∧ CapacitatedLotSizingSetupTimesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CapacitatedLotSizingSetupTimes
