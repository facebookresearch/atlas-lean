/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTI-ITEM CAPACITATED LOT SIZING WITH SETUP TIMES: FEASIBILITY is NP-complete

Source:
W. W. Trigeiro, L. J. Thomas and J. O. McClain, "Capacitated lot sizing with setup times",
Management Science 35 (1989), 353-366, doi:10.1287/mnsc.35.3.353, p. 359;
I. Fragkos, Z. Degraeve and B. De Reyck, "A horizon decomposition approach for the
capacitated lot-sizing problem with setup times", INFORMS Journal on Computing 28 (2016),
465-482, doi:10.1287/ijoc.2016.0691, Sections 3 and 6.5.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedLotSizingSetupTimes

/-!
# MULTI-ITEM CAPACITATED LOT SIZING WITH SETUP TIMES: FEASIBILITY is NP-complete

INSTANCE: `T` periods and `N` items; for item `i` a processing time `a_i` per unit, a setup
time `s_i` and demands `d_{it}`; a single resource with capacity `C_t` in period `t`.
QUESTION: is there a production plan without backlogging, i.e. production quantities
`x_{it} ≥ 0` whose cumulative production `∑_{u ≤ t} x_{iu}` covers the cumulative demand
`∑_{u ≤ t} d_{iu}` of every item `i` in every period `t` (starting from zero inventory), such
that in every period the processing time `∑_i a_i x_{it}` plus the setup times `s_i` of the
items with `x_{it} > 0` is at most `C_t`?

This is the feasibility problem of the capacitated lot-sizing problem with setup times
(CLST), in the formulation recorded by Fragkos, Degraeve and De Reyck (Section 3):
production quantities are nonnegative reals and a setup indicator `y_{it} ∈ {0, 1}` must be
`1` whenever `x_{it} > 0`. Trigeiro, Thomas and McClain call this feasibility test NP-complete
(p. 359, quoted by Fragkos, Degraeve and De Reyck, Section 6.5.1). The restriction to setup
and processing times that depend only on the item keeps it NP-hard: BIN PACKING with `N`
pieces and `0 < K < N` bins reduces to it with one period per bin, of capacity the bin size,
and one item per piece, with setup time the piece size, processing time `0` and demand `1` in
the last period (the output has `O(N²)` numbers); a BIN PACKING instance with `K = 0` (a
yes-instance iff `N = 0`) or `K ≥ N` (one piece per bin, a yes-instance iff every piece fits a
bin) is decided directly and mapped to a fixed yes- or no-instance. Membership in NP: given
the setup indicators, the remaining constraints are a linear program. Data are natural
numbers in the canonical binary encoding; items and periods are numbered from `0` below.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MULTI-ITEM CAPACITATED LOT SIZING WITH SETUP TIMES: FEASIBILITY is NP-complete.**
Source: Trigeiro, Thomas and McClain (1989); Fragkos, Degraeve and De Reyck (2016). -/
public theorem_wanted capacitatedLotSizingSetupTimes_npComplete :
    capacitatedLotSizingSetupTimesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L capacitatedLotSizingSetupTimesDec

end MetaMathlibExt.Complexity.NPComplete.CapacitatedLotSizingSetupTimes
