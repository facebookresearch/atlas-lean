/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM n-TIMES COVERAGE is NP-complete

Source:
G. Liu, A. Dimitrakakis, B. Carter and D. Gifford, "Maximum n-times coverage for vaccine design",
*International Conference on Learning Representations (ICLR)* (2022).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxNTimesCoverage

/-!
# MAXIMUM n-TIMES COVERAGE is NP-complete

An instance is `(n, rows, weights, k, τ)`: each row lists, for one overlay, how many times it
covers each element; `weights` are the element weights. The question is whether at most `k`
overlays cover elements of total weight at least `τ` at least `n` times each (the decision
version of the problem of Liu et al.; the objective is `nCoverage` in
`CSLibExt/Algorithms/Lean/Approximation/MaxNTimesCoverage.lean`). For `n = 1` and unit
multiplicities this contains maximum coverage, hence SET COVER.

Encoding and the NP-completeness format follow
`WantedExt/Complexity/NPComplete/SetCoverWanted.lean`.
-/

/-- An instance: `n`, the coverage rows of the overlays, element weights, `k`, `τ`. -/
abbrev Instance := ℕ × List (List ℕ) × List ℕ × ℕ × ℕ

/-- Well-formedness: every row has one entry per element. -/
def WellFormed (i : Instance) : Prop :=
  ∀ row ∈ i.2.1, row.length = i.2.2.1.length

/-- The weight of the elements covered at least `n` times by the rows `sub`. -/
def coveredWeight (n : ℕ) (sub : List (List ℕ)) (weights : List ℕ) : ℕ :=
  ((List.range weights.length).filter fun e => n ≤ (sub.map fun row => row.getD e 0).sum).foldr
    (fun e acc => weights.getD e 0 + acc) 0

/-- At most `k` overlays cover weight at least `τ` at least `n` times. -/
def Feasible (i : Instance) : Prop :=
  ∃ sub : List (List ℕ), sub.Sublist i.2.1 ∧ sub.length ≤ i.2.2.2.1 ∧
    i.2.2.2.2 ≤ coveredWeight i.1 sub i.2.2.1

open Classical in
/-- MAXIMUM n-TIMES COVERAGE as a decision problem over bitstrings. -/
noncomputable def maxNTimesCoverageDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := Instance) x with
  | some i => decide (WellFormed i ∧ Feasible i)
  | none => false

/-- **MAXIMUM n-TIMES COVERAGE is NP-complete** (Liu, Dimitrakakis, Carter and Gifford 2022). -/
public theorem_wanted maxNTimesCoverage_npComplete :
    maxNTimesCoverageDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxNTimesCoverageDec

end MetaMathlibExt.Complexity.NPComplete.MaxNTimesCoverage
