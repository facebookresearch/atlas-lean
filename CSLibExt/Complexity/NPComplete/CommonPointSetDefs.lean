/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMMON POINT SET: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MAXIMUM COMMON POINT SET;
T. Akutsu and M. M. Halldórsson, "On the approximation of largest common subtrees and largest
common point sets", Theoretical Computer Science 233 (2000), 33-50,
doi:10.1016/S0304-3975(97)00278-8 (conference version: Proc. ISAAC 1994, LNCS 834, 405-413,
doi:10.1007/3-540-58325-4_205).
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Congruence
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.QuadraticProgrammingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CommonPointSet

open QuadraticProgramming (RatCode ratVal)

/-- An instance: the dimension `d`, the point sets `S₁, …, S_k` (each a list of points, each
point a list of `d` rational coordinates), and the bound `K`. -/
abbrev CommonPointSetInstance := ℕ × List (List (List RatCode)) × ℕ

/-- The point of `ℝ^d` whose coordinates are listed in `x`. -/
noncomputable def point (d : ℕ) (x : List RatCode) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun c => (ratVal (x.getD c ((0, 0), 1)) : ℝ)

/-- Well-formedness of an instance: `d` is positive, the collection is nonempty, every point has
`d` coordinates, every encoded rational has a positive denominator, and `K` is positive. -/
def WellFormed (i : CommonPointSetInstance) : Prop :=
  0 < i.1 ∧ i.2.1 ≠ [] ∧ (∀ S ∈ i.2.1, ∀ x ∈ S, x.length = i.1 ∧ ∀ q ∈ x, 0 < q.2) ∧
    0 < i.2.2

/-- Some set `S'` of at least `K` points of `ℝ^d` is congruent to a subset of every `Sᵢ`. -/
def CommonPointSetFeasible (i : CommonPointSetInstance) : Prop :=
  ∃ m, i.2.2 ≤ m ∧ ∃ v : Fin m → EuclideanSpace ℝ (Fin i.1), Function.Injective v ∧
    ∀ S ∈ i.2.1, ∃ w : Fin m → EuclideanSpace ℝ (Fin i.1),
      (∀ a, ∃ x ∈ S, w a = point i.1 x) ∧ Congruent v w

open Classical in
/-- COMMON POINT SET as a decision problem over bitstrings. -/
noncomputable def commonPointSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CommonPointSetInstance) x with
  | some i => decide (WellFormed i ∧ CommonPointSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CommonPointSet
