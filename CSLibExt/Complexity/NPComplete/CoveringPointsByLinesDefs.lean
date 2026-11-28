/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COVERING POINTS BY LINES: definitions

Source:
N. Megiddo and A. Tamir, "On the complexity of locating linear facilities in the plane",
Operations Research Letters 1 (1982), 194-197, doi:10.1016/0167-6377(82)90039-6;
P. K. Agarwal, C. M. Procopiuc and K. R. Varadarajan, "Approximation algorithms for k-line
center", Algorithms - ESA 2002, LNCS 2461 (2002), 54-63, doi:10.1007/3-540-45749-6_9.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoveringPointsByLines

open GeometricTravelingSalesman (point)

/-- An instance: the points, each a pair of integer coordinates in positive/negative-part
form, and the bound `K`. -/
abbrev CoveringPointsByLinesInstance := List ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ

/-- Well-formedness of an instance: the points are distinct, and `K` is positive. -/
def WellFormed (i : CoveringPointsByLinesInstance) : Prop :=
  (i.1.map point).Nodup ∧ 0 < i.2

/-- There are `K` straight lines, each through two distinct points of `ℝ × ℝ`, such that every
point of `P` lies on one of them. -/
def CoveringPointsByLinesFeasible (i : CoveringPointsByLinesInstance) : Prop :=
  ∃ L : Fin i.2 → (ℝ × ℝ) × (ℝ × ℝ), (∀ j, (L j).1 ≠ (L j).2) ∧
    ∀ q ∈ i.1, ∃ j, ((point q).map Int.cast Int.cast : ℝ × ℝ) ∈ line[ℝ, (L j).1, (L j).2]

open Classical in
/-- COVERING POINTS BY LINES as a decision problem over bitstrings. -/
noncomputable def coveringPointsByLinesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CoveringPointsByLinesInstance) x with
  | some i => decide (WellFormed i ∧ CoveringPointsByLinesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CoveringPointsByLines
