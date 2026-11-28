/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM AREA POLYGONALIZATION: definitions

Source:
S. P. Fekete, "On simple polygonalizations with optimal area", Discrete & Computational
Geometry 23 (2000), 73-110, doi:10.1007/PL00009492, Theorem 4.1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumAreaPolygonalizationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumAreaPolygonalization

open MetaMathlibExt.Complexity.NPComplete.QuadraticProgramming (ratVal)
open MetaMathlibExt.Complexity.NPComplete.MinimumAreaPolygonalization
  (MinimumAreaPolygonalizationInstance WellFormed point twiceSignedArea)

/-- Some simple polygon with vertex set exactly `S` has area at least `A`: some cyclic order `σ`
of the points gives a simple polygon `p_{σ 0}, …, p_{σ (n-1)}` whose shoelace area is at least
`A`. -/
def MaximumAreaPolygonalizationFeasible (i : MinimumAreaPolygonalizationInstance) : Prop :=
  ∃ σ : Equiv.Perm (Fin i.1.length),
    MathlibExt.Geometry.SegmentVisibilityShared.IsSimplePolygon (point i ∘ σ) ∧
      ratVal i.2 ≤ (|twiceSignedArea i σ| : ℚ) / 2

open Classical in
/-- MAXIMUM AREA POLYGONALIZATION as a decision problem over bitstrings. -/
noncomputable def maximumAreaPolygonalizationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumAreaPolygonalizationInstance) x with
  | some i => decide (WellFormed i ∧ MaximumAreaPolygonalizationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumAreaPolygonalization
