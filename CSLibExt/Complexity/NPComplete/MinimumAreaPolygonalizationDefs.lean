/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM AREA POLYGONALIZATION: definitions

Source:
S. P. Fekete, "On simple polygonalizations with optimal area", Discrete and Computational
Geometry 23(1) (2000), 73-110, doi:10.1007/PL00009492.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Logic.Equiv.Fin.Rotate
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.QuadraticProgrammingDefs
public import MathlibExt.Geometry.SegmentVisibilitySharedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumAreaPolygonalization

open MetaMathlibExt.Complexity.NPComplete.QuadraticProgramming (RatCode ratVal)

/-- An instance: the points of `S`, each a pair of integer coordinates given as
(positive part, negative part) pairs, and the bound `A`. -/
abbrev MinimumAreaPolygonalizationInstance := List ((ℕ × ℕ) × (ℕ × ℕ)) × RatCode

/-- The integer coordinates of the `k`-th listed point. -/
def coord (i : MinimumAreaPolygonalizationInstance) (k : Fin i.1.length) : ℤ × ℤ :=
  ((i.1[k].1.1 : ℤ) - i.1[k].1.2, (i.1[k].2.1 : ℤ) - i.1[k].2.2)

/-- The `k`-th listed point in the real plane. -/
noncomputable def point (i : MinimumAreaPolygonalizationInstance) (k : Fin i.1.length) :
    ℝ × ℝ :=
  ((coord i k).1, (coord i k).2)

/-- Well-formedness of an instance: the listed points are pairwise distinct (each point of `S`
is listed once), and the denominator of `A` is positive. -/
def WellFormed (i : MinimumAreaPolygonalizationInstance) : Prop :=
  Function.Injective (coord i) ∧ 0 < i.2.2

/-- Twice the signed area of the polygon through the points in the cyclic order `σ` (shoelace
formula): `∑ⱼ (xⱼ yⱼ₊₁ - xⱼ₊₁ yⱼ)` over the vertices `p_{σ j}`, indices mod `n`. -/
def twiceSignedArea (i : MinimumAreaPolygonalizationInstance)
    (σ : Equiv.Perm (Fin i.1.length)) : ℤ :=
  ∑ j, ((coord i (σ j)).1 * (coord i (σ (finRotate _ j))).2 -
    (coord i (σ (finRotate _ j))).1 * (coord i (σ j)).2)

/-- Some simple polygon with vertex set exactly `S` has area at most `A`: some cyclic order `σ`
of the points gives a simple polygon `p_{σ 0}, …, p_{σ (n-1)}` whose shoelace area is at most
`A`. -/
def MinimumAreaPolygonalizationFeasible (i : MinimumAreaPolygonalizationInstance) : Prop :=
  ∃ σ : Equiv.Perm (Fin i.1.length),
    MathlibExt.Geometry.SegmentVisibilityShared.IsSimplePolygon (point i ∘ σ) ∧
      (|twiceSignedArea i σ| : ℚ) / 2 ≤ ratVal i.2

open Classical in
/-- MINIMUM AREA POLYGONALIZATION as a decision problem over bitstrings. -/
noncomputable def minimumAreaPolygonalizationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumAreaPolygonalizationInstance) x with
  | some i => decide (WellFormed i ∧ MinimumAreaPolygonalizationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumAreaPolygonalization
