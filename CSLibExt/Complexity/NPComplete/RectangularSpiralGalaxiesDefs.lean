/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTANGULAR SPIRAL GALAXIES: definitions

Source:
E. D. Demaine, M. Löffler and C. Schmidt, "Rectangular Spiral Galaxies are still hard",
Computational Geometry 110 (2023), 101949, doi:10.1016/j.comgeo.2022.101949, Section 1
(Rectangular Galaxies) and Theorem 2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SpiralGalaxiesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectangularSpiralGalaxies

/-- An instance: a Spiral Galaxies puzzle, drawn on its doubled lattice
(`SpiralGalaxies.SpiralGalaxiesInstance`). -/
abbrev RectangularSpiralGalaxiesInstance := SpiralGalaxies.SpiralGalaxiesInstance

/-- Well-formedness: that of the Spiral Galaxies puzzle (a board with `m, n ≥ 1`). -/
def WellFormed (i : RectangularSpiralGalaxiesInstance) : Prop :=
  SpiralGalaxies.WellFormed i

/-- The puzzle has a Spiral Galaxies solution (`SpiralGalaxies.IsSolution`) all of whose galaxies
are rectangles of cells. -/
def RectangularSpiralGalaxiesFeasible (i : RectangularSpiralGalaxiesInstance) : Prop :=
  ∃ g : Fin (SpiralGalaxies.rows i) × Fin (SpiralGalaxies.cols i) →
      Fin (SpiralGalaxies.centres i).length, SpiralGalaxies.IsSolution i g ∧
    ∀ j : Fin (SpiralGalaxies.centres i).length, ∃ r₁ r₂ c₁ c₂ : ℕ,
      ∀ p : Fin (SpiralGalaxies.rows i) × Fin (SpiralGalaxies.cols i),
      g p = j ↔ (r₁ ≤ (p.1 : ℕ) ∧ (p.1 : ℕ) < r₂ ∧ c₁ ≤ (p.2 : ℕ) ∧ (p.2 : ℕ) < c₂)

open Classical in
/-- RECTANGULAR SPIRAL GALAXIES as a decision problem over bitstrings. -/
noncomputable def rectangularSpiralGalaxiesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RectangularSpiralGalaxiesInstance) x with
  | some i => decide (WellFormed i ∧ RectangularSpiralGalaxiesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RectangularSpiralGalaxies
