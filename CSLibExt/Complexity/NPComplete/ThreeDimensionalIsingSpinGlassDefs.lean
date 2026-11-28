/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3D ISING SPIN GLASS GROUND STATE: definitions

Source:
F. Barahona, "On the computational complexity of Ising spin glass models", Journal of
Physics A: Mathematical and General 15 (1982), 3241-3253,
doi:10.1088/0305-4470/15/10/028.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalIsingSpinGlass

/-- A site `((x, y), z)` of the cubic lattice. -/
abbrev Site := (ℕ × ℕ) × ℕ

/-- An instance: the box dimensions `(a, b, c)`, the couplings `(u, v, J)` with `J` an encoded
integer, and the energy bound `E₀`, an encoded integer. -/
abbrev ThreeDimensionalIsingSpinGlassInstance :=
  (ℕ × ℕ × ℕ) × List (Site × Site × (ℕ × ℕ)) × (ℕ × ℕ)

/-- The integer `p.1 - p.2` encoded by a pair of naturals. -/
def intOf (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)

/-- The cubic lattice: two sites are adjacent when they differ by one in exactly one
coordinate. -/
abbrev lattice : SimpleGraph Site :=
  SimpleGraph.hasse ℕ □ SimpleGraph.hasse ℕ □ SimpleGraph.hasse ℕ

/-- The site lies in the box with dimensions `d = (a, b, c)`. -/
def InBox (d : ℕ × ℕ × ℕ) (v : Site) : Prop := v.1.1 < d.1 ∧ v.1.2 < d.2.1 ∧ v.2 < d.2.2

/-- Well-formedness of an instance: every coupling sits on a lattice edge of the box and has
value in `{-1, 0, 1}`, and no edge carries two couplings. -/
def WellFormed (i : ThreeDimensionalIsingSpinGlassInstance) : Prop :=
  (∀ e ∈ i.2.1, InBox i.1 e.1 ∧ InBox i.1 e.2.1 ∧ lattice.Adj e.1 e.2.1 ∧
      -1 ≤ intOf e.2.2 ∧ intOf e.2.2 ≤ 1) ∧
    (i.2.1.map fun e => s(e.1, e.2.1)).Nodup

/-- The value `+1` or `-1` of a spin. -/
def spin (b : Bool) : ℤ := if b then 1 else -1

/-- The energy `-∑_{(ij) ∈ E} J_{ij} sᵢ sⱼ` of a spin assignment. -/
def energy (i : ThreeDimensionalIsingSpinGlassInstance) (s : Site → Bool) : ℤ :=
  -(i.2.1.map fun e => intOf e.2.2 * spin (s e.1) * spin (s e.2.1)).sum

/-- Some spin assignment has energy at most `E₀`. -/
def ThreeDimensionalIsingSpinGlassFeasible (i : ThreeDimensionalIsingSpinGlassInstance) :
    Prop :=
  ∃ s : Site → Bool, energy i s ≤ intOf i.2.2

open Classical in
/-- 3D ISING SPIN GLASS GROUND STATE as a decision problem over bitstrings. -/
noncomputable def threeDimensionalIsingSpinGlassDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeDimensionalIsingSpinGlassInstance) x with
  | some i => decide (WellFormed i ∧ ThreeDimensionalIsingSpinGlassFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalIsingSpinGlass
