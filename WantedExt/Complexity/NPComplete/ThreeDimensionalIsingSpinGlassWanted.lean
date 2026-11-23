/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3D ISING SPIN GLASS GROUND STATE is NP-complete

Source:
F. Barahona, "On the computational complexity of Ising spin glass models", Journal of
Physics A: Mathematical and General 15 (1982), 3241-3253,
doi:10.1088/0305-4470/15/10/028.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalIsingSpinGlass

/-!
# 3D ISING SPIN GLASS GROUND STATE is NP-complete

INSTANCE: a finite three-dimensional grid graph `G = (V, E)`, couplings `J_{ij} ∈ {-1, 0, 1}`
on its edges, and an integer `E₀`.
QUESTION: is there a spin assignment `s ∈ {-1, +1}^V` whose energy `-∑_{(ij) ∈ E} J_{ij} sᵢ sⱼ`
is at most `E₀`?

Barahona proves that finding a ground state of this model is NP-hard, "even in a two-level grid
and with interactions restricted to be {-1, 0, 1}" (problem P3, the two-level spin glass); the
energy of a given assignment is computable in polynomial time.

The grid is the box `{0, …, a - 1} × {0, …, b - 1} × {0, …, c - 1}` of the cubic lattice,
whose sites `((x, y), z)` are adjacent when they differ by one in exactly one coordinate:
the Mathlib graph `SimpleGraph.hasse ℕ □ SimpleGraph.hasse ℕ □ SimpleGraph.hasse ℕ`. The
couplings are a list of entries `(u, v, J)` on distinct lattice edges of the box; an edge that
is not listed has coupling `0`, which contributes nothing to the energy. Integers are encoded
as pairs of naturals `(positive part, negative part)` (`intOf`), as in
`WantedExt.Complexity.NPComplete.ZeroOneILPWanted`. A spin assignment is a map from sites to
`Bool` (`true` is `+1`, `false` is `-1`); only its values on the box enter the energy.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **3D ISING SPIN GLASS GROUND STATE is NP-complete.** Source: Barahona (1982). -/
public theorem_wanted threeDimensionalIsingSpinGlass_npComplete :
    threeDimensionalIsingSpinGlassDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeDimensionalIsingSpinGlassDec

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalIsingSpinGlass
