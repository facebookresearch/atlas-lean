/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GROUND STATE OF A PLANAR SPIN GLASS IN A MAGNETIC FIELD: definitions

Source:
F. Barahona, "On the computational complexity of Ising spin glass models", Journal of
Physics A: Mathematical and General 15 (1982), 3241-3253,
doi:10.1088/0305-4470/15/10/028;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 4
(1983), 87-100, doi:10.1016/0196-6774(83)90038-X (comment on GROUND STATE OF A SPIN GLASS).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.ThreeDimensionalIsingSpinGlassDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarSpinGlassField



open MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalIsingSpinGlass (intOf spin)

/-- An instance: vertex count `n`, edges as `(u, v, J)`, the fields `h(v)` (indexed by
vertex), and the bound `K`; every integer is a pair `(p, q)` standing for `p - q`. -/
abbrev PlanarSpinGlassFieldInstance :=
  ℕ × List (ℕ × ℕ × (ℕ × ℕ)) × List (ℕ × ℕ) × (ℕ × ℕ)

/-- The endpoint pairs of the edge list. -/
def endpoints (i : PlanarSpinGlassFieldInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PlanarSpinGlassFieldInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (endpoints i)

/-- Well-formedness of an instance: a simple edge list on `Fin n` (no loops, no repeated or
reversed edges), one field value per vertex, and a planar graph. -/
def WellFormed (i : PlanarSpinGlassFieldInstance) : Prop :=
  ((endpoints i).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧ (e.2.1, e.1) ∉ endpoints i) ∧
    i.2.2.1.length = i.1 ∧ (Graph i).IsPlanar

/-- The spin value at vertex index `k` (`0` off range, which a well-formed instance never
uses). -/
def spinAt (i : PlanarSpinGlassFieldInstance) (s : Fin i.1 → Bool) (k : ℕ) : ℤ :=
  if h : k < i.1 then spin (s ⟨k, h⟩) else 0

/-- The spin energy of the assignment `s` (`true` is spin `+1`):
`- ∑_e J(e) s(u) s(v) - ∑_v h(v) s(v)`. -/
def energy (i : PlanarSpinGlassFieldInstance) (s : Fin i.1 → Bool) : ℤ :=
  -(i.2.1.map fun e => intOf e.2.2 * spinAt i s e.1 * spinAt i s e.2.1).sum -
    ∑ v : Fin i.1, intOf (i.2.2.1.getD v (0, 0)) * spin (s v)

/-- Some spin assignment has energy at most `K`. -/
def PlanarSpinGlassFieldFeasible (i : PlanarSpinGlassFieldInstance) : Prop :=
  ∃ s : Fin i.1 → Bool, energy i s ≤ intOf i.2.2.2

open Classical in
/-- GROUND STATE OF A PLANAR SPIN GLASS IN A MAGNETIC FIELD as a decision problem over
bitstrings. -/
noncomputable def planarSpinGlassFieldDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PlanarSpinGlassFieldInstance) x with
  | some i => decide (WellFormed i ∧ PlanarSpinGlassFieldFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PlanarSpinGlassField
