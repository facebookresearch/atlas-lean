/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GROUND STATE OF A PLANAR SPIN GLASS IN A MAGNETIC FIELD is NP-complete

Source:
F. Barahona, "On the computational complexity of Ising spin glass models", Journal of
Physics A: Mathematical and General 15 (1982), 3241-3253,
doi:10.1088/0305-4470/15/10/028;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 4
(1983), 87-100, doi:10.1016/0196-6774(83)90038-X (comment on GROUND STATE OF A SPIN GLASS).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import WantedExt.Complexity.NPComplete.ThreeDimensionalIsingSpinGlassWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarSpinGlassField

/-!
# GROUND STATE OF A PLANAR SPIN GLASS IN A MAGNETIC FIELD is NP-complete

An instance is a planar graph `G = (V, E)`, an integer interaction `J(e)` for each edge, an
integer external field `h(v)` at each vertex, and an integer `K`. The question is whether there
is an assignment of a spin `s(v) ∈ {-1, +1}` to each vertex such that the spin energy

`- ∑_{{u,v} ∈ E} J(u,v) s(u) s(v) - ∑_{v ∈ V} h(v) s(v)`

is `K` or less. All numbers are in binary encoding.

Without the field term the planar problem is polynomial (planar MAX CUT). Barahona (1982)
shows that finding a ground state is NP-hard for the two-dimensional lattice in a magnetic
field; Johnson's column records that "for arbitrary planar graphs, NP-hardness returns when an
external magnetic field is introduced (this adds a new term to the spin energy function)". The
field is given per vertex here; a uniform field `h` is the case of equal values, and
two-dimensional lattices are planar, so the source's instances are contained. NP membership is
immediate (the energy of a given assignment is computed in polynomial time).

Planarity is `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, equivalent to
planarity for finite simple graphs by Fáry's theorem). The integer helpers `intOf` and `spin`
are reused from `ThreeDimensionalIsingSpinGlassWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **GROUND STATE OF A PLANAR SPIN GLASS IN A MAGNETIC FIELD is NP-complete.** Source:
Barahona (1982); Johnson (1983). -/
public theorem_wanted planarSpinGlassField_npComplete :
    planarSpinGlassFieldDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarSpinGlassFieldDec

end MetaMathlibExt.Complexity.NPComplete.PlanarSpinGlassField
