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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PlanarSpinGlassFieldDefs

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

/-- **GROUND STATE OF A PLANAR SPIN GLASS IN A MAGNETIC FIELD is NP-complete.** Source:
Barahona (1982); Johnson (1983). -/
public theorem_wanted planarSpinGlassField_npComplete :
    planarSpinGlassFieldDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarSpinGlassFieldDec

end MetaMathlibExt.Complexity.NPComplete.PlanarSpinGlassField
