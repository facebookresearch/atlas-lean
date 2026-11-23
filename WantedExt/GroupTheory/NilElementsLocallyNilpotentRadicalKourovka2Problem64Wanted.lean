/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nil-elements and the locally nilpotent radical of linear groups (Kourovka Notebook Problem 2.64)

Kourovka Notebook, Archive of Solved Problems, Problem 2.64 (B. I. Plotkin): does the set of
nil-elements of a finite-dimensional linear group coincide with its locally nilpotent radical?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Matrix.Mul
public import WantedExt.GroupTheory.LocallyNilpotentShared

@[expose] public section

namespace MathlibExt.GroupTheory.NilElementsLocallyNilpotentRadicalKourovka2Problem64Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.64 (B. I.
Plotkin). UnsolvedMath record UM-00700134 (`KOU-2.64`), dataset ulamai/UnsolvedMath v1.8.0.

A finite-dimensional linear group is a subgroup of `GLₙ(D) = (Mₙ(D))ˣ` over a skew field `D`, the
setting of the Archive's counterexample. A nil-element is a left Engel element: for every `x` some
iterated commutator `[x, g, …, g]` is `1`, with `[y, g] = y⁻¹ g⁻¹ y g`. The locally nilpotent
radical is the Hirsch-Plotkin radical `hirschPlotkinRadical`, the join of all locally nilpotent
normal subgroups (shared with the Kourovka 1.45 entry in
`WantedExt.GroupTheory.LocallyNilpotentShared`).
-/

open MathlibExt.GroupTheory.LocallyNilpotentShared

/-- `g` is a nil-element of `G` (a left Engel element): for every `x ∈ G` some iterated commutator
`[x, g, …, g]` equals `1`, where `[y, g] = y⁻¹ g⁻¹ y g`. -/
def IsNilElement {G : Type} [Group G] (g : G) : Prop :=
  ∀ x : G, ∃ n : ℕ, (fun y => y⁻¹ * g⁻¹ * y * g)^[n] x = 1

/-- Kourovka 2.64 (B. I. Plotkin): in every finite-dimensional linear group `G ≤ GLₙ(D)` over a
skew field `D`, the set of nil-elements coincides with the locally nilpotent radical. -/
def nilElementsEqualLocallyNilpotentRadical : Prop :=
  ∀ (D : Type) [DivisionRing D] (n : ℕ) (G : Subgroup (Matrix (Fin n) (Fin n) D)ˣ),
    {g : G | IsNilElement g} = (hirschPlotkinRadical G : Set G)

/--
Resolved false: the Kourovka Archive answers 2.64 "Not always" (V. A. Roman'kov, 1978): Golod's
non-nilpotent 3-generator nil-group over `ℚ` is residually torsion-free nilpotent, hence orderable,
hence embeds in `GLₙ` over a skew field by Mal'cev's theorem; all of its elements are nil-elements,
but being finitely generated and not nilpotent it is not locally nilpotent, so its locally nilpotent
radical is a proper subgroup. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 2.64 (B. I. Plotkin); resolution: V. A. Roman'kov, 1978 (Golod's group); E. S.
Golod's non-nilpotent 3-generator nil-group; Mal'cev's embedding of orderable groups in skew fields,
Kourovka Archive, Problem 2.64: Not always; Golod's non-nilpotent 3-generator nil-group built from
an algebra over Q is residually torsion-free nilpotent, hence orderable, hence embeddable in GL_n
over some skew field by Mal'cev's theorem (Roman'kov, 1978), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted nilElementsEqualLocallyNilpotentRadical_refuted :
    ¬ nilElementsEqualLocallyNilpotentRadical

end MathlibExt.GroupTheory.NilElementsLocallyNilpotentRadicalKourovka2Problem64Wanted
