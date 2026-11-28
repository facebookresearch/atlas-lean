/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Elliptic.ComplexMultiplication
public import MathlibExt.Analysis.SpecialFunctions.Elliptic.JInvariant
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# The ring class field of an imaginary quadratic order

For a subfield $K \subseteq \mathbb{C}$ and a subring $\mathcal{O} \subseteq \mathbb{C}$,
`ringClassField K 𝒪` is the subfield of $\mathbb{C}$ generated over $K$ by the $j$-invariants
`PeriodPair.jInvariant` of the lattices contained in $K$ whose endomorphism ring is
$\mathcal{O}$. When $K$ is an imaginary quadratic field and $\mathcal{O}$ an order in $K$, these
lattices are the nonzero proper fractional $\mathcal{O}$-ideals, and the field is the ring class
field of $\mathcal{O}$ of Sutherland's Definition 21.3 (see the docstring of `ringClassField`).

The source is Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT
OpenCourseWare, Fall 2025, Lecture 21, Definition 21.3, p. 4.
-/

@[expose] public section

set_option autoImplicit false

/-- The ring class field of `𝒪` over `K`: the subfield of `ℂ` generated over the subfield `K` by
the $j$-invariants `PeriodPair.jInvariant L` of the period pairs `L` whose lattice $\Lambda$ is
contained in `K` and has endomorphism ring
$\{\lambda \in \mathbb{C} : \lambda \Lambda \subseteq \Lambda\}$ equal to `𝒪`
(`L.IsProperIdeal 𝒪`). The definition is made for every subfield `K` and subring `𝒪`.

When `K` is an imaginary quadratic field and `𝒪` an order in `K`, the lattices contained in `K`
with endomorphism ring `𝒪` are the nonzero proper fractional `𝒪`-ideals (Lecture 17,
Definition 17.2, p. 2, and §17.3, p. 4). Each of them is $\lambda \mathfrak{a}$ for a proper
`𝒪`-ideal $\mathfrak{a}$ (Lemma 17.9, p. 4), with the same $j$-invariant as $\mathfrak{a}$
(Lecture 15, Theorem 15.5, p. 4). The $j(\mathfrak{a})$ are the $j$-invariants of the elliptic
curves over $\mathbb{C}$ with complex multiplication by `𝒪`, the roots of the Hilbert class
polynomial $H_D$ (Lecture 20, §20.3, p. 5). So in that case `ringClassField K 𝒪` is the
splitting field of $H_D$ over `K`, the ring class field of `𝒪` (Lecture 21, Definition 21.3,
p. 4). That a single one of these $j$-invariants generates it, the second description in
Definition 21.3, is Corollary 21.2 (Lecture 21, p. 4). These identifications are not proved
here.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lecture 21, Definition 21.3, p. 4, with Lecture 15, Theorem 15.5; Lecture 17,
Definition 17.2, §17.3 and Lemma 17.9; Lecture 20, §20.3; and Lecture 21, Corollary 21.2. -/
noncomputable def ringClassField (K : Subfield ℂ) (𝒪 : Subring ℂ) : IntermediateField K ℂ :=
  IntermediateField.adjoin K
    {x | ∃ L : PeriodPair, L.IsProperIdeal 𝒪 ∧ (L.lattice : Set ℂ) ⊆ K ∧ x = L.jInvariant}

/-- The $j$-invariant of a period pair whose lattice is contained in `K` and has endomorphism
ring `𝒪` lies in `ringClassField K 𝒪`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lecture 21, Definition 21.3, p. 4. -/
theorem jInvariant_mem_ringClassField {K : Subfield ℂ} {𝒪 : Subring ℂ} {L : PeriodPair}
    (hL : L.IsProperIdeal 𝒪) (hLK : (L.lattice : Set ℂ) ⊆ K) :
    L.jInvariant ∈ ringClassField K 𝒪 :=
  IntermediateField.subset_adjoin K _ ⟨L, hL, hLK, rfl⟩
