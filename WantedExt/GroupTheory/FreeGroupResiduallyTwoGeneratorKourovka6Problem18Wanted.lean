/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Free groups residually in classes of 2-generator groups (Kourovka Notebook Problem 6.18)

Kourovka Notebook, Archive of Solved Problems, Problem 6.18 (V. M. Levchuk): (Well-known problem.)
Suppose that a class 𝔎 of 2-generator groups generates the variety of all groups. Is a non-cyclic
free group residually in 𝔎?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupResiduallyTwoGeneratorKourovka6Problem18Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.18 (V. M.
Levchuk). UnsolvedMath record UM-00700365 (`KOU-6.18`), dataset ulamai/UnsolvedMath v1.8.0.

The class is an indexed family `K i`, `i : ι`, of `2`-generator groups; it generates the variety of
all groups when no non-trivial word of `FreeGroup ℕ` is a law in all of them. Residually in `𝔎` is
read with quotients: every non-trivial element of the free group survives a homomorphism onto a
member of the class (with arbitrary homomorphisms the property would follow from the generation
hypothesis). The non-cyclic free group of the counterexample has rank `2`: Pride's thesis abstract
(Bull. Austral. Math. Soc. 10 (1974), 477-478) states that for `G = ⟨a, t; [a, t]ⁿ⟩`, `n > 1`, a
free group `F` is residually `{G}` exactly when the rank of `F` is at least `3`, so the free group
of rank `2` is not residually `{G}`; this is a statement about quotients, since `F₂` embeds in `G`.
-/

/-- Kourovka 6.18 (V. M. Levchuk): if a class `K i` (`i : ι`) of `2`-generator groups generates the
variety of all groups (no non-trivial law holds in all of them), then the free group of rank `2` is
residually in the class: every non-trivial element survives some homomorphism of `F₂` onto some
`K i`. -/
def freeGroupResiduallyInTwoGeneratorClass : Prop :=
  ∀ (ι : Type) (K : ι → Type) [∀ i, Group (K i)],
    (∀ i, ∃ a b : K i, Subgroup.closure {a, b} = ⊤) →
    (∀ w : FreeGroup ℕ, w ≠ 1 → ∃ i, ∃ φ : FreeGroup ℕ →* K i, φ w ≠ 1) →
    ∀ w : FreeGroup (Fin 2), w ≠ 1 →
      ∃ i, ∃ φ : FreeGroup (Fin 2) →* K i, Function.Surjective φ ∧ φ w ≠ 1

/--
Resolved false: the Kourovka Archive answers 6.18 "Not always", citing Pride (1973): some class of
`2`-generator groups generates the variety of all groups while the free group of rank `2` is not
residually in it. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
6.18 (V. M. Levchuk); resolution: S. J. Pride, Residual properties of free groups. III, Math. Z. 132
(1973), 245-248 (the Archive prints volume 131); S. J. Pride, Residual properties of free groups
(thesis abstract), Bull. Austral. Math. Soc. 10 (1974), 477-478, thesis abstract: for G = ⟨a, t; [a,
t]ⁿ⟩ (n > 1) a free group F is residually {G} if and only if the rank of F is at least three, so a
free group of rank 2 is not residually {G}; Kourovka Archive, Problem 6.18: Not always (Pride),
https://doi.org/10.1017/S0004972700041174.
-/
public theorem_wanted freeGroupResiduallyInTwoGeneratorClass_refuted :
    ¬ freeGroupResiduallyInTwoGeneratorClass

end MathlibExt.GroupTheory.FreeGroupResiduallyTwoGeneratorKourovka6Problem18Wanted
