/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Embedding the braid group `B₄` in `Aut(F₂)` (Kourovka Notebook Problem 17.14)

Kourovka Notebook, Archive of Solved Problems, Problem 17.14 (V. G. Bardakov): can the braid group
`Bₙ` for `n ≥ 4` be embedded into the automorphism group `Aut(F_{n-2})` of a free group `F_{n-2}` of
rank `n - 2`? (Artin's theorem embeds `Bₙ` into `Aut(Fₙ)`, and Perron and Vannier embedded `Bₙ`, `n
≥ 3`, into `Aut(F_{n-1})`.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.BraidGroupFourAutFreeGroupTwoKourovka17Problem14Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.14 (V. G.
Bardakov). UnsolvedMath record UM-00701316 (`KOU-17.14`), dataset ulamai/UnsolvedMath v1.8.0.

The resolution settles the case `n = 4` negatively, and the target is that case: `B₄`, given by
Artin's presentation on `σ₁, σ₂, σ₃`, embeds in `MulAut (FreeGroup (Fin 2))`. Its refutation shows
that the answer is not "yes" for every `n ≥ 4`; the cases `n ≥ 5` are not settled by the source and
are not formalized.
-/

/-- The braid group `B₄ = ⟨σ₁, σ₂, σ₃ | σ₁σ₂σ₁ = σ₂σ₁σ₂, σ₂σ₃σ₂ = σ₃σ₂σ₃, σ₁σ₃ = σ₃σ₁⟩`, with
`σ₁ = x₀`, `σ₂ = x₁`, `σ₃ = x₂`. -/
abbrev BraidGroupFour : Type :=
  PresentedGroup ({FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 *
      (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1)⁻¹,
    FreeGroup.of 1 * FreeGroup.of 2 * FreeGroup.of 1 *
      (FreeGroup.of 2 * FreeGroup.of 1 * FreeGroup.of 2)⁻¹,
    FreeGroup.of 0 * FreeGroup.of 2 * (FreeGroup.of 2 * FreeGroup.of 0)⁻¹} :
      Set (FreeGroup (Fin 3)))

/-- Kourovka 17.14 (V. G. Bardakov) for `n = 4`: the braid group `B₄` embeds in the automorphism
group `Aut(F₂)` of the free group of rank `2`. -/
def braidGroupFourEmbedsInAutFreeGroupTwo : Prop :=
  ∃ f : BraidGroupFour →* MulAut (FreeGroup (Fin 2)), Function.Injective f

/--
Resolved false: the Kourovka Archive answers 17.14 "No, it cannot for `n = 4`", citing Bardakov and
Bellingeri (2016): the braid group `B₄` does not embed in `Aut(F₂)`. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.14 (V. G. Bardakov); resolution:
V. G. Bardakov and P. Bellingeri, in Knot theory and its applications (ICTS program KTH-2013, IISER
Mohali), Contemp. Math. 670, Amer. Math. Soc., 2016, 285-298, Kourovka Archive, Problem 17.14 (No,
it cannot for n = 4).
-/
public theorem_wanted braidGroupFourEmbedsInAutFreeGroupTwo_refuted :
    ¬ braidGroupFourEmbedsInAutFreeGroupTwo

end MathlibExt.GroupTheory.BraidGroupFourAutFreeGroupTwoKourovka17Problem14Wanted
