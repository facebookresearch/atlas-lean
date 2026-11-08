/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monochrome symmetric subsets of infinite abelian groups (Kourovka Notebook Problem 15.77)

Kourovka Notebook, Problem 15.77 (I. V. Protasov): elements `a, b` of a group `G` are symmetric with
respect to `g ∈ G` if `a = g b⁻¹ g`. Let `G` be an infinite abelian group and `α < |G|` a cardinal.
Is it true that for any `n`-colouring `χ : G → {0, …, n - 1}` there is a monochrome subset of
cardinality `α` that is symmetric with respect to some element of `G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

namespace MathlibExt.GroupTheory.MonochromeSymmetricSubsetKourovka15Problem77Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.77 (I. V. Protasov). UnsolvedMath record
UM-00701165 (`KOU-15.77`), dataset ulamai/UnsolvedMath v1.8.0.

Abelian groups are written additively, so `a = g b⁻¹ g` reads `a = 2g - b`, and a symmetric set is
one closed under `a ↦ 2g - a`. The number `n` of colours is arbitrary (the case `n ≤ 3` was known),
and `α` ranges over all cardinals below `|G|`, finite or infinite.
-/

/-- Kourovka 15.77 (I. V. Protasov), written additively: for every infinite abelian group `G`,
cardinal `α < |G|` and colouring `χ : G → Fin n`, some monochrome set `A ⊆ G` of cardinality `α` is
symmetric with respect to some `g ∈ G`, i.e. `2g - a ∈ A` for every `a ∈ A`. -/
def monochromeSymmetricSubsetExists : Prop :=
  ∀ (G : Type) [AddCommGroup G], Infinite G → ∀ α : Cardinal, α < Cardinal.mk G →
    ∀ (n : ℕ) (χ : G → Fin n), ∃ A : Set G, Cardinal.mk A = α ∧ (∃ c, ∀ a ∈ A, χ a = c) ∧
      ∃ g : G, ∀ a ∈ A, g + g - a ∈ A

/--
Resolved true: Jayadevan proved that if `G` is an infinite abelian group and `α < |G|`, every finite
colouring of `G` has a monochromatic set `S` of cardinality exactly `α` with `2g - S = S` for some
`g ∈ G`; the Kourovka Notebook (21st issue) marks 15.77 solved, "Yes, it is true" (AI solution
confirmed by I. V. Protasov). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.77 (I. V.
Protasov); resolution: A. Jayadevan, Monochromatic symmetric subsets in finite colourings of
infinite abelian groups, preprint, Zenodo record 22909420 (2026), AI-generated solution confirmed by
I. V. Protasov, main theorem (for G infinite abelian and α < |G|, every finite colouring has a
monochromatic S with |S| = α and 2g - S = S for some g); the Kourovka Notebook (21st issue) marks
15.77 solved, https://zenodo.org/records/22909420.
-/
public theorem_wanted monochromeSymmetricSubsetExists_holds : monochromeSymmetricSubsetExists

end MathlibExt.GroupTheory.MonochromeSymmetricSubsetKourovka15Problem77Wanted
