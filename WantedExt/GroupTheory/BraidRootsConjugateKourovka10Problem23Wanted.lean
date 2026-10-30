/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Uniqueness of roots in braid groups up to conjugacy (Kourovka Notebook Problem 10.23)

Kourovka Notebook, Archive of Solved Problems, Problem 10.23 (G. S. Makanin): is it true that
extraction of roots in braid groups is unique up to conjugation?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.BraidRootsConjugateKourovka10Problem23Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.23 (G. S.
Makanin). UnsolvedMath record UM-00700638 (`KOU-10.23`), dataset ulamai/UnsolvedMath v1.8.0.

`Bₙ` is given by Artin's presentation on `σ₁, …, σₙ₋₁` (as in
`BraidConjugacyProblemKourovka1Problem11Wanted`). Uniqueness up to conjugation: `α ^ k = β ^ k` with
`k ≥ 1` implies that `α` and `β` are conjugate; `k = 0` is excluded since `α ^ 0 = β ^ 0` always.
-/

open FreeGroup

/-- Artin's relators for the braid group on `n` strands, in the free group on the generators
`σ₀, …, σ_{n-2}` (indexed by `Fin (n - 1)`): `σᵢ σⱼ = σⱼ σᵢ` when `j ≥ i + 2`, and
`σᵢ σᵢ₊₁ σᵢ = σᵢ₊₁ σᵢ σᵢ₊₁`. -/
def braidRelators (n : ℕ) : Set (FreeGroup (Fin (n - 1))) :=
  {r | ∃ i j : Fin (n - 1),
    (i.val + 2 ≤ j.val ∧ r = of i * of j * (of i)⁻¹ * (of j)⁻¹) ∨
    (i.val + 1 = j.val ∧ r = of i * of j * of i * (of j * of i * of j)⁻¹)}

/-- The braid group `Bₙ` on `n` strands, by Artin's presentation. -/
abbrev BraidGroup (n : ℕ) : Type := PresentedGroup (braidRelators n)

/-- Kourovka 10.23 (G. S. Makanin): extraction of roots in braid groups is unique up to
conjugation: if `α ^ k = β ^ k` in `Bₙ` for some `k ≥ 1`, then `α` and `β` are conjugate. -/
def braidRootsUniqueUpToConjugacy : Prop :=
  ∀ (n k : ℕ), 0 < k → ∀ α β : BraidGroup n, α ^ k = β ^ k → IsConj α β

/--
Resolved true: González-Meneses proved Makanin's conjecture that if `α ^ k = β ^ k` in `Bₙ` for some
nonzero integer `k`, then `α` and `β` are conjugate; the Kourovka Archive answers 10.23 "Yes, it is
true". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.23
(G. S. Makanin); resolution: J. González-Meneses, The nth root of a braid is unique up to conjugacy,
Algebr. Geom. Topol. 3 (2003), 1103-1118, main theorem; Kourovka Archive, Problem 10.23 ("Yes, it is
true"), https://doi.org/10.2140/agt.2003.3.1103.
-/
public theorem_wanted braidRootsUniqueUpToConjugacy_holds : braidRootsUniqueUpToConjugacy

end MathlibExt.GroupTheory.BraidRootsConjugateKourovka10Problem23Wanted
