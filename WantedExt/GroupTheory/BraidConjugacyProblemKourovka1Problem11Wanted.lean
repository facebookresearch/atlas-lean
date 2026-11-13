/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The conjugacy problem for braid groups (Kourovka Notebook Problem 1.11)

Kourovka Notebook, Archive of Solved Problems, Problem 1.11 (E. Artin; M. D. Greendlinger): the
conjugacy problem for the braid groups `Bₙ`, `n > 4`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.BraidConjugacyProblemKourovka1Problem11Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.11 (E. Artin;
M. D. Greendlinger). UnsolvedMath record UM-00700009 (`KOU-1.11`), dataset ulamai/UnsolvedMath
v1.8.0.

`Bₙ` is given by Artin's presentation on `σ₁, …, σₙ₋₁`. Solvability of the conjugacy problem is
`ComputablePred` on pairs of braid words `List (Fin (n - 1) × Bool)`, the encoding used for word
problems elsewhere in `WantedExt` (`NovikovBooneWanted`). The range `n > 4` follows the problem;
Garside's algorithm covers all `n`.
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

/-- The braid word `w` (a list of letters `(i, b)`: `σᵢ` if `b`, `σᵢ⁻¹` otherwise) as an element
of `Bₙ`. -/
def braidOfWord (n : ℕ) (w : List (Fin (n - 1) × Bool)) : BraidGroup n :=
  PresentedGroup.mk (braidRelators n) (FreeGroup.mk w)

/-- Kourovka 1.11 (E. Artin): for every `n > 4` the conjugacy problem in `Bₙ` is solvable: the
predicate "the braid words `u` and `v` represent conjugate elements of `Bₙ`" is computable. -/
def braidConjugacyProblemSolvable : Prop :=
  ∀ n : ℕ, 4 < n → ComputablePred fun uv : List (Fin (n - 1) × Bool) × List (Fin (n - 1) × Bool) =>
    IsConj (braidOfWord n uv.1) (braidOfWord n uv.2)

/--
Resolved true: the Kourovka Archive records the affirmative solution of Makanin (1968) and Garside
(1969), whose algorithm decides conjugacy in `Bₙ` for every `n`. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.11 (E. Artin; M. D. Greendlinger);
resolution: F. A. Garside, The braid group and other groups, Quart. J. Math. Oxford Ser. (2) 20
(1969), 235-254; G. S. Makanin, The conjugacy problem in the braid group, Soviet Math. Dokl. 9
(1968), 1156-1157, Garside's solution of the conjugacy problem; Kourovka Archive, Problem 1.11,
https://doi.org/10.1093/qmath/20.1.235.
-/
public theorem_wanted braidConjugacyProblemSolvable_holds : braidConjugacyProblemSolvable

end MathlibExt.GroupTheory.BraidConjugacyProblemKourovka1Problem11Wanted
