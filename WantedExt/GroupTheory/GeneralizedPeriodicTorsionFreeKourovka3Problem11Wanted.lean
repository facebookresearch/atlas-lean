/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Torsion-free groups of generalized periodic elements (Kourovka Notebook Problem 3.11)

Kourovka Notebook, Archive of Solved Problems, Problem 3.11 (Yu. M. Gorchakov): an element `g` of a
group `G` is said to be generalized periodic if there exist `x₁, …, xₙ ∈ G` such that `x₁⁻¹ g x₁ ⋯
xₙ⁻¹ g xₙ = 1`. Does there exist a finitely generated torsion-free group all of whose elements are
generalized periodic?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.GeneralizedPeriodicTorsionFreeKourovka3Problem11Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.11 (Yu. M.
Gorchakov). UnsolvedMath record UM-00700165 (`KOU-3.11`), dataset ulamai/UnsolvedMath v1.8.0.

The group is required to be non-trivial (the trivial group would qualify vacuously) and `n ≥ 1` (the
empty product is `1`). Torsion-free: non-identity elements have infinite order.
-/

/-- Kourovka 3.11 (Yu. M. Gorchakov): there is a non-trivial finitely generated torsion-free
group all of whose elements `g` are generalized periodic: `x₁⁻¹ g x₁ ⋯ xₙ⁻¹ g xₙ = 1` for some
`n ≥ 1` and `x₁, …, xₙ`. -/
def existsFGTorsionFreeGeneralizedPeriodic : Prop :=
  ∃ (G : Type) (_ : Group G), Nontrivial G ∧ Group.FG G ∧ (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) ∧
    ∀ g : G, ∃ (n : ℕ) (x : Fin n → G), 1 ≤ n ∧
      ((List.finRange n).map fun i => (x i)⁻¹ * g * x i).prod = 1

/--
Resolved true: the Kourovka Archive answers 3.11 "Yes, there does", citing Goryushkin (Siberian
Math. J. 14 (1973)) and Churkin's example `⟨a, b | (b²)^a = b⁻², (a²)^b = a⁻²⟩`, a torsion-free
two-generator group in which `x² (x²)^a (x²)^b (x²)^(ab) = 1` for every `x`. Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.11 (Yu. M. Gorchakov); resolution:
A. P. Goryushkin, Siberian Math. J. 14 (1973), 146-148; V. A. Churkin (1973), Kourovka Archive,
Problem 3.11: Yes, there does; the Archive's example G = ⟨a, b | (b²)^a = b⁻², (a²)^b = a⁻²⟩ is
torsion-free and satisfies x² (x²)^a (x²)^b (x²)^(ab) = 1 for every x (Churkin),
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted existsFGTorsionFreeGeneralizedPeriodic_holds :
    existsFGTorsionFreeGeneralizedPeriodic

end MathlibExt.GroupTheory.GeneralizedPeriodicTorsionFreeKourovka3Problem11Wanted
