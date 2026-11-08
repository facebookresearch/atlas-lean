/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Automorphisms of order `p` with few fixed points (Kourovka Notebook Problem 10.68)

Kourovka Notebook, Archive of Solved Problems, Problem 10.68 (E. I. Khukhro): suppose that a finite
`p`-group `G` admits an automorphism of order `p` with exactly `p ^ m` fixed points. Is it true that
`G` has a subgroup whose index is bounded by a function of `p` and `m` and whose nilpotency class is
bounded by a function of `m` only?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.AutomorphismFewFixedPointsPGroupKourovka10Problem68Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.68 (E. I.
Khukhro). UnsolvedMath record UM-00700683 (`KOU-10.68`), dataset ulamai/UnsolvedMath v1.8.0.

The bounding functions are quantified before `p`, `m` and `G`. Nilpotency class at most `c` for a
subgroup `H` is `H.lowerCentralSeries c = ⊥` (`γ_{c+1}(H) = 1`); fixed points are counted with
`Nat.card`.
-/

/-- Kourovka 10.68 (E. I. Khukhro): there are functions `f(p, m)` and `g(m)` such that every finite
`p`-group admitting an automorphism of order `p` with exactly `p ^ m` fixed points has a subgroup of
index at most `f(p, m)` and nilpotency class at most `g(m)` (`γ_{g(m)+1} = 1`). -/
def boundedIndexBoundedClassSubgroup : Prop :=
  ∃ (f : ℕ → ℕ → ℕ) (g : ℕ → ℕ), ∀ p : ℕ, p.Prime → ∀ (m : ℕ) (G : Type) [Group G] [Finite G],
    IsPGroup p G → ∀ φ : MulAut G, orderOf φ = p → Nat.card {x : G // φ x = x} = p ^ m →
      ∃ H : Subgroup G, H.index ≤ f p m ∧ H.lowerCentralSeries (g m) = ⊥

/--
Resolved true: the Kourovka Archive answers "Yes, it is", citing Medvedev (1999): such a `p`-group
has a subgroup of `(p, m)`-bounded index and `m`-bounded nilpotency class (the case `m = 1` follows
from the theory of `p`-groups of maximal class). Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 10.68 (E. I. Khukhro); resolution: Yu. Medvedev, J. London Math.
Soc. (2) 59, no. 3 (1999), 787-798, Kourovka Archive, Problem 10.68 ("Yes, it is").
-/
public theorem_wanted boundedIndexBoundedClassSubgroup_holds : boundedIndexBoundedClassSubgroup

end MathlibExt.GroupTheory.AutomorphismFewFixedPointsPGroupKourovka10Problem68Wanted
