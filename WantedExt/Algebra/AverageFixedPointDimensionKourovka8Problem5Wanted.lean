/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Average dimension of fixed point spaces (Kourovka Notebook Problem 8.5)

Kourovka Notebook, Archive of Solved Problems, Problem 8.5 (M. R. Vaughan-Lee): prove that if `X` is
a finite group, `F` is any field, and `M` is a non-trivial irreducible `FX`-module then `(1 / |X|)
∑_{x ∈ X} dim fix(x) ≤ (1 / 2) dim M`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Irreducible

@[expose] public section

namespace MathlibExt.Algebra.AverageFixedPointDimensionKourovka8Problem5Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.5 (M. R.
Vaughan-Lee). UnsolvedMath record UM-00700457 (`KOU-8.5`), dataset ulamai/UnsolvedMath v1.8.0.

`M` is finite dimensional (as for an irreducible module of a finite group) and given by a
`Representation F X M`. Irreducible is Mathlib's `Representation.IsIrreducible` (`M ≠ 0` with no
invariant subspaces but `0` and `M`); non-trivial means some element acts non-trivially. `fix(x)`
is the kernel of `ρ x - 1`. The bound is the Archive's strengthening `(1 / p) dim M`, `p` the least
prime divisor of `|X|` (`Nat.minFac`), which implies the printed `1 / 2`.
-/

/-- Kourovka 8.5 (M. R. Vaughan-Lee), in the strengthened form of the Archive: for a finite group
`X`, a field `F` and a non-trivial irreducible finite-dimensional representation `ρ` of `X` on `M`,
the average over `x ∈ X` of the dimension of the fixed space of `x` is at most `dim M / p`, where
`p` is the least prime divisor of `|X|` (so at most `dim M / 2`). -/
def averageFixedPointDimensionBound : Prop :=
  ∀ (X : Type) [Group X] [Fintype X] (F : Type) [Field F] (M : Type) [AddCommGroup M]
    [Module F M] [FiniteDimensional F M] (ρ : Representation F X M),
    ρ.IsIrreducible →
    (∃ x : X, ρ x ≠ 1) →
    (∑ x : X, (Module.finrank F (LinearMap.ker (ρ x - 1)) : ℚ)) / Fintype.card X ≤
      (Module.finrank F M : ℚ) / (Fintype.card X).minFac

/--
Resolved true: the Kourovka Archive records 8.5 as proved, even with `1 / p` in place of `1 / 2`,
citing Guralnick and Maróti (2011), who prove that for a finite group `G`, a field `F` and a finite
dimensional `FG`-module `V` without trivial composition factors the average dimension of the fixed
point spaces of the elements of `G` is at most `(1 / p) dim V`; a non-trivial irreducible module has
no trivial composition factor. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 8.5 (M. R. Vaughan-Lee); resolution: R. M. Guralnick and A. Maróti, Average
dimension of fixed point spaces with applications, Adv. Math. 226 (2011), 298-308, Kourovka Archive,
Problem 8.5: Proved, even with ≤ (1/p) dim M; paper, Theorem 1.1 (arXiv:1001.3836): for a finite
group G, a field F and a finite dimensional FG-module V with no trivial composition factor, the
average dimension of the fixed point spaces is at most (1/p) dim V,
https://www.sciencedirect.com/science/article/pii/S0001870810002471.
-/
public theorem_wanted averageFixedPointDimensionBound_holds : averageFixedPointDimensionBound

end MathlibExt.Algebra.AverageFixedPointDimensionKourovka8Problem5Wanted
