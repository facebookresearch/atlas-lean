/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Free subgroups of the Nottingham group (Kourovka Notebook Problem 12.24)

Kourovka Notebook, Archive of Solved Problems, Problem 12.24 (D. L. Johnson): the automorphisms of
`R⟦x⟧` sending `x` to `x (1 + ∑ᵢ aᵢ xⁱ)` form a group `N(R)`. Does `N(ℤ/pℤ)`, `p` a prime, contain a
copy of the free group `F₂`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.NottinghamGroupFreeSubgroupKourovka12Problem24Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.24 (D. L.
Johnson). UnsolvedMath record UM-00700843 (`KOU-12.24`), dataset ulamai/UnsolvedMath v1.8.0.

`N(R)` is taken literally as a set of ring automorphisms of `R⟦x⟧`: those `φ` with `φ x - x ∈ (x²)`.
For `R = ℤ/pℤ` every ring automorphism is `ℤ/pℤ`-linear and preserves the maximal ideal, so it is
the substitution `x ↦ φ x`. A copy of `F₂` is an injective homomorphism from `FreeGroup (Fin 2)`
with values in `N(ℤ/pℤ)`. The answer covers every prime, so the target is universal in `p`.
-/

/-- A ring automorphism `φ` of `R⟦x⟧` lies in the Nottingham group `N(R)` when it sends `x` to
`x (1 + a₁ x + a₂ x² + ⋯)`, that is, `φ x - x ∈ (x²)`. -/
def IsNottingham {R : Type*} [CommRing R] (φ : RingAut (PowerSeries R)) : Prop :=
  φ PowerSeries.X - PowerSeries.X ∈ Ideal.span {PowerSeries.X ^ 2}

/-- Kourovka 12.24 (D. L. Johnson): for every prime `p`, the Nottingham group `N(ℤ/pℤ)` contains
a free subgroup of rank 2. -/
def nottinghamContainsFreeGroup : Prop :=
  ∀ p : ℕ, p.Prime → ∃ f : FreeGroup (Fin 2) →* RingAut (PowerSeries (ZMod p)),
    Function.Injective f ∧ ∀ g, IsNottingham (f g)

/--
Resolved true: the Kourovka Archive answers 12.24 "Yes, it does" (R. Camina, 1997). Camina embeds
every countably based pro-`p` group in `N(𝔽ₚ)`, for every prime `p`; the free pro-`p` group of rank
2 contains `F₂`, since free groups are residually `p`. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 12.24 (D. L. Johnson); resolution: R. Camina, J. Algebra
196 (1997), no. 1, 101-113, Camina's theorem that every countably based (in particular every
finitely generated) pro-p group embeds in N(F_p); Kourovka Archive, Problem 12.24.
-/
public theorem_wanted nottinghamContainsFreeGroup_holds : nottinghamContainsFreeGroup

end MathlibExt.GroupTheory.NottinghamGroupFreeSubgroupKourovka12Problem24Wanted
