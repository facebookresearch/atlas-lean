/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ends of uncountable locally finite groups (Kourovka Notebook Problem 5.61)

Kourovka Notebook, Archive of Solved Problems, Problem 5.61 (B. Hartley): (Well-known problem.) Does
an arbitrary uncountable locally finite group have only one end?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Countable.Defs
public import WantedExt.GroupTheory.LocallyFiniteSimpleFiniteRankKourovka1Problem23Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.UncountableLocallyFiniteOneEndKourovka5Problem61Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.61 (B.
Hartley). UnsolvedMath record UM-00700340 (`KOU-5.61`), dataset ulamai/UnsolvedMath v1.8.0.

Locally finite is `IsLocallyFinite` of the Kourovka 1.23 module (every finitely generated subgroup
is finite). Ends of an arbitrary group are counted with almost invariant subsets (Specker,
Stallings): `e(G)` is the dimension over `𝔽₂` of the `G`-invariant part of `P(G) ⧸ F(G)` (all
subsets modulo finite subsets, under right translation), so an infinite group has exactly one end
when every almost invariant subset `A` (`A ∆ A g` finite for every `g`) is finite or cofinite. The
target uses `A g⁻¹ = (· * g) ⁻¹' A`, which ranges over the same translates.
-/

open MathlibExt.GroupTheory.LocallyFiniteSimpleFiniteRankKourovka1Problem23Wanted (IsLocallyFinite)

/-- Kourovka 5.61 (B. Hartley): every uncountable locally finite group has exactly one end: every
almost invariant subset `A` (`A ∆ A g⁻¹` finite for every `g`) is finite or has finite
complement. -/
def uncountableLocallyFiniteOneEnd : Prop :=
  ∀ (G : Type) [Group G], IsLocallyFinite G → Uncountable G →
    ∀ A : Set G, (∀ g : G, (symmDiff A ((· * g) ⁻¹' A)).Finite) → A.Finite ∨ Aᶜ.Finite

/--
Resolved true: the Kourovka Archive answers 5.61 "Yes, it does", citing Holt (1981), Uncountable
locally finite groups have one end: every uncountable locally finite group has exactly one end, that
is, every almost invariant subset is finite or cofinite. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 5.61 (B. Hartley); resolution: D. F. Holt, Uncountable
locally finite groups have one end, Bull. London Math. Soc. 13 (1981), 557-560, Kourovka Archive,
Problem 5.61: Yes, it does (Holt), https://doi.org/10.1112/blms/13.6.557.
-/
public theorem_wanted uncountableLocallyFiniteOneEnd_holds : uncountableLocallyFiniteOneEnd

end MathlibExt.GroupTheory.UncountableLocallyFiniteOneEndKourovka5Problem61Wanted
