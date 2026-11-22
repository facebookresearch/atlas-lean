/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Subgroups of `ℤ^ω` with free dual of uncountable rank (Kourovka Notebook Problem 17.24)

Kourovka Notebook, Archive of Solved Problems, Problem 17.24 (G. M. Bergman): (A. Blass, J. Irwin,
G. Schlitt). Does `ℤ^ω` have a subgroup whose dual is free of uncountable rank?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.BaerSpeckerSubgroupDualFreeKourovka17Problem24Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.24 (G. M.
Bergman). UnsolvedMath record UM-00701326 (`KOU-17.24`), dataset ulamai/UnsolvedMath v1.8.0.

`ℤ^ω` is `ℕ → ℤ`, the dual of `H` is `Hom(H, ℤ) = H →+ ℤ` as a `ℤ`-module, free means `Module.Free
ℤ`, and uncountable rank means `ℵ₀ < Module.rank`.
-/

/-- Kourovka 17.24 (G. M. Bergman; A. Blass, J. Irwin, G. Schlitt): the Baer-Specker group `ℤ^ω`
has a subgroup `H` whose dual `Hom(H, ℤ)` is a free abelian group of uncountable rank. -/
def baerSpeckerSubgroupDualFreeUncountable : Prop :=
  ∃ H : AddSubgroup (ℕ → ℤ), Module.Free ℤ (H →+ ℤ) ∧ Cardinal.aleph0 < Module.rank ℤ (H →+ ℤ)

/--
Resolved true: Bergman constructs a subgroup `H` of `ℤ^ω` whose dual `Hom(H, ℤ)` is a free abelian
group of rank `2^ℵ₀`, which is uncountable; the Kourovka Archive answers 17.24 "Yes, it does".
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.24 (G. M.
Bergman); resolution: G. M. Bergman, More Abelian groups with free duals, Portugaliae Math. 69
(2012), 69-84 (arXiv:1104.3827), abstract (a subgroup of ℤ^ω whose dual Hom(G, ℤ) is free abelian of
rank 2^ℵ₀); Kourovka Archive, Problem 17.24 (Yes, it does), https://arxiv.org/abs/1104.3827.
-/
public theorem_wanted baerSpeckerSubgroupDualFreeUncountable_holds :
    baerSpeckerSubgroupDualFreeUncountable

end MathlibExt.GroupTheory.BaerSpeckerSubgroupDualFreeKourovka17Problem24Wanted
