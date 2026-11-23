/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Torsion-free groups with a periodic upper central quotient (Kourovka Notebook Problem 2.15)

Kourovka Notebook, Archive of Solved Problems, Problem 2.15 (G. A. Karasëv): does there exist a
torsion-free group such that the factor group by some term of its upper central series is nontrivial
periodic, with a bound on the orders of the elements?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.TorsionFreeUpperCentralQuotientKourovka2Problem15Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.15 (G. A.
Karasëv). UnsolvedMath record UM-00700091 (`KOU-2.15`), dataset ulamai/UnsolvedMath v1.8.0.

The upper central series is Mathlib's `Subgroup.upperCentralSeries`; "nontrivial" means `Zₙ(G) ≠ G`
and the bound means a common exponent `e ≥ 1` of `G / Zₙ(G)` (`gᵉ ∈ Zₙ(G)` for all `g`).
-/

/-- Kourovka 2.15 (G. A. Karasëv): there is a torsion-free group `G` and a term `Zₙ(G)` of its upper
central series such that `G / Zₙ(G)` is nontrivial and periodic of bounded exponent. -/
def existsTorsionFreeUpperCentralQuotientBoundedExponent : Prop :=
  ∃ (G : Type) (_ : Group G) (n : ℕ), (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) ∧
    Subgroup.upperCentralSeries G n ≠ ⊤ ∧
    ∃ e : ℕ, 0 < e ∧ ∀ g : G, g ^ e ∈ Subgroup.upperCentralSeries G n

/--
Resolved true: the Kourovka Archive answers 2.15 "Yes, such groups do exist", citing Adian. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.15 (G. A. Karasëv);
resolution: S. I. Adian, Proc. Steklov Inst. Math. 112 (1971), 61-69, Kourovka Archive, Problem
2.15: Yes, such groups do exist, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted existsTorsionFreeUpperCentralQuotientBoundedExponent_holds :
    existsTorsionFreeUpperCentralQuotientBoundedExponent

end MathlibExt.GroupTheory.TorsionFreeUpperCentralQuotientKourovka2Problem15Wanted
