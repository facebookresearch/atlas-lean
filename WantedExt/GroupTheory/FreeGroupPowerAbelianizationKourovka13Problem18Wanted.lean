/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Abelianized Cartesian powers of free groups (Kourovka Notebook Problem 13.18)

Kourovka Notebook, Archive of Solved Problems, Problem 13.18 (A. M. Gaglione, D. Spellman): let `F`
be a finitely generated non-abelian free group and `G` the Cartesian (unrestricted) product of
countably many copies of `F`. Must `G/G'` be torsion-free?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupPowerAbelianizationKourovka13Problem18Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.18 (A. M.
Gaglione, D. Spellman). UnsolvedMath record UM-00700936 (`KOU-13.18`), dataset ulamai/UnsolvedMath
v1.8.0.

The Cartesian product of countably many copies of `F` is `ℕ → F` with pointwise multiplication;
torsion-free means that no nontrivial element has finite order. The question is posed for every
finitely generated non-abelian free group, i.e. every rank `n ≥ 2`.
-/

/-- **Torsion-freeness of abelianized Cartesian powers of free groups (Kourovka 13.18).** The
statement, posed by A. M. Gaglione and D. Spellman, that for every integer $n \ge 2$ the
abelianization of the unrestricted (Cartesian) product $F_n^{\mathbb{N}}$ of countably many copies
of the free group $F_n$ of rank $n$ is torsion-free: none of its nontrivial elements has finite
order. -/
def cartesianPowerAbelianizationTorsionFree : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ g : Abelianization (ℕ → FreeGroup (Fin n)), g ≠ 1 → ¬ IsOfFinOrder g

/--
**Abelianized Cartesian powers of free groups can have torsion.** For some integer $n \ge 2$, the
abelianization of the unrestricted (Cartesian) product $F_n^{\mathbb{N}}$ of countably many copies
of the free group $F_n$ of rank $n$ contains a nontrivial element of finite order. That is, the
torsion-freeness asked for in Kourovka Problem 13.18 fails.

The Kourovka Archive answers 13.18 "No, it may contain elements of order 2" (O. Kharlampovich and
A. Myasnikov, 2001).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 13.18 (A. M. Gaglione, D. Spellman); resolution: O. Kharlampovich and A.
Myasnikov, in: Knots, braids, and mapping class groups (New York, 1998), Amer. Math. Soc., 2001,
77-83, Kourovka Archive, Problem 13.18: No, it may contain elements of order 2.
-/
public theorem_wanted cartesianPowerAbelianizationTorsionFree_refuted :
    ¬ cartesianPowerAbelianizationTorsionFree

end MathlibExt.GroupTheory.FreeGroupPowerAbelianizationKourovka13Problem18Wanted
