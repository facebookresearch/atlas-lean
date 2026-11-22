/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Residual finiteness of one-relator groups with torsion (Kourovka Notebook Problem 8.68)

Kourovka Notebook, Archive of Solved Problems, Problem 8.68 (C. Y. Tang): let `G = ⟨a, b | r = 1⟩`
where `r` is a cyclically reduced word that is not a proper power of any word in `a, b`. If `G` is
residually finite, is `G_t = ⟨a, b | rᵗ = 1⟩`, `t > 1`, residually finite?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.ResiduallyFinite

@[expose] public section

namespace MathlibExt.GroupTheory.OneRelatorPowerResiduallyFiniteKourovka8Problem68Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.68 (C. Y.
Tang). UnsolvedMath record UM-00700516 (`KOU-8.68`), dataset ulamai/UnsolvedMath v1.8.0.

`r` is an element of the free group on `a = of 0`, `b = of 1`; cyclically reduced is Mathlib's
`FreeGroup.IsCyclicallyReduced` of its reduced word; a proper power is `sᵏ` with `k ≥ 2`; residually
finite is `Group.ResiduallyFinite`.
-/

/-- Kourovka 8.68 (C. Y. Tang): if `r` is a cyclically reduced word in `a, b` that is not a proper
power and `G = ⟨a, b | r⟩` is residually finite, then `G_t = ⟨a, b | rᵗ⟩` is residually finite for
every `t > 1`. -/
def oneRelatorPowerResiduallyFinite : Prop :=
  ∀ r : FreeGroup (Fin 2), FreeGroup.IsCyclicallyReduced r.toWord →
    (¬ ∃ (s : FreeGroup (Fin 2)) (k : ℕ), 2 ≤ k ∧ r = s ^ k) →
    Group.ResiduallyFinite (PresentedGroup ({r} : Set (FreeGroup (Fin 2)))) →
    ∀ t : ℕ, 1 < t → Group.ResiduallyFinite (PresentedGroup ({r ^ t} : Set (FreeGroup (Fin 2))))

/--
Resolved true: the Kourovka Archive answers 8.68 "Yes, it is", citing Wise, The structure of groups
with a quasiconvex hierarchy (2021): one-relator groups with torsion are virtually compact special,
hence residually finite (Baumslag's conjecture; Ch. 18 of the 2011 preprint, as cited by Minasyan
and Zalesskii, arXiv:1211.0488, §1-2), and `⟨a, b | rᵗ⟩` with `t > 1` and `r ≠ 1` is a one-relator
group with torsion. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 8.68 (C. Y. Tang); resolution: D. T. Wise, The structure of groups with a quasiconvex
hierarchy, Annals of Mathematics Studies 209, Princeton University Press, 2021, Kourovka Archive,
Problem 8.68: Yes, it is (Wise); book, applications to one-relator groups with torsion (Ch. 18 of
the 2011 preprint, cited in Minasyan and Zalesskii, arXiv:1211.0488, §1-2),
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted oneRelatorPowerResiduallyFinite_holds : oneRelatorPowerResiduallyFinite

end MathlibExt.GroupTheory.OneRelatorPowerResiduallyFiniteKourovka8Problem68Wanted
