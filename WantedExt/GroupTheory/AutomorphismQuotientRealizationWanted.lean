/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Automorphism quotient realization
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Rat.Defs
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.GroupTheory.AutomorphismQuotientRealizationWanted

/-! Source record `KOU-21.97__2606`. -/

/-- Kourovka Notebook Problem 21.97 [KOU-21.97]: is it true that for every
positive rational `r` there exists a finite group `G` with
`|Aut G| / |G| = r`? -/
def conjecture : Prop :=
  ∀ r : ℚ, 0 < r → ∃ (G : Type) (_hg : Group G) (_hf : Fintype G) (_hd : DecidableEq G),
    letI := _hg; letI := _hf; letI := _hd;
    (Fintype.card (G ≃* G) : ℚ) / (Fintype.card G : ℚ) = r

/--
Resolved true: Answered affirmatively: S. Sureaux, Automorphism ratios of finite groups
(preprint, 2026, Kourovka Notebook site), Theorem 1.1(a): for every positive rational r there is
a finite group G with |Aut(G)|/|G| = r. The Kourovka Notebook (arXiv:1401.0300v49) marks Problem
21.97 solved with this reference. Source: S. Sureaux, Automorphism ratios of finite groups
(preprint, 2026, Kourovka Notebook site),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/08/21.97-solution.pdf; E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (20 October 2026), Problem 21.97, https://arxiv.org/abs/1401.0300v49.
Moved from `OpenConjectures/GroupTheory/AutomorphismQuotientRealization`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GroupTheory.AutomorphismQuotientRealizationWanted
