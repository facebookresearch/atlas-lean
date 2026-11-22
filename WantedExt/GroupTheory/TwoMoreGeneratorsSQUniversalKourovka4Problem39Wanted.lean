/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups with two more generators than relators are SQ-universal (Kourovka Notebook Problem 4.39)

Kourovka Notebook, Archive of Solved Problems, Problem 4.39 (A. M. Macbeath, P. M. Neumann): a
countable group `U` is said to be SQ-universal if every countable group is isomorphic to a subgroup
of a quotient group of `U`. Let `G` be a group that has a presentation with `r ≥ 2` generators and
at most `r - 2` defining relations. Is `G` SQ-universal?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import WantedExt.GroupTheory.SQUniversalShared

@[expose] public section

namespace MathlibExt.GroupTheory.TwoMoreGeneratorsSQUniversalKourovka4Problem39Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.39 (A. M.
Macbeath, P. M. Neumann). UnsolvedMath record UM-00700247 (`KOU-4.39`), dataset ulamai/UnsolvedMath
v1.8.0.

The presentation is `⟨x₁, …, x_r | R₁, …, R_m⟩` with `m + 2 ≤ r` (which forces `r ≥ 2`).
SQ-universality is the batch's shared `SQUniversalShared.IsSQUniversal`: every countable group
embeds in a quotient, a quotient being a surjective image.
-/

open MathlibExt.GroupTheory.SQUniversalShared

/-- Kourovka 4.39 (A. M. Macbeath, P. M. Neumann): every group with a presentation on `r ≥ 2`
generators and at most `r - 2` defining relations, `⟨x₁, …, x_r | R₁, …, R_m⟩` with `m + 2 ≤ r`,
is SQ-universal. -/
def twoMoreGeneratorsThanRelatorsSQUniversal : Prop :=
  ∀ (r m : ℕ) (R : Fin m → FreeGroup (Fin r)), m + 2 ≤ r →
    IsSQUniversal (FreeGroup (Fin r) ⧸ Subgroup.normalClosure (Set.range R))

/--
Resolved true: Baumslag and Pride prove that a group with a presentation having at least two more
generators than relators is SQ-universal; the Kourovka Archive answers 4.39 "Yes, it is". Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.39 (A. M. Macbeath, P. M.
Neumann); resolution: B. Baumslag and S. J. Pride, Groups with two more generators than relators, J.
London Math. Soc. (2) 17 (1978), 425-426, Kourovka Archive of Solved Problems, Problem 4.39: Yes, it
is, https://doi.org/10.1112/jlms/s2-17.3.425.
-/
public theorem_wanted twoMoreGeneratorsThanRelatorsSQUniversal_holds :
    twoMoreGeneratorsThanRelatorsSQUniversal

end MathlibExt.GroupTheory.TwoMoreGeneratorsSQUniversalKourovka4Problem39Wanted
