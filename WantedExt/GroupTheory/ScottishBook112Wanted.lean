/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.End

@[expose] public section

namespace MathlibExt.GroupTheory.ScottishBook112Wanted

/-- Scottish Book 112: every automorphism of a group that sends
every element to a conjugate of itself is an inner automorphism. -/
def ScottishBookProblem112Claim : Prop :=
  ∀ (G : Type*) [Group G] (α : MulAut G),
    (∀ x : G, ∃ g : G, α x = g * x * g⁻¹) →
    ∃ g : G, ∀ x : G, α x = g * x * g⁻¹

/--
Scottish Book 112 is false as stated: not every class-preserving
automorphism is inner. Burnside's classical 1913 example is a finite
group `G` of order `p ^ 6` (for an odd prime `p`), isomorphic to the
group of `3 × 3` lower unitriangular matrices over the field `𝔽_{p ^ 2}`,
for which the group of class-preserving outer automorphisms is
nontrivial: `Out_c (G) ≠ 1`. Such an outer class-preserving
automorphism sends every element to a conjugate of itself but is not
conjugation by any single element of `G`, refuting the claim.
Source: W. Burnside's 1913 example, as summarized in M. K. Yadav,
"Class preserving automorphisms of finite p-groups: A survey",
arXiv:1002.1359, §1 (Burnside constructed a group of order `p ^ 6` with
`Out_c (G) ≠ 1`).
-/
theorem_wanted scottishBook112_refuted : ¬ ScottishBookProblem112Claim

end MathlibExt.GroupTheory.ScottishBook112Wanted
