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

/-- **Claim of Scottish Book Problem 112.** The claim that for every group $G$, every
automorphism $\alpha$ of $G$ that sends each element to a conjugate of itself (for each
$x \in G$ there is $g \in G$ with $\alpha(x) = g x g^{-1}$) is inner, that is, there is a
single $g \in G$ with $\alpha(x) = g x g^{-1}$ for all $x \in G$. -/
def ScottishBookProblem112Claim : Prop :=
  ∀ (G : Type*) [Group G] (α : MulAut G),
    (∀ x : G, ∃ g : G, α x = g * x * g⁻¹) →
    ∃ g : G, ∀ x : G, α x = g * x * g⁻¹

/--
**Class-preserving automorphisms need not be inner.** The claim of Scottish Book Problem 112
is false: there are a group $G$ and an automorphism $\alpha$ of $G$ that sends every element
to a conjugate of itself (for each $x \in G$ there is $g \in G$ with $\alpha(x) = g x g^{-1}$)
but is not inner (there is no $g \in G$ with $\alpha(x) = g x g^{-1}$ for all $x \in G$).

Burnside's 1913 example is such a group: for an odd prime $p$, a group of order $p^6$,
isomorphic to the group of $3 \times 3$ lower unitriangular matrices over the field
$\mathbb{F}_{p^2}$, whose group of class-preserving outer automorphisms is nontrivial.

Source: W. Burnside's 1913 example, as summarized in M. K. Yadav,
"Class preserving automorphisms of finite p-groups: A survey",
arXiv:1002.1359, §1 (Burnside constructed a group of order `p ^ 6` with
`Out_c (G) ≠ 1`).
-/
theorem_wanted scottishBook112_refuted : ¬ ScottishBookProblem112Claim

end MathlibExt.GroupTheory.ScottishBook112Wanted
