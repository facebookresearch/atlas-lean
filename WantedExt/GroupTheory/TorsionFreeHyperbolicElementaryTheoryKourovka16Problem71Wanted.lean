/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Elementary theory of torsion-free hyperbolic groups (Kourovka Notebook Problem 16.71)

Kourovka Notebook, Archive of Solved Problems, Problem 16.71 (A. G. Myasnikov, O. G. Kharlampovich):
is the elementary theory of a torsion-free hyperbolic group decidable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.OrderOfElement
public import MathlibExt.GroupTheory.HyperbolicGroup
public import WantedExt.GroupTheory.PrenexSentenceShared

@[expose] public section

namespace MathlibExt.GroupTheory.TorsionFreeHyperbolicElementaryTheoryKourovka16Problem71Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.71 (A. G.
Myasnikov, O. G. Kharlampovich). UnsolvedMath record UM-00701263 (`KOU-16.71`), dataset
ulamai/UnsolvedMath v1.8.0.

Sentences of the language of groups are coded in prenex form (`PrenexSentence` of
`PrenexSentenceShared`), a quantifier prefix over `x₀, x₁, …` followed by a conjunctive normal form
over literals `w = 1` and `w ≠ 1`, so that codes form a `Primcodable` type; every first-order
sentence is effectively equivalent to such a code and conversely. Hyperbolic is `Group.IsHyperbolic`
(`MathlibExt.GroupTheory.HyperbolicGroup`: some finite generating set has a Gromov-hyperbolic word
metric) and torsion-free means no nontrivial element of finite order. Decidability is per group.
-/

open MathlibExt.GroupTheory.PrenexSentenceShared

/-- **Decidability of the elementary theory of torsion-free hyperbolic groups.** The proposition
stating Kourovka Problem 16.71 (A. G. Myasnikov, O. G. Kharlampovich): for every torsion-free
word-hyperbolic group $G$ (every element $g \ne 1$ of $G$ has infinite order), the set of prenex
sentences of the language of groups that hold in $G$ is computable, that is, some algorithm
decides for each prenex sentence whether it holds in $G$. -/
def torsionFreeHyperbolicTheoryDecidable : Prop :=
  ∀ (G : Type) [Group G], Group.IsHyperbolic G → (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) →
    ComputablePred fun s : PrenexSentence => s.HoldsIn G

/--
**Torsion-free hyperbolic groups have decidable elementary theory.** For every torsion-free
word-hyperbolic group $G$ (every element $g \ne 1$ of $G$ has infinite order), the set of prenex
sentences of the language of groups that hold in $G$ is computable, that is, some algorithm decides
for each prenex sentence whether it holds in $G$.

This answers Kourovka Problem 16.71 affirmatively (the Kourovka Archive answers "Yes, it is"); it
is Theorem 3 of Kharlampovich and Myasnikov.

Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.71 (A. G. Myasnikov,
O. G. Kharlampovich); resolution: O. Kharlampovich and A. Myasnikov, Decidability of the elementary
theory of a torsion-free hyperbolic group, arXiv:1303.0760, Theorem 3 (the elementary theory of a
torsion-free hyperbolic group is decidable); Kourovka Archive, Problem 16.71 (Yes, it is),
https://arxiv.org/abs/1303.0760.
-/
public theorem_wanted torsionFreeHyperbolicTheoryDecidable_holds :
    torsionFreeHyperbolicTheoryDecidable

end MathlibExt.GroupTheory.TorsionFreeHyperbolicElementaryTheoryKourovka16Problem71Wanted
