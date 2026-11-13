/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely separable subgroups of free soluble groups (Kourovka Notebook Problem 2.19)

Kourovka Notebook, Archive of Solved Problems, Problem 2.19 (M. I. Kargapolov): are finitely
generated subgroups of a free soluble group finitely separable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import WantedExt.GroupTheory.FreeSolubleNormalClosureConjugacyKourovka1Problem89Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.FreeSolubleSubgroupSeparableKourovka2Problem19Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.19 (M. I.
Kargapolov). UnsolvedMath record UM-00700095 (`KOU-2.19`), dataset ulamai/UnsolvedMath v1.8.0.

Free soluble groups are `F_r / F_r^{(l)}` of finite rank `r` and derived length `l`. A subgroup `H`
is finitely separable when it is the intersection of the subgroups of finite index containing it
(every element outside `H` is outside one of them). The refutation is existential in `r` and `l`.
`FreeSolubleGroup` is that of the Kourovka 1.89 entry, reused here.
-/

open MathlibExt.GroupTheory.FreeSolubleNormalClosureConjugacyKourovka1Problem89Wanted
  (FreeSolubleGroup)

/-- `H` is finitely separable: every element outside `H` lies outside some subgroup of finite index
containing `H` (so `H` is an intersection of subgroups of finite index). -/
def IsFinitelySeparable {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∀ g ∉ H, ∃ K : Subgroup G, H ≤ K ∧ K.FiniteIndex ∧ g ∉ K

/-- Kourovka 2.19 (M. I. Kargapolov): every finitely generated subgroup of a free soluble group
(of finite rank `r` and derived length `l`) is finitely separable. -/
def freeSolubleFGSubgroupsSeparable : Prop :=
  ∀ (r l : ℕ) (H : Subgroup (FreeSolubleGroup r l)), H.FG → IsFinitelySeparable H

/--
Resolved false: the Kourovka Archive answers 2.19 "Not always", citing Agalakov: some free soluble
group has a finitely generated subgroup that is not finitely separable. Source: E. I. Khukhro and V.
D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.19 (M. I. Kargapolov); resolution:
S. A. Agalakov, Finite separability of groups and Lie algebras, Algebra and Logic 22 (1983),
261-268, Kourovka Archive, Problem 2.19: Not always, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted freeSolubleFGSubgroupsSeparable_refuted : ¬ freeSolubleFGSubgroupsSeparable

end MathlibExt.GroupTheory.FreeSolubleSubgroupSeparableKourovka2Problem19Wanted
