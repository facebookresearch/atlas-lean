/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Derangements mapping one point to another in primitive groups (Kourovka Notebook Problem 8.75)

Kourovka Notebook, Problem 8.75 (J. G. Thompson), marked solved in the 21st issue: (a known problem)
suppose `G` is a finite primitive permutation group on `Ω` and `α, β` are distinct points of `Ω`.
Does there exist an element `g ∈ G` such that `αg = β` and `g` fixes no point of `Ω`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.GroupAction.Primitive

@[expose] public section

namespace MathlibExt.GroupTheory.PrimitiveDerangementMappingPointKourovka8Problem75Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 8.75 (J. G. Thompson). UnsolvedMath record
UM-00700523 (`KOU-8.75`), dataset ulamai/UnsolvedMath v1.8.0.

A finite primitive permutation group is a subgroup `G` of `Equiv.Perm Ω`, `Ω` finite, acting
primitively (Mathlib's `MulAction.IsPreprimitive`, which includes transitivity). The action is
written on the left (`g • α = β`); since inverses of derangements are derangements and the pair `α,
β` is arbitrary, this is the same question.
-/

/-- Kourovka 8.75 (J. G. Thompson): for every finite primitive permutation group `G ≤ Sym(Ω)` and
distinct points `α, β ∈ Ω` there is `g ∈ G` with `g • α = β` that fixes no point of `Ω`. -/
def primitiveDerangementMapsPoint : Prop :=
  ∀ (Ω : Type) [Finite Ω] (G : Subgroup (Equiv.Perm Ω)), MulAction.IsPreprimitive G Ω →
    ∀ α β : Ω, α ≠ β → ∃ g : G, g • α = β ∧ ∀ ω : Ω, g • ω ≠ ω

/--
Resolved false: Müller constructs a primitive permutation action of the Steinberg triality group
`³D₄(2)` of degree `4064256` with distinct points `α, β` such that no derangement maps `α` to `β`;
the Kourovka Notebook (21st issue) marks 8.75 solved: "Not always". Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Problem 8.75 (J. G. Thompson); resolution: P. Müller, On transitive sets
of derangements in primitive groups, arXiv:2304.08459 (2023), abstract: a primitive permutation
action of the Steinberg triality group ³D₄(2) of degree 4064256 with distinct points α, β such that
no derangement g ∈ ³D₄(2) satisfies α^g = β; this answers Kourovka 8.75 in the negative; the
Kourovka Notebook (21st issue) marks 8.75 solved: "Not always", https://arxiv.org/abs/2304.08459.
-/
public theorem_wanted primitiveDerangementMapsPoint_refuted : ¬ primitiveDerangementMapsPoint

end MathlibExt.GroupTheory.PrimitiveDerangementMappingPointKourovka8Problem75Wanted
