/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# `p`-separability of isolated subgroups of free groups (Kourovka Notebook Problem 15.60)

Kourovka Notebook, Archive of Solved Problems, Problem 15.60 (D. I. Moldavanskiĭ): is it true that
any finitely generated `p'`-isolated subgroup of a free group is separable in the class of finite
`p`-groups? (This is true for cyclic subgroups.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.IsolatedSubgroupPSeparableKourovka15Problem60Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.60 (D. I.
Moldavanskiĭ). UnsolvedMath record UM-00701148 (`KOU-15.60`), dataset ulamai/UnsolvedMath v1.8.0.

`H` is `p'`-isolated if `xⁿ ∈ H` with `n > 0` coprime to `p` implies `x ∈ H`; `H` is separable in
finite `p`-groups if every `x ∉ H` stays outside the image of `H` under some homomorphism to a
finite `p`-group. The source asks the question for a prime `p`. The target is stated for some prime
`p` and all free groups `FreeGroup α` (the strongest true form, existential when refuted, as in
WantedExt/Sources/UnsolvedMath.md), so its refutation asserts failure for every prime: stronger than
the source's negative answer, which needs one prime, and what Bardakov proves (his isolated subgroup
is `p'`-isolated for every `p` and is not separable in the class of nilpotent groups, which contains
the finite `p`-groups).
-/

/-- `H` is `p'`-isolated: `xⁿ ∈ H` with `n > 0` not divisible by `p` implies `x ∈ H`. -/
def IsPPrimeIsolated (p : ℕ) {F : Type*} [Group F] (H : Subgroup F) : Prop :=
  ∀ (x : F) (n : ℕ), 0 < n → ¬ p ∣ n → x ^ n ∈ H → x ∈ H

/-- `H` is separable in the class of finite `p`-groups: every element outside `H` stays outside
the image of `H` under some homomorphism to a finite `p`-group. -/
def IsPSeparable (p : ℕ) {F : Type*} [Group F] (H : Subgroup F) : Prop :=
  ∀ x : F, x ∉ H → ∃ (Q : Type) (_ : Group Q) (_ : Finite Q), IsPGroup p Q ∧
    ∃ f : F →* Q, f x ∉ H.map f

/-- Kourovka 15.60 (D. I. Moldavanskiĭ), for some prime `p`: every finitely generated `p'`-isolated
subgroup of a free group is separable in the class of finite `p`-groups. -/
def isolatedFGSubgroupsPSeparable : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∀ (α : Type) (H : Subgroup (FreeGroup α)), H.FG → IsPPrimeIsolated p H →
    IsPSeparable p H

/--
Resolved false: Bardakov proved that every nonabelian free group has a finitely generated isolated
subgroup (`xⁿ ∈ H` with `n ≠ 0` implies `x ∈ H`) that is not separable in the class of nilpotent
groups; it is `p'`-isolated for every prime `p`, and finite `p`-groups are nilpotent. The Kourovka
Archive answers 15.60 "No, it is not". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 15.60 (D. I. Moldavanskiĭ); resolution: V. G. Bardakov, On D. I.
Moldavanskii's question about p-separable subgroups of a free group, Siberian Math. J. 45 (2004),
no. 3, 416-419, arXiv:math/0404292, abstract (every nonabelian free group has a finitely generated
isolated subgroup that is not separable in the class of nilpotent groups); Kourovka Archive, Problem
15.60 (answer: No, it is not), https://arxiv.org/abs/math/0404292.
-/
public theorem_wanted isolatedFGSubgroupsPSeparable_refuted : ¬ isolatedFGSubgroupsPSeparable

end MathlibExt.GroupTheory.IsolatedSubgroupPSeparableKourovka15Problem60Wanted
