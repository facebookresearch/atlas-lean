/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Conjugacy separability of wreath products (Kourovka Notebook Problem 2.17)

Kourovka Notebook, Archive of Solved Problems, Problem 2.17 (M. I. Kargapolov): is it true that the
wreath product `A ≀ B` of two conjugacy separable groups is itself conjugacy separable if and only
if either `A` is abelian or `B` is finite?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.WreathProductConjugacySeparableKourovka2Problem17Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.17 (M. I.
Kargapolov). UnsolvedMath record UM-00700093 (`KOU-2.17`), dataset ulamai/UnsolvedMath v1.8.0.

Conjugacy separable: elements whose images are conjugate in every finite quotient `G / N` (`N`
normal of finite index, written as `g x g⁻¹ y⁻¹ ∈ N` for some `g`) are conjugate in `G`. The wreath
product is the restricted (standard) one, the finitely supported part of Mathlib's regular wreath
product `A ≀ᵣ B = (B → A) ⋊ B`, written as a generated subgroup; for finite `B` it is all of `A ≀ᵣ
B`. `IsConjugacySeparable` and `restrictedWreath` are the shared definitions in
`WantedExt/GroupTheory/KourovkaNotebookShared.lean`.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared

/-- Kourovka 2.17 (M. I. Kargapolov): for conjugacy separable groups `A` and `B`, the wreath product
`A ≀ B` is conjugacy separable if and only if `A` is abelian or `B` is finite. -/
def wreathConjugacySeparableIff : Prop :=
  ∀ (A B : Type) [Group A] [Group B], IsConjugacySeparable A → IsConjugacySeparable B →
    (IsConjugacySeparable (restrictedWreath A B) ↔ ((∀ x y : A, x * y = y * x) ∨ Finite B))

/--
Resolved false: the Kourovka Archive answers 2.17 "No", citing Remeslennikov; the Archive does not
say which direction of the equivalence fails, and the refuted statement is the equivalence as posed.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.17 (M. I.
Kargapolov); resolution: V. N. Remeslennikov, Groups that are residually finite with respect to
conjugacy, Siberian Math. J. 12 (1971), 783-792, Kourovka Archive, Problem 2.17: No,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted wreathConjugacySeparableIff_refuted : ¬ wreathConjugacySeparableIff

end MathlibExt.GroupTheory.WreathProductConjugacySeparableKourovka2Problem17Wanted
