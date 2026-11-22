/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hall subgroups pronormal in their normal closure (Kourovka Notebook Problem 18.32)

Kourovka Notebook, Archive of Solved Problems, Problem 18.32 (E. P. Vdovin, D. O. Revin): is every
Hall subgroup of a finite group pronormal in its normal closure?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace MathlibExt.GroupTheory.HallPronormalNormalClosureKourovka18Problem32Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.32 (E. P.
Vdovin, D. O. Revin). UnsolvedMath record UM-00701461 (`KOU-18.32`), dataset ulamai/UnsolvedMath
v1.8.0.

A Hall subgroup `H` has `|H|` coprime to `|G : H|`. `H` is pronormal in `K` when, for every `g ∈ K`,
`H` and `H^g` are conjugate by an element of `⟨H, H^g⟩`; conjugation is written with `MulAut.conj`,
and since `g` ranges over a subgroup the convention does not matter.
-/

/-- `H` is a Hall subgroup: `|H|` is coprime to `|G : H|`. -/
def IsHallSubgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  (Nat.card H).Coprime H.index

/-- `H` is pronormal in `K`: for every `g ∈ K`, the subgroups `H` and `H^g` are conjugate by an
element of `⟨H, H^g⟩`. -/
def IsPronormalIn {G : Type} [Group G] (H K : Subgroup G) : Prop :=
  ∀ g ∈ K, ∃ x ∈ H ⊔ H.map (MulAut.conj g).toMonoidHom,
    H.map (MulAut.conj x).toMonoidHom = H.map (MulAut.conj g).toMonoidHom

/-- Kourovka 18.32 (E. P. Vdovin, D. O. Revin): every Hall subgroup `H` of a finite group `G` is
pronormal in its normal closure `⟨H^G⟩`. -/
def hallSubgroupPronormalInNormalClosure : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), IsHallSubgroup H →
    IsPronormalIn H (Subgroup.normalClosure (H : Set G))

/--
Resolved false: the Kourovka Archive answers 18.32 "No, not always" (M. N. Nesterov, 2017): some
Hall subgroup of a finite group is not pronormal in its normal closure. Source: E. I. Khukhro and V.
D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.32 (E. P. Vdovin, D. O. Revin);
resolution: M. N. Nesterov, Siberian Math. J. 58 (2017), no. 1, 128-133, Kourovka Archive, Problem
18.32: No, not always, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted hallSubgroupPronormalInNormalClosure_refuted :
    ¬ hallSubgroupPronormalInNormalClosure

end MathlibExt.GroupTheory.HallPronormalNormalClosureKourovka18Problem32Wanted
