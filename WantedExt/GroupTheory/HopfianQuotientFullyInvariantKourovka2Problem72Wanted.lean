/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hopfian quotients by fully invariant subgroups (Kourovka Notebook Problem 2.72)

Kourovka Notebook, Archive of Solved Problems, Problem 2.72 (D. M. Smirnov; question of G.
Baumslag): suppose that `F` is a finitely generated free group, `N` its normal subgroup and `V` a
fully invariant subgroup of `N`. Is `F/V` necessarily Hopfian if `F/N` is Hopfian?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.HopfianQuotientFullyInvariantKourovka2Problem72Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.72 (D. M.
Smirnov; question of G. Baumslag). UnsolvedMath record UM-00700142 (`KOU-2.72`), dataset
ulamai/UnsolvedMath v1.8.0.

`F = FreeGroup (Fin n)`; `V` fully invariant in `N` means `φ(V) ⊆ V` for every endomorphism `φ` of
`N`, which makes `V` characteristic in `N` and so normal in `F`; normality of `V` is listed as a
hypothesis so that `F/V` is a group, which changes nothing. Hopfian means every surjective
endomorphism is injective.
-/

/-- A group is Hopfian: every surjective endomorphism is injective. -/
def IsHopfian (G : Type) [Group G] : Prop :=
  ∀ f : G →* G, Function.Surjective f → Function.Injective f

/-- Kourovka 2.72 (G. Baumslag; D. M. Smirnov): let `F` be a free group of finite rank, `N` a
normal subgroup of `F` and `V ≤ N` a subgroup that is fully invariant in `N` (mapped into itself
by every endomorphism of `N`; such a `V` is normal in `F`). If `F/N` is Hopfian, then so is
`F/V`. -/
def hopfianQuotientByFullyInvariant : Prop :=
  ∀ (n : ℕ) (N : Subgroup (FreeGroup (Fin n))) (_ : N.Normal) (V : Subgroup (FreeGroup (Fin n)))
    (_ : V.Normal) (hVN : V ≤ N),
    (∀ φ : N →* N, ∀ v (hv : v ∈ V), ((φ ⟨v, hVN hv⟩ : N) : FreeGroup (Fin n)) ∈ V) →
    IsHopfian (FreeGroup (Fin n) ⧸ N) → IsHopfian (FreeGroup (Fin n) ⧸ V)

/--
Resolved false: Ivanov and Storozhev (2005) construct a nontrivial variety of groups all of whose
noncyclic free groups are non-Hopfian; with `N = F` of rank at least `2` (so `F/N` is trivial, hence
Hopfian) and `V` the verbal subgroup of that variety (fully invariant in `F`), `F/V` is not Hopfian.
The Kourovka Archive answers 2.72 "No, not necessarily". Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 2.72 (D. M. Smirnov; question of G. Baumslag);
resolution: S. V. Ivanov and A. M. Storozhev, Non-Hopfian relatively free groups, Geom. Dedicata 114
(2005), 209-228, Abstract: a nontrivial variety of groups all of whose noncyclic free groups are
non-Hopfian (so N = F, F/N trivial and V the verbal subgroup); Kourovka Archive, Problem 2.72: No,
not necessarily, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted hopfianQuotientByFullyInvariant_refuted : ¬ hopfianQuotientByFullyInvariant

end MathlibExt.GroupTheory.HopfianQuotientFullyInvariantKourovka2Problem72Wanted
