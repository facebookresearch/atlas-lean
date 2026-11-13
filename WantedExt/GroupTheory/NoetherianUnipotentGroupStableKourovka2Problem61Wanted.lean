/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Noetherian groups of unipotent automorphisms (Kourovka Notebook Problem 2.61)

Kourovka Notebook, Archive of Solved Problems, Problem 2.61 (B. I. Plotkin): let `Γ` be a Noetherian
group of automorphisms of a vector space `G` such that every element of `Γ` is unipotent. Is `Γ`
necessarily a stable group of automorphisms?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import WantedExt.GroupTheory.StableSeriesShared

@[expose] public section

namespace MathlibExt.GroupTheory.NoetherianUnipotentGroupStableKourovka2Problem61Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.61 (B. I.
Plotkin). UnsolvedMath record UM-00700131 (`KOU-2.61`), dataset ulamai/UnsolvedMath v1.8.0.

A set of linear automorphisms is stable when some finite chain of subspaces `0 = W₀ ≤ W₁ ≤ ⋯ ≤ W_m =
V` satisfies `g w - w ∈ W_i` for every element `g` of the set and every `w ∈ W_{i+1}` (a chain of
additive subgroups with this property spans such a chain of subspaces, so nothing depends on using
subspaces). Groups of automorphisms of `V` are subgroups of the group `V ≃ₗ[K] V` of linear
automorphisms. `HasStableSeries` is shared with the other stable-series entries in
`WantedExt.GroupTheory.StableSeriesShared`. Noetherian means that every subgroup of `Γ` is finitely
generated (the maximal condition on subgroups); `g` is unipotent when `(g - 1)ᵐ = 0` for some `m`.
The field is arbitrary.
-/

open MathlibExt.GroupTheory.StableSeriesShared

/-- Kourovka 2.61 (B. I. Plotkin): a Noetherian group `Γ` of automorphisms of a vector space (every
subgroup of `Γ` finitely generated) all of whose elements are unipotent (`(g - 1)ᵐ = 0` for some
`m`) is stable. -/
def noetherianUnipotentGroupIsStable : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] (Γ : Subgroup (V ≃ₗ[K] V)),
    (∀ H : Subgroup Γ, H.FG) → (∀ g ∈ Γ, ∃ m : ℕ, ((g : V →ₗ[K] V) - 1) ^ m = 0) →
      HasStableSeries (Γ : Set (V ≃ₗ[K] V))

/--
Resolved false: the Kourovka Archive answers 2.61 "Not if the field has non-zero characteristic",
citing Ol'shanskii's book (1991); in characteristic zero the Archive records the positive result for
uniformly bounded indices of unipotence (Plotkin-Vovsi), which this target does not state. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.61 (B. I. Plotkin);
resolution: A. Yu. Ol'shanskii, The geometry of defining relations in groups, Kluwer, Dordrecht,
1991, Kourovka Archive, Problem 2.61: Not if the field has non-zero characteristic (Ol'shanskii's
book); true in characteristic zero if the indices of unipotence are uniformly bounded
(Plotkin-Vovsi), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted noetherianUnipotentGroupIsStable_refuted : ¬ noetherianUnipotentGroupIsStable

end MathlibExt.GroupTheory.NoetherianUnipotentGroupStableKourovka2Problem61Wanted
