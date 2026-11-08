/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Infinite chains of `Φ`-extensions of `p`-groups (Kourovka Notebook Problem 16.12)

Kourovka Notebook, Archive of Solved Problems, Problem 16.12 (Ya. G. Berkovich): a `Φ`-extension of
a finite `p`-group `G` is a finite `p`-group `H` with a normal subgroup `N` of order `p` such that
`H/N ≅ G` and `N ≤ Φ(H)`. Is it true that for every finite `p`-group `G` there is an infinite
sequence `G = G₁, G₂, …` in which every `G_{i+1}` is a `Φ`-extension of `G_i`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Frattini

@[expose] public section

namespace MathlibExt.GroupTheory.FrattiniExtensionSequenceKourovka16Problem12Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.12 (Ya. G.
Berkovich). UnsolvedMath record UM-00701204 (`KOU-16.12`), dataset ulamai/UnsolvedMath v1.8.0.

`G` is required to be nontrivial: the trivial group has no `Φ`-extension (a group `H` of order `p`
has `Φ(H) = 1`, so no subgroup of order `p` lies in `Φ(H)`), and every later term of such a sequence
is nontrivial anyway. The sequence is a family of groups `S : ℕ → Type` indexed from `0`, with `S 0
≅ G`.
-/

/-- `H` is a `Φ`-extension of `G` (Ya. G. Berkovich): `H` is a finite `p`-group with a normal
subgroup `N` of order `p` such that `N ≤ Φ(H)` and `H / N ≅ G`. -/
def IsPhiExtension (p : ℕ) (H G : Type) [Group H] [Group G] : Prop :=
  Finite H ∧ IsPGroup p H ∧ ∃ N : Subgroup H, ∃ _ : N.Normal,
    Nat.card N = p ∧ N ≤ frattini H ∧ Nonempty (H ⧸ N ≃* G)

/-- Kourovka 16.12 (Ya. G. Berkovich): for every prime `p` and every nontrivial finite `p`-group
`G` there is an infinite sequence `G = G₀, G₁, G₂, …` of groups in which every `G_{i+1}` is a
`Φ`-extension of `G_i`. -/
def phiExtensionSequence : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsPGroup p G → Nontrivial G →
    ∃ (S : ℕ → Type) (_ : ∀ i, Group (S i)), Nonempty (S 0 ≃* G) ∧
      ∀ i, IsPhiExtension p (S (i + 1)) (S i)

/--
Resolved true: the Kourovka Archive answers 16.12 "Yes, it is", citing Kamornikov (2008). The
trivial group is excluded: it has no `Φ`-extension, since a group of order `p` has trivial Frattini
subgroup. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.12
(Ya. G. Berkovich); resolution: S. F. Kamornikov, Izv. Gomel' Univ. 5 (2008), 200-201 (Russian),
Kourovka Archive, Problem 16.12 (Yes, it is).
-/
public theorem_wanted phiExtensionSequence_holds : phiExtensionSequence

end MathlibExt.GroupTheory.FrattiniExtensionSequenceKourovka16Problem12Wanted
