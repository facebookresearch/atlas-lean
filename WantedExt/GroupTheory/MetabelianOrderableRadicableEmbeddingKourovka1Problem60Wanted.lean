/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `e4e4de3e175eab51e689706fcab2456068d90482`.

Original formalization by Adam Kiezun, with contributions by Metamate
(consolidation commit `f204b2a6`, PR #9859); ported with attribution.
-/

/-
# Radicable orderable hulls of metabelian groups (Kourovka Notebook Problem 1.60)

Kourovka Notebook, Archive of Solved Problems, Problem 1.60 (A. I. Kokorin): can an orderable
metabelian group be embedded in a radicable orderable group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Solvable
public import MathlibExt.GroupTheory.Orderability

@[expose] public section

namespace MathlibExt.GroupTheory.MetabelianOrderableRadicableEmbeddingKourovka1Problem60Wanted

export MathlibExt.GroupTheory (IsBiInvariantOrder IsOrderable)

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.60 (A. I.
Kokorin). UnsolvedMath record UM-00700052 (`KOU-1.60`), dataset ulamai/UnsolvedMath v1.8.0.

"Orderable" is the Kokorin-Kopytov sense of the problem list (fully ordered): `G` admits a linear
order invariant under multiplication on both sides (`IsOrderable`). Metabelian means derived length
at most `2` (`derivedSeries G 2 = ⊥`); radicable means every element has an `n`-th root for every `n
≥ 1`. The embedding is an injective group homomorphism, as the problem asks; the target group is
taken in `Type`.
-/

/-- `G` is radicable: every element has an `n`-th root for every `n ≥ 1`. -/
def IsRadicable (G : Type) [Group G] : Prop :=
  ∀ g : G, ∀ n : ℕ, 0 < n → ∃ h : G, h ^ n = g

/-- Kourovka 1.60 (A. I. Kokorin): every orderable metabelian group (derived length at most `2`)
embeds, by an injective group homomorphism, in a radicable orderable group. -/
def orderableMetabelianEmbedsInRadicableOrderable : Prop :=
  ∀ (G : Type) [Group G], derivedSeries G 2 = ⊥ → IsOrderable G →
    ∃ (H : Type) (_ : Group H) (f : G →* H), Function.Injective f ∧ IsOrderable H ∧ IsRadicable H

/--
Resolved true: the Kourovka Archive answers 1.60 "Yes, it can", citing Bludov and Medvedev (1974).
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.60 (A. I.
Kokorin); resolution: V. V. Bludov and N. Ya. Medvedev, Algebra and Logic 13 (1974), 207-209,
Kourovka Archive, Problem 1.60 (Yes, it can).
-/
public theorem_wanted orderableMetabelianEmbedsInRadicableOrderable_holds :
    orderableMetabelianEmbedsInRadicableOrderable

private example : ProofWanted.Stmt orderableMetabelianEmbedsInRadicableOrderable_holds ↔
    orderableMetabelianEmbedsInRadicableOrderable :=
  Iff.rfl

end MathlibExt.GroupTheory.MetabelianOrderableRadicableEmbeddingKourovka1Problem60Wanted
