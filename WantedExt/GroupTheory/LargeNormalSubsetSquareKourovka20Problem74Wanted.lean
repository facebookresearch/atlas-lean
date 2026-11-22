/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Large normal subsets whose square is not the whole group (Kourovka Notebook Problem 20.74)

Kourovka Notebook, Problem 20.74 (L. Pyber), marked solved in the 21st issue: (a) conjecture: there
are only finitely many nonabelian finite simple groups `G` that have a normal subset `S` closed
under inversion such that `|S| > |G| / log₂ |G|` and `S² ≠ G`. (b) The same conjecture for the
groups `PSL(2, p)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

@[expose] public section

namespace MathlibExt.GroupTheory.LargeNormalSubsetSquareKourovka20Problem74Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.74 (L. Pyber). UnsolvedMath record
UM-00701732 (`KOU-20.74`), dataset ulamai/UnsolvedMath v1.8.0.

A normal subset is closed under conjugation. "Only finitely many groups" (up to isomorphism) is
stated as a bound on their orders, which is equivalent since there are finitely many groups of each
order; for (b) it is a bound on the prime `p`, with `PSL(2, p) = Matrix.ProjectiveSpecialLinearGroup
(Fin 2) (ZMod p)`.
-/

open scoped Pointwise

/-- `G` has a normal subset `S` (closed under conjugation) that is closed under inversion, has
more than `|G| / log₂ |G|` elements and satisfies `S² ≠ G`. -/
def HasLargeInverseClosedNormalSubsetWithSmallSquare (G : Type) [Group G] : Prop :=
  ∃ S : Set G, (∀ g s : G, s ∈ S → g * s * g⁻¹ ∈ S) ∧ (∀ s ∈ S, s⁻¹ ∈ S) ∧
    (Nat.card G : ℝ) / Real.logb 2 (Nat.card G) < S.ncard ∧ S * S ≠ Set.univ

/-- Kourovka 20.74(a) (L. Pyber), conjecture: only finitely many nonabelian finite simple groups
have such a subset, stated as a bound on their orders. -/
def finitelyManySimpleGroupsWithLargeNormalSubset : Prop :=
  ∃ N : ℕ, ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    HasLargeInverseClosedNormalSubsetWithSmallSquare G → Nat.card G ≤ N

/-- Kourovka 20.74(b) (L. Pyber), conjecture: only finitely many groups `PSL(2, p)`, `p` prime,
have such a subset. -/
def finitelyManyPSL2WithLargeNormalSubset : Prop :=
  ∃ N : ℕ, ∀ p : ℕ, p.Prime →
    HasLargeInverseClosedNormalSubsetWithSmallSquare
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) → p ≤ N

/--
Resolved false: Sheinfeld (Theorem 1.6) gives, for every odd `n ≥ 5`, an inverse-closed normal
subset `S` of the simple group `PSL_n(5) = SL_n(5)` with `|S| ≥ |G| / 960` and `S² ≠ G`, so
infinitely many nonabelian finite simple groups have such a subset; the paper states that this
disproves Pyber's conjecture, and the 21st issue of the Kourovka Notebook records 20.74(a) as "No,
there are infinitely many such groups". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem
20.74 (L. Pyber); resolution: O. Sheinfeld, On Shalev's quantitative version of Thompson's
conjecture, preprint, arXiv:2609.22004 (2026) (part (a)); S. V. Skresanov, Bull. London Math. Soc.
57 (2025), no. 11, 3429-3440 (part (b)), (a) Sheinfeld, Theorem 1.6: for every odd n ≥ 5 there is an
inverse-closed normal subset S ⊆ SL_n(5) = PSL_n(5) with |S| ≥ |SL_n(5)|/960 and diag(1, -I_{n-1}) ∉
S², which the paper states disproves Pyber's conjecture; (b) Skresanov, Corollary 3
(arXiv:2406.12506): in a finite simple group of Lie type of bounded rank every inverse-closed normal
subset A with |A| > |G|/log₂|G| has A² = G once |G| is large in terms of the rank, and part (b) for
PSL(2, p) follows; Kourovka Notebook (21st issue), Problem 20.74: a) No, there are infinitely many
such groups; b) The conjecture is proved for the groups PSL(2, p), https://arxiv.org/abs/2609.22004.
-/
public theorem_wanted finitelyManySimpleGroupsWithLargeNormalSubset_refuted :
    ¬ finitelyManySimpleGroupsWithLargeNormalSubset

/--
Resolved true: Skresanov (Bull. London Math. Soc. 57 (2025), Corollary 3) proves that in a finite
simple group of Lie type of bounded rank every inverse-closed normal subset `A` with `|A| > |G| /
log₂ |G|` satisfies `A² = G` once `|G|` is large, and notes that this settles the groups `PSL(2,
p)`; the 21st issue of the Kourovka Notebook records 20.74(b) as proved for the groups `PSL(2, p)`.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.74 (L. Pyber); resolution: O. Sheinfeld,
On Shalev's quantitative version of Thompson's conjecture, preprint, arXiv:2609.22004 (2026) (part
(a)); S. V. Skresanov, Bull. London Math. Soc. 57 (2025), no. 11, 3429-3440 (part (b)), (a)
Sheinfeld, Theorem 1.6: for every odd n ≥ 5 there is an inverse-closed normal subset S ⊆ SL_n(5) =
PSL_n(5) with |S| ≥ |SL_n(5)|/960 and diag(1, -I_{n-1}) ∉ S², which the paper states disproves
Pyber's conjecture; (b) Skresanov, Corollary 3 (arXiv:2406.12506): in a finite simple group of Lie
type of bounded rank every inverse-closed normal subset A with |A| > |G|/log₂|G| has A² = G once |G|
is large in terms of the rank, and part (b) for PSL(2, p) follows; Kourovka Notebook (21st issue),
Problem 20.74: a) No, there are infinitely many such groups; b) The conjecture is proved for the
groups PSL(2, p), https://arxiv.org/abs/2609.22004.
-/
public theorem_wanted finitelyManyPSL2WithLargeNormalSubset_holds :
    finitelyManyPSL2WithLargeNormalSubset

end MathlibExt.GroupTheory.LargeNormalSubsetSquareKourovka20Problem74Wanted
