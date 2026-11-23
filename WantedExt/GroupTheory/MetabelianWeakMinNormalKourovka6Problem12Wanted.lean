/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Metabelian groups with the weak Min-n condition (Kourovka Notebook Problem 6.12)

Kourovka Notebook, Archive of Solved Problems, Problem 6.12 (D. I. Zaitsev): a) Is a metabelian
group countable if it satisfies the weak minimum condition for normal subgroups? b) Is such a group
minimax if it is torsion-free?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import WantedExt.GroupTheory.MinimaxFiniteImagesKourovka12Problem90Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.MetabelianWeakMinNormalKourovka6Problem12Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.12 (D. I.
Zaitsev). UnsolvedMath record UM-00700359 (`KOU-6.12`), dataset ulamai/UnsolvedMath v1.8.0.

Metabelian is `derivedSeries G 2 = ⊥`. The weak minimal condition for normal subgroups (Min-∞-n)
says that in every descending chain of normal subgroups the indices `|N_n : N_(n+1)|` are finite
beyond some point; equivalently (pass to a subchain) no descending chain of normal subgroups has all
its indices infinite, which is `HasWeakMinNormal` (`relIndex = 0` encodes infinite index). Minimax
is `IsMinimax` of the Kourovka 12.90 module: a finite subnormal series whose factors satisfy the
maximal or the minimal condition on subgroups. Torsion-free is written `∀ g, g ≠ 1 → ¬ IsOfFinOrder
g`.
-/

open MathlibExt.GroupTheory.MinimaxFiniteImagesKourovka12Problem90Wanted (IsMinimax)

/-- `G` satisfies the weak minimal condition for normal subgroups: no descending chain
`N₀ ≥ N₁ ≥ ⋯` of normal subgroups has every index `|N_n : N_(n+1)|` infinite (`relIndex = 0`). -/
def HasWeakMinNormal (G : Type) [Group G] : Prop :=
  ∀ N : ℕ → Subgroup G, (∀ n, (N n).Normal) → (∀ n, N (n + 1) ≤ N n) →
    ∃ n, (N (n + 1)).relIndex (N n) ≠ 0

/-- Kourovka 6.12(a) (D. I. Zaitsev): a metabelian group satisfying the weak minimal condition for
normal subgroups is countable. -/
def metabelianWeakMinNormalCountable : Prop :=
  ∀ (G : Type) [Group G], derivedSeries G 2 = ⊥ → HasWeakMinNormal G → Countable G

/-- Kourovka 6.12(b) (D. I. Zaitsev): a torsion-free metabelian group satisfying the weak minimal
condition for normal subgroups is minimax. -/
def metabelianTorsionFreeWeakMinNormalMinimax : Prop :=
  ∀ (G : Type) [Group G], derivedSeries G 2 = ⊥ → HasWeakMinNormal G →
    (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) → IsMinimax G

/--
Resolved true: the Kourovka Archive answers 6.12 "Yes, it is, in both cases", citing Zaitsev,
Kurdachenko and Tushev (1985); for part (a), every metabelian group satisfying the weak minimal
condition for normal subgroups is countable. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 6.12 (D. I. Zaitsev); resolution: D. I. Zaitsev, L. A.
Kurdachenko and A. V. Tushev, Modules over nilpotent groups of finite rank, Algebra and Logic 24
(1985), 412-436, Corollary to Theorem 4.2 (every metabelian group with Min-∞-n is countable) and
Theorem 4.3 (torsion-free metabelian groups with Min-∞-n are minimax), as summarized in the zbMATH
review Zbl 0604.20037, which defines Min-∞-n: in every descending chain of normal subgroups the
indices are finite beyond some point; Kourovka Archive, Problem 6.12: Yes, it is, in both cases,
https://doi.org/10.1007/BF01978845.
-/
public theorem_wanted metabelianWeakMinNormalCountable_holds : metabelianWeakMinNormalCountable

/--
Resolved true: the Kourovka Archive answers 6.12 "Yes, it is, in both cases", citing Zaitsev,
Kurdachenko and Tushev (1985); for part (b), every torsion-free metabelian group satisfying the weak
minimal condition for normal subgroups is minimax. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 6.12 (D. I. Zaitsev); resolution: D. I. Zaitsev, L. A.
Kurdachenko and A. V. Tushev, Modules over nilpotent groups of finite rank, Algebra and Logic 24
(1985), 412-436, Corollary to Theorem 4.2 (every metabelian group with Min-∞-n is countable) and
Theorem 4.3 (torsion-free metabelian groups with Min-∞-n are minimax), as summarized in the zbMATH
review Zbl 0604.20037, which defines Min-∞-n: in every descending chain of normal subgroups the
indices are finite beyond some point; Kourovka Archive, Problem 6.12: Yes, it is, in both cases,
https://doi.org/10.1007/BF01978845.
-/
public theorem_wanted metabelianTorsionFreeWeakMinNormalMinimax_holds :
    metabelianTorsionFreeWeakMinNormalMinimax

end MathlibExt.GroupTheory.MetabelianWeakMinNormalKourovka6Problem12Wanted
