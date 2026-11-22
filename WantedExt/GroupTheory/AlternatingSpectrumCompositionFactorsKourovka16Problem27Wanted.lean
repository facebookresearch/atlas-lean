/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups isospectral to alternating groups (Kourovka Notebook Problem 16.27)

Kourovka Notebook, Archive of Solved Problems, Problem 16.27 (A. V. Vasil'ev and V. D. Mazurov):
suppose that a finite group `G` has the same spectrum as an alternating group. Is it true that `G`
has at most one non-abelian composition factor?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.AlternatingSpectrumCompositionFactorsKourovka16Problem27Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.27 (A. V.
Vasil'ev and V. D. Mazurov). UnsolvedMath record UM-00701219 (`KOU-16.27`), dataset
ulamai/UnsolvedMath v1.8.0.

The spectrum is the set of element orders and the alternating groups are `alternatingGroup (Fin n)`
for all `n`. A composition series is a chain `⊥ = s₀ ≤ s₁ ≤ ⋯ ≤ s_m = ⊤` of subgroups, each normal
in the next with simple quotient; the target says that every composition series has at most one
non-abelian factor (by Jordan-Hölder, the same as for one composition series).
-/

/-- The spectrum `ω(G)` of a group: the set of orders of its elements. -/
def spectrum (G : Type*) [Group G] : Set ℕ :=
  Set.range (orderOf : G → ℕ)

/-- `s` is a composition series of `G` of length `m`: `s 0 = ⊥`, `s m = ⊤`, and every `s i` is a
normal subgroup of `s (i + 1)` with simple quotient. -/
def IsCompositionSeries {G : Type} [Group G] {m : ℕ} (s : Fin (m + 1) → Subgroup G) : Prop :=
  s 0 = ⊥ ∧ s (Fin.last m) = ⊤ ∧ ∀ i : Fin m, s i.castSucc ≤ s i.succ ∧
    ∃ _ : ((s i.castSucc).subgroupOf (s i.succ)).Normal,
      IsSimpleGroup (s i.succ ⧸ (s i.castSucc).subgroupOf (s i.succ))

/-- The `i`-th factor `s (i + 1) / s i` of the chain `s` is a non-abelian group. -/
def IsNonabelianFactor {G : Type} [Group G] {m : ℕ} (s : Fin (m + 1) → Subgroup G) (i : Fin m) :
    Prop :=
  ∃ _ : ((s i.castSucc).subgroupOf (s i.succ)).Normal,
    ∃ x y : s i.succ ⧸ (s i.castSucc).subgroupOf (s i.succ), x * y ≠ y * x

/-- Kourovka 16.27 (A. V. Vasil'ev, V. D. Mazurov): a finite group with the same spectrum as an
alternating group `Aₙ` has at most one non-abelian composition factor, stated for every
composition series. -/
def alternatingSpectrumOneNonabelianFactor : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [Finite G], spectrum G = spectrum (alternatingGroup (Fin n)) →
    ∀ (m : ℕ) (s : Fin (m + 1) → Subgroup G), IsCompositionSeries s →
      ∀ i j : Fin m, IsNonabelianFactor s i → IsNonabelianFactor s j → i = j

/--
Resolved true: the Kourovka Archive answers 16.27 "Yes, it is", citing Gorshkov (2013): a finite
group with the same spectrum as an alternating group has at most one non-abelian composition factor.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.27 (A. V.
Vasil'ev and V. D. Mazurov); resolution: I. B. Gorshkov, Algebra and Logic 52 (2013), no. 1, 41-45,
Kourovka Archive, Problem 16.27 (Yes, it is).
-/
public theorem_wanted alternatingSpectrumOneNonabelianFactor_holds :
    alternatingSpectrumOneNonabelianFactor

end MathlibExt.GroupTheory.AlternatingSpectrumCompositionFactorsKourovka16Problem27Wanted
