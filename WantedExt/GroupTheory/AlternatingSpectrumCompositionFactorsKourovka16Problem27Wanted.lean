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

/-- **Spectrum of a group.** The spectrum $\omega(G)$ of a group $G$ is the set of natural numbers
that are orders of elements of $G$, where an element of infinite order is assigned order $0$. -/
def spectrum (G : Type*) [Group G] : Set ℕ :=
  Set.range (orderOf : G → ℕ)

/-- **Finite composition series.** Let $G$ be a group and $m$ a natural number. A sequence
$s_0, s_1, \dots, s_m$ of subgroups of $G$ is a composition series of length $m$ if $s_0$ is the
trivial subgroup, $s_m = G$, and for each $i < m$ the subgroup $s_i$ is a normal subgroup of
$s_{i+1}$ and the quotient $s_{i+1}/s_i$ is a simple group. -/
def IsCompositionSeries {G : Type} [Group G] {m : ℕ} (s : Fin (m + 1) → Subgroup G) : Prop :=
  s 0 = ⊥ ∧ s (Fin.last m) = ⊤ ∧ ∀ i : Fin m, s i.castSucc ≤ s i.succ ∧
    ∃ _ : ((s i.castSucc).subgroupOf (s i.succ)).Normal,
      IsSimpleGroup (s i.succ ⧸ (s i.castSucc).subgroupOf (s i.succ))

/-- **Non-abelian factor of a chain of subgroups.** Let $G$ be a group, let $s_0, s_1, \dots, s_m$
be subgroups of $G$, and let $i < m$. The $i$-th factor of the chain is non-abelian if
$s_i \cap s_{i+1}$ is a normal subgroup of $s_{i+1}$ and the quotient group
$s_{i+1}/(s_i \cap s_{i+1})$ is non-abelian, that is, it has elements $x, y$ with $xy \ne yx$.
When $s_i \le s_{i+1}$, this quotient is $s_{i+1}/s_i$. -/
def IsNonabelianFactor {G : Type} [Group G] {m : ℕ} (s : Fin (m + 1) → Subgroup G) (i : Fin m) :
    Prop :=
  ∃ _ : ((s i.castSucc).subgroupOf (s i.succ)).Normal,
    ∃ x y : s i.succ ⧸ (s i.castSucc).subgroupOf (s i.succ), x * y ≠ y * x

/-- **Kourovka Problem 16.27 (statement).** The statement that for every natural number $n$ and
every finite group $G$ whose spectrum, the set of orders of its elements, equals the spectrum of
the alternating group $A_n$, every composition series of $G$ has at most one non-abelian factor.

The problem was posed by A. V. Vasil'ev and V. D. Mazurov. -/
def alternatingSpectrumOneNonabelianFactor : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [Finite G], spectrum G = spectrum (alternatingGroup (Fin n)) →
    ∀ (m : ℕ) (s : Fin (m + 1) → Subgroup G), IsCompositionSeries s →
      ∀ i j : Fin m, IsNonabelianFactor s i → IsNonabelianFactor s j → i = j

/--
**Groups isospectral to an alternating group (Kourovka Problem 16.27).** Let $n$ be a natural
number and let $G$ be a finite group whose spectrum, the set of orders of its elements, equals the
spectrum of the alternating group $A_n$. Then every composition series of $G$ has at most one
non-abelian factor.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.27 (A. V.
Vasil'ev and V. D. Mazurov); resolution: I. B. Gorshkov, Algebra and Logic 52 (2013), no. 1, 41-45,
Kourovka Archive, Problem 16.27 (Yes, it is).
-/
public theorem_wanted alternatingSpectrumOneNonabelianFactor_holds :
    alternatingSpectrumOneNonabelianFactor

end MathlibExt.GroupTheory.AlternatingSpectrumCompositionFactorsKourovka16Problem27Wanted
