/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Torsion-free groups with unique product presentations (Kourovka Notebook Problem 13.11)

Kourovka Notebook, Archive of Solved Problems, Problem 13.11 (V. V. Bludov): is a torsion-free group
almost polycyclic if it has generators `a₁, …, aₙ` such that every element has a unique presentation
`a₁^k₁ ⋯ aₙ^kₙ` with `kᵢ ∈ ℤ`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.UniqueProductPresentationPolycyclicKourovka13Problem11Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.11 (V. V.
Bludov). UnsolvedMath record UM-00700929 (`KOU-13.11`), dataset ulamai/UnsolvedMath v1.8.0.

Polycyclic means a finite subnormal series with cyclic factors and almost polycyclic means a
polycyclic subgroup of finite index, as in the resolving paper. Torsion-free means no nontrivial
element of finite order. Generation is implied by the bijectivity of `k ↦ a₁^k₁ ⋯ aₙ^kₙ`.
-/

/-- **Polycyclic groups (Kourovka Problem 13.11).** A group $G$ is polycyclic if it has a finite
series of subgroups $1 = H_0 \le H_1 \le \cdots \le H_n = G$ in which each $H_i$ is normal in
$H_{i+1}$ and each quotient $H_{i+1} / H_i$ is cyclic. -/
def IsPolycyclic (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧
    ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧
      ∃ _ : ((H i.castSucc).subgroupOf (H i.succ)).Normal,
        IsCyclic (H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ))

/-- **Almost polycyclic groups (Kourovka Problem 13.11).** A group $G$ is almost polycyclic, or
virtually polycyclic, if some subgroup of finite index in $G$ is polycyclic. -/
def IsAlmostPolycyclic (G : Type*) [Group G] : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolycyclic H

/-- **Groups with a unique product presentation.** A group $G$ has a unique product presentation if
there are $n \in \mathbb{N}$ and elements $a_0, \dots, a_{n-1} \in G$ such that every element of $G$
equals $a_0^{k_0} a_1^{k_1} \cdots a_{n-1}^{k_{n-1}}$ for exactly one tuple
$(k_0, \dots, k_{n-1}) \in \mathbb{Z}^n$. -/
def HasUniqueProductPresentation (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (a : Fin n → G),
    Function.Bijective fun k : Fin n → ℤ => (List.ofFn fun i => a i ^ k i).prod

/-- **Kourovka Problem 13.11 (torsion-free groups with a unique product presentation).** The
statement, asked by V. V. Bludov, that every group $G$ which is torsion-free (no element of $G$
other than $1$ has finite order) and has a unique product presentation is almost polycyclic. -/
def torsionFreeUniqueProductAlmostPolycyclic : Prop :=
  ∀ (G : Type) [Group G], (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) →
    HasUniqueProductPresentation G → IsAlmostPolycyclic G

/-- **A torsion-free group with a unique product presentation need not be almost polycyclic.** Not
every torsion-free group with a unique product presentation is almost polycyclic: there is a group
$G$ in which no element other than $1$ has finite order, which has a unique product presentation,
and which is not almost polycyclic.

Muranov's theorem gives such a group with $n$ generators for every $n \ge 63$.

Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.11 (V. V. Bludov); resolution: A.
Muranov, On torsion-free groups with finite regular file bases, Trans. Amer. Math. Soc. 359 (2007),
3609-3645, Theorem (Section 1, proved at the end of Section 5),
https://doi.org/10.1090/S0002-9947-07-04256-0.
-/
public theorem_wanted torsionFreeUniqueProductAlmostPolycyclic_refuted :
    ¬ torsionFreeUniqueProductAlmostPolycyclic

end MathlibExt.GroupTheory.UniqueProductPresentationPolycyclicKourovka13Problem11Wanted
