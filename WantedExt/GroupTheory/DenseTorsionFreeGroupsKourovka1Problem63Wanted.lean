/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dense torsion-free groups (Kourovka Notebook Problem 1.63)

Kourovka Notebook, Archive of Solved Problems, Problem 1.63 (P. G. Kontorovich): a group `G` is
dense if it has no proper isolated subgroups other than its trivial subgroup. a) Do there exist
dense torsion-free groups that are not locally cyclic? b) Suppose that any two non-trivial elements
`x` and `y` of a torsion-free group `G` satisfy `x^k = y^l`, where `k` and `l` are non-zero integers
depending on `x` and `y`. Does it follow that `G` is abelian?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.DenseTorsionFreeGroupsKourovka1Problem63Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.63 (P. G.
Kontorovich). UnsolvedMath record UM-00700054 (`KOU-1.63`), dataset ulamai/UnsolvedMath v1.8.0.

A subgroup `H` is isolated if `xⁿ ∈ H` with `n ≥ 1` implies `x ∈ H`; dense means the only isolated
subgroups are `1` and `G`. Locally cyclic means every finitely generated subgroup is cyclic, and
torsion-free means no element other than `1` has finite order.
-/

/-- `G` is torsion-free: no element other than `1` has finite order. -/
def IsTorsionFreeGroup (G : Type) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g

/-- The subgroup `H` is isolated: `xⁿ ∈ H` with `n ≥ 1` implies `x ∈ H`. -/
def IsIsolated {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ (x : G) (n : ℕ), 0 < n → x ^ n ∈ H → x ∈ H

/-- `G` is dense: its only isolated subgroups are the trivial subgroup and `G` itself. -/
def IsDense (G : Type) [Group G] : Prop :=
  ∀ H : Subgroup G, IsIsolated H → H = ⊥ ∨ H = ⊤

/-- `G` is locally cyclic: every finitely generated subgroup is cyclic. -/
def IsLocallyCyclic (G : Type) [Group G] : Prop :=
  ∀ s : Finset G, IsCyclic (Subgroup.closure (s : Set G))

/-- Kourovka 1.63(a) (P. G. Kontorovich): there is a dense torsion-free group that is not locally
cyclic. -/
def existsDenseTorsionFreeNotLocallyCyclic : Prop :=
  ∃ (G : Type) (_ : Group G), IsTorsionFreeGroup G ∧ IsDense G ∧ ¬ IsLocallyCyclic G

/-- Kourovka 1.63(b) (P. G. Kontorovich): a torsion-free group in which any two nontrivial elements
`x`, `y` satisfy `x ^ k = y ^ l` for some nonzero integers `k`, `l` is abelian. -/
def commensurablePowersImpliesAbelian : Prop :=
  ∀ (G : Type) [Group G], IsTorsionFreeGroup G →
    (∀ x y : G, x ≠ 1 → y ≠ 1 → ∃ k l : ℤ, k ≠ 0 ∧ l ≠ 0 ∧ x ^ k = y ^ l) →
      ∀ a b : G, a * b = b * a

/--
Resolved true: the Kourovka Archive answers 1.63(a) "Yes, such groups do exist", citing Adian
(1971). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.63
(P. G. Kontorovich); resolution: S. I. Adian, On some torsion-free groups, Math. USSR-Izv. 5 (1971),
475-484, Kourovka Archive, Problem 1.63 (a) Yes, such groups do exist; (b) Not necessarily.
-/
public theorem_wanted existsDenseTorsionFreeNotLocallyCyclic_holds :
    existsDenseTorsionFreeNotLocallyCyclic

/--
Resolved false: the Kourovka Archive answers 1.63(b) "Not necessarily", citing Adian (1971): some
non-abelian torsion-free group has `x^k = y^l` with nonzero `k`, `l` for any two nontrivial elements
`x`, `y`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.63
(P. G. Kontorovich); resolution: S. I. Adian, On some torsion-free groups, Math. USSR-Izv. 5 (1971),
475-484, Kourovka Archive, Problem 1.63 (a) Yes, such groups do exist; (b) Not necessarily.
-/
public theorem_wanted commensurablePowersImpliesAbelian_refuted :
    ¬ commensurablePowersImpliesAbelian

end MathlibExt.GroupTheory.DenseTorsionFreeGroupsKourovka1Problem63Wanted
