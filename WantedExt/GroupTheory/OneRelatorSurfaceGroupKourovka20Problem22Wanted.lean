/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# One-relator groups whose infinite-index subgroups are free (Kourovka Notebook Problem 20.22)

Kourovka Notebook, Problem 20.22 (B. Fine, G. Rosenberger, L. Wienke), marked solved in the 21st
issue: let `G` be a non-free and non-cyclic one-relator group in which every subgroup of infinite
index is free. Is `G` a surface group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.OneRelatorSurfaceGroupKourovka20Problem22Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.22 (B. Fine, G. Rosenberger, L. Wienke).
UnsolvedMath record UM-00701680 (`KOU-20.22`), dataset ulamai/UnsolvedMath v1.8.0.

A one-relator group is isomorphic to `⟨x₁, …, xₙ | r⟩` (`PresentedGroup {r}`); free is Mathlib's
`IsFreeGroup`; infinite index is `Subgroup.index = 0`. A surface group is the fundamental group of a
closed aspherical surface (Wilton's usage): the standard one-relator presentations of the orientable
surfaces of genus `g ≥ 1` and the non-orientable ones of genus `k ≥ 2`.
-/

/-- **One-relator groups with finitely many generators.** A group $G$ is a one-relator group if,
for some $n \ge 0$ and some element $r$ of the free group on $x_1, \dots, x_n$, $G$ is isomorphic
to the group $\langle x_1, \dots, x_n \mid r \rangle$ with generators $x_1, \dots, x_n$ and the
single relator $r$. -/
def IsOneRelatorGroup (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (r : FreeGroup (Fin n)), Nonempty (G ≃* PresentedGroup ({r} : Set (FreeGroup (Fin n))))

/-- **Orientable surface relator.** For $g \ge 0$, the orientable surface relator of genus $g$ is
the element $[a_1, b_1] [a_2, b_2] \cdots [a_g, b_g]$ of the free group on the $2g$ generators
$a_1, \dots, a_g, b_1, \dots, b_g$, where $[a, b] = a b a^{-1} b^{-1}$; for $g = 0$ it is the
identity. -/
def orientableSurfaceRelator (g : ℕ) : FreeGroup (Fin g ⊕ Fin g) :=
  (List.ofFn fun i : Fin g => FreeGroup.of (Sum.inl i) * FreeGroup.of (Sum.inr i) *
    (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod

/-- **Non-orientable surface relator.** For $k \ge 0$, the non-orientable surface relator of genus
$k$ is the element $a_1^2 a_2^2 \cdots a_k^2$ of the free group on the $k$ generators
$a_1, \dots, a_k$; for $k = 0$ it is the identity. -/
def nonorientableSurfaceRelator (k : ℕ) : FreeGroup (Fin k) :=
  (List.ofFn fun i : Fin k => FreeGroup.of i * FreeGroup.of i).prod

/-- **Surface groups.** A group $G$ is a surface group if either $G$ is isomorphic to
$\langle a_1, b_1, \dots, a_g, b_g \mid [a_1, b_1] \cdots [a_g, b_g] \rangle$ for some $g \ge 1$,
where $[a, b] = a b a^{-1} b^{-1}$, or $G$ is isomorphic to
$\langle a_1, \dots, a_k \mid a_1^2 \cdots a_k^2 \rangle$ for some $k \ge 2$.

These are the standard one-relator presentations of the fundamental groups of the closed
orientable surfaces of genus $g \ge 1$ and the closed non-orientable surfaces of genus $k \ge 2$,
that is, of the closed aspherical surfaces. -/
def IsSurfaceGroup (G : Type) [Group G] : Prop :=
  (∃ g : ℕ, 1 ≤ g ∧ Nonempty (G ≃* PresentedGroup {orientableSurfaceRelator g})) ∨
    ∃ k : ℕ, 2 ≤ k ∧ Nonempty (G ≃* PresentedGroup {nonorientableSurfaceRelator k})

/-- **Kourovka Problem 20.22 (statement).** The statement that every group $G$ with the following
properties is a surface group: $G$ is isomorphic to $\langle x_1, \dots, x_n \mid r \rangle$ for
some $n \ge 0$ and some element $r$ of the free group on $x_1, \dots, x_n$; $G$ is neither free nor
cyclic; and every subgroup of infinite index in $G$ is free. Here $G$ is a surface group if it is
isomorphic to $\langle a_1, b_1, \dots, a_g, b_g \mid [a_1, b_1] \cdots [a_g, b_g] \rangle$ for some
$g \ge 1$, where $[a, b] = a b a^{-1} b^{-1}$, or to
$\langle a_1, \dots, a_k \mid a_1^2 \cdots a_k^2 \rangle$ for some $k \ge 2$. -/
def oneRelatorInfiniteIndexFreeIsSurfaceGroup : Prop :=
  ∀ (G : Type) [Group G], IsOneRelatorGroup G → ¬ IsFreeGroup G → ¬ IsCyclic G →
    (∀ H : Subgroup G, H.index = 0 → IsFreeGroup H) → IsSurfaceGroup G

/--
**Wilton's theorem (Kourovka Problem 20.22).** Let $G$ be a group isomorphic to
$\langle x_1, \dots, x_n \mid r \rangle$ for some $n \ge 0$ and some element $r$ of the free group
on $x_1, \dots, x_n$. If $G$ is neither free nor cyclic and every subgroup of infinite index in $G$
is free, then $G$ is a surface group: $G$ is isomorphic to
$\langle a_1, b_1, \dots, a_g, b_g \mid [a_1, b_1] \cdots [a_g, b_g] \rangle$ for some $g \ge 1$,
where $[a, b] = a b a^{-1} b^{-1}$, or to $\langle a_1, \dots, a_k \mid a_1^2 \cdots a_k^2 \rangle$
for some $k \ge 2$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.22 (B. Fine, G. Rosenberger, L.
Wienke); resolution: H. Wilton, Surface groups among cubulated hyperbolic and one-relator groups,
preprint, arXiv:2406.02121 (2024), Theorem D: an infinite one-relator group that is neither free nor
a surface group has a subgroup of infinite index that is not free; the Kourovka Notebook (21st
issue) marks 20.22 solved, https://arxiv.org/abs/2406.02121.
-/
public theorem_wanted oneRelatorInfiniteIndexFreeIsSurfaceGroup_holds :
    oneRelatorInfiniteIndexFreeIsSurfaceGroup

end MathlibExt.GroupTheory.OneRelatorSurfaceGroupKourovka20Problem22Wanted
