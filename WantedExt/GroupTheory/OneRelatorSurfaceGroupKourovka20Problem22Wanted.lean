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

/-- `G` is a one-relator group: `G ≅ ⟨x₁, …, xₙ | r⟩` for some `n` and some word `r`. -/
def IsOneRelatorGroup (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (r : FreeGroup (Fin n)), Nonempty (G ≃* PresentedGroup ({r} : Set (FreeGroup (Fin n))))

/-- The surface relator `[a₁, b₁] ⋯ [a_g, b_g]` with `[a, b] = a b a⁻¹ b⁻¹`. -/
def orientableSurfaceRelator (g : ℕ) : FreeGroup (Fin g ⊕ Fin g) :=
  (List.ofFn fun i : Fin g => FreeGroup.of (Sum.inl i) * FreeGroup.of (Sum.inr i) *
    (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod

/-- The surface relator `a₁² ⋯ a_k²`. -/
def nonorientableSurfaceRelator (k : ℕ) : FreeGroup (Fin k) :=
  (List.ofFn fun i : Fin k => FreeGroup.of i * FreeGroup.of i).prod

/-- `G` is a surface group: the fundamental group of a closed aspherical surface, i.e. of an
orientable closed surface of genus `g ≥ 1` or a non-orientable one of genus `k ≥ 2`, given by the
standard one-relator presentations. -/
def IsSurfaceGroup (G : Type) [Group G] : Prop :=
  (∃ g : ℕ, 1 ≤ g ∧ Nonempty (G ≃* PresentedGroup {orientableSurfaceRelator g})) ∨
    ∃ k : ℕ, 2 ≤ k ∧ Nonempty (G ≃* PresentedGroup {nonorientableSurfaceRelator k})

/-- Kourovka 20.22 (B. Fine, G. Rosenberger, L. Wienke): a one-relator group that is neither free
nor cyclic and all of whose subgroups of infinite index are free is a surface group. -/
def oneRelatorInfiniteIndexFreeIsSurfaceGroup : Prop :=
  ∀ (G : Type) [Group G], IsOneRelatorGroup G → ¬ IsFreeGroup G → ¬ IsCyclic G →
    (∀ H : Subgroup G, H.index = 0 → IsFreeGroup H) → IsSurfaceGroup G

/--
Resolved true: Wilton (2024, Theorem D) proves that an infinite one-relator group that is neither
free nor a surface group has a non-free subgroup of infinite index (a non-cyclic one-relator group
has at least two generators and so is infinite); the Kourovka Notebook (21st issue) answers 20.22
"Yes, it is". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.22 (B. Fine, G. Rosenberger, L.
Wienke); resolution: H. Wilton, Surface groups among cubulated hyperbolic and one-relator groups,
preprint, arXiv:2406.02121 (2024), Theorem D: an infinite one-relator group that is neither free nor
a surface group has a subgroup of infinite index that is not free; the Kourovka Notebook (21st
issue) marks 20.22 solved, https://arxiv.org/abs/2406.02121.
-/
public theorem_wanted oneRelatorInfiniteIndexFreeIsSurfaceGroup_holds :
    oneRelatorInfiniteIndexFreeIsSurfaceGroup

end MathlibExt.GroupTheory.OneRelatorSurfaceGroupKourovka20Problem22Wanted
