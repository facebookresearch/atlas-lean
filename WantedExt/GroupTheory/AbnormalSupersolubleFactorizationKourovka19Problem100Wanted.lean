/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Factorizations by three abnormal supersoluble subgroups (Kourovka Notebook Problem 19.100)

Kourovka Notebook, Problem 19.100 (A. F. Vasil'ev, T. I. Vasil'eva), marked solved in the 21st
issue: suppose that a finite group `G` admits a factorization `G = AB = BC = CA`, where `A`, `B`,
`C` are abnormal supersoluble subgroups. Is `G` supersoluble?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.AbnormalSupersolubleFactorizationKourovka19Problem100Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.100 (A. F. Vasil'ev, T. I. Vasil'eva).
UnsolvedMath record UM-00701648 (`KOU-19.100`), dataset ulamai/UnsolvedMath v1.8.0.

Supersoluble: a series of normal subgroups with cyclic factors (the encoding of the OpenConjectures
entry `Kourovka17Problem38`). `H` is abnormal when `g ∈ ⟨H, H^g⟩` for all `g` (the conjugation
convention does not matter, since `g` and `g⁻¹` lie in the same subgroups). Factorizations are
equalities of sets.
-/

open scoped Pointwise

/-- `G` is supersoluble: it has a series `⊥ = s 0 ≤ ⋯ ≤ s k = ⊤` of normal subgroups of `G` with
cyclic factors (`s (i + 1) = ⟨x⟩ ⊔ s i`). -/
def IsSupersoluble (G : Type) [Group G] : Prop :=
  ∃ (k : ℕ) (s : ℕ → Subgroup G), s 0 = ⊥ ∧ s k = ⊤ ∧ ∀ i < k, s i ≤ s (i + 1) ∧ (s i).Normal ∧
    ∃ x ∈ s (i + 1), s (i + 1) = Subgroup.closure {x} ⊔ s i

/-- `H` is abnormal in `G`: `g ∈ ⟨H, H^g⟩` for every `g ∈ G`. -/
def IsAbnormal {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ g : G, g ∈ H ⊔ H.map (MulAut.conj g).toMonoidHom

/-- Kourovka 19.100 (A. F. Vasil'ev, T. I. Vasil'eva): if a finite group `G = AB = BC = CA` is
factorized by abnormal supersoluble subgroups `A`, `B`, `C`, then `G` is supersoluble. -/
def abnormalSupersolubleTriFactorizationSupersoluble : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A B C : Subgroup G),
    IsAbnormal A → IsAbnormal B → IsAbnormal C →
    IsSupersoluble A → IsSupersoluble B → IsSupersoluble C →
    (A : Set G) * (B : Set G) = Set.univ → (B : Set G) * (C : Set G) = Set.univ →
    (C : Set G) * (A : Set G) = Set.univ → IsSupersoluble G

/--
Resolved true: the Kourovka Notebook (21st issue) answers 19.100 "Yes, it is" (L. S. Kazarin and V.
N. Tyutyanov, 2023). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.100 (A. F.
Vasil'ev, T. I. Vasil'eva); resolution: L. S. Kazarin and V. N. Tyutyanov, preprint, 2023 (Russian),
the Kourovka Notebook (21st issue) marks 19.100 solved: Yes, it is,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2025/09/d09ad0bed183d180d0bed0b2d0bad0b0-19.100-5.pdf.
-/
public theorem_wanted abnormalSupersolubleTriFactorizationSupersoluble_holds :
    abnormalSupersolubleTriFactorizationSupersoluble

end MathlibExt.GroupTheory.AbnormalSupersolubleFactorizationKourovka19Problem100Wanted
