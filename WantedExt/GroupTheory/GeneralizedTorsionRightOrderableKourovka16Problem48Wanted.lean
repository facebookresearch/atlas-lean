/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups without generalized torsion that are not right-orderable (Kourovka Notebook Problem 16.48)

Kourovka Notebook, Problem 16.48 (V. M. Kopytov, N. Ya. Medvedev): a group `H` has generalized
torsion if `h^{x₁} h^{x₂} ⋯ h^{xₙ} = 1` for some `h ≠ 1`, some `n` and some `xᵢ ∈ H`. Is every group
without generalized torsion right-orderable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.GeneralizedTorsionRightOrderableKourovka16Problem48Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.48 (V. M. Kopytov, N. Ya. Medvedev).
UnsolvedMath record UM-00701240 (`KOU-16.48`), dataset ulamai/UnsolvedMath v1.8.0.

`n ≥ 1` is required (the empty product would make every element generalized torsion) and `h^x = x⁻¹
h x`. Right-orderable means admitting a linear order (a reflexive, transitive, antisymmetric, total
relation) invariant under right multiplication; right- and left-orderability are equivalent (`a ≤' b
↔ b⁻¹ ≤ a⁻¹`).
-/

/-- `h` is a generalized torsion element: `h ≠ 1` and some nonempty product of conjugates of `h` is
trivial. -/
def IsGeneralizedTorsion {H : Type*} [Group H] (h : H) : Prop :=
  h ≠ 1 ∧ ∃ l : List H, l ≠ [] ∧ (l.map fun x => x⁻¹ * h * x).prod = 1

/-- The right orders of `G`: linear orders (as relations) invariant under right multiplication. -/
def rightOrders (G : Type*) [Group G] : Set (G → G → Prop) :=
  {r | IsLinearOrder G r ∧ ∀ a b c : G, r a b → r (a * c) (b * c)}

/-- Kourovka 16.48 (V. M. Kopytov, N. Ya. Medvedev): every group without generalized torsion is
right-orderable. -/
def noGeneralizedTorsionRightOrderable : Prop :=
  ∀ (H : Type) [Group H], (∀ h : H, ¬ IsGeneralizedTorsion h) → (rightOrders H).Nonempty

/--
Resolved false: Cai and Clay give a condition ensuring that an amalgam is generalized torsion-free
and use it to construct a group that is generalized torsion-free but not left-orderable (Theorem
1.3, proved in Section 7), hence not right-orderable; the Kourovka Notebook (21st issue) answers
16.48 "No, not every". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.48 (V. M. Kopytov,
N. Ya. Medvedev); resolution: T. W. Cai and A. Clay, Generalized torsion in amalgams, preprint,
arXiv:2504.08084 (2025), Theorem 1.3 (there exists a group which is generalized torsion-free and not
left-orderable; Definition 7.1 and Theorem 7.2); the Kourovka Notebook (21st issue) marks 16.48
solved (No, not every), https://arxiv.org/abs/2504.08084.
-/
public theorem_wanted noGeneralizedTorsionRightOrderable_refuted :
    ¬ noGeneralizedTorsionRightOrderable

end MathlibExt.GroupTheory.GeneralizedTorsionRightOrderableKourovka16Problem48Wanted
