/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sylow 2-subgroups with an abelian direct factor (Kourovka Notebook Problem 6.13)

Kourovka Notebook, Archive of Solved Problems, Problem 6.13 (A. S. Kondratiev): is it true that if a
non-abelian Sylow 2-subgroup of a finite group G has a non-trivial abelian direct factor, then G is
not simple?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace MathlibExt.GroupTheory.SylowTwoAbelianDirectFactorKourovka6Problem13Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.13 (A. S.
Kondratiev). UnsolvedMath record UM-00700360 (`KOU-6.13`), dataset ulamai/UnsolvedMath v1.8.0.

`P = A × B` is an internal direct product: `A ⊔ B = P`, `A ∩ B = 1`, and `A`, `B` commute
elementwise; `A` is non-trivial and abelian and `P` is non-abelian. Simple is Mathlib's
`IsSimpleGroup` (a group with a non-abelian Sylow subgroup is non-abelian).
-/

/-- Kourovka 6.13 (A. S. Kondratiev): if a non-abelian Sylow `2`-subgroup `P = A × B` of a finite
group `G` has a non-trivial abelian direct factor `A`, then `G` is not simple. -/
def sylowTwoAbelianDirectFactorNotSimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 2 G) (A B : Subgroup G),
    (∃ x ∈ (P : Subgroup G), ∃ y ∈ (P : Subgroup G), x * y ≠ y * x) →
    A ⊔ B = P → A ⊓ B = ⊥ → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
    A ≠ ⊥ → (∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) → ¬ IsSimpleGroup G

/--
Resolved true: the Kourovka Archive answers 6.13 "Yes, it is, mod CFSG", citing the survey of
Kabanov and Kondratiev (1979): a finite group whose non-abelian Sylow `2`-subgroup has a non-trivial
abelian direct factor is not simple. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 6.13 (A. S. Kondratiev); resolution: V. V. Kabanov and A. S. Kondratiev,
Sylow 2-subgroups of finite groups (a survey), Inst. Math. Mech. UNC AN SSSR, Sverdlovsk, 1979
(Russian), Kourovka Archive, Problem 6.13: Yes, it is, mod CFSG (Kabanov, Kondratiev),
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted sylowTwoAbelianDirectFactorNotSimple_holds :
    sylowTwoAbelianDirectFactorNotSimple

end MathlibExt.GroupTheory.SylowTwoAbelianDirectFactorKourovka6Problem13Wanted
