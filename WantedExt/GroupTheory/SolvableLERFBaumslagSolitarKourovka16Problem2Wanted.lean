/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LERF solvable groups and Baumslag-Solitar subgroups (Kourovka Notebook Problem 16.2)

Kourovka Notebook, Archive of Solved Problems, Problem 16.2 (R. C. Alperin): a group `G` is
subgroup-separable if for any subgroup `H` and `x ∉ H` there is a homomorphism `f` to a finite group
with `f(x) ∉ f(H)`. Is it true that a finitely generated solvable group is locally
subgroup-separable if and only if it does not contain a solvable Baumslag-Solitar group `BS(1, n) =
⟨a, b | b a b⁻¹ = aⁿ⟩`, `n > 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.SolvableLERFBaumslagSolitarKourovka16Problem2Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.2 (R. C.
Alperin). UnsolvedMath record UM-00701194 (`KOU-16.2`), dataset ulamai/UnsolvedMath v1.8.0.

Locally subgroup-separable is the problem's separability condition for finitely generated subgroups
(LERF), as in the resolving paper: Button states Problem 16.2 as asking whether a finitely generated
solvable group is LERF if and only if it does not contain `BS(1, m)` for `m > 1`. For all subgroups
the condition characterizes the polycyclic groups among finitely generated solvable groups (the
problem's background, Alperin). Containing `BS(1, n)` means having a subgroup isomorphic to it,
stated as an injective homomorphism from the presented group.
-/

/-- The solvable Baumslag-Solitar group `BS(1, n) = ⟨a, b | b a b⁻¹ = aⁿ⟩`, with `a = x₀` and
`b = x₁`. -/
abbrev BS1 (n : ℕ) : Type :=
  PresentedGroup ({FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0 ^ n)⁻¹} :
    Set (FreeGroup (Fin 2)))

/-- The subgroup `H` of `G` is separable: every `x ∉ H` stays outside the image of `H` under some
homomorphism to a finite group. -/
def IsSeparableSubgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ x : G, x ∉ H → ∃ (F : Type) (_ : Group F) (_ : Finite F) (f : G →* F), f x ∉ H.map f

/-- `G` is locally subgroup-separable (LERF): every finitely generated subgroup is separable. -/
def IsLocallySubgroupSeparable (G : Type) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG → IsSeparableSubgroup H

/-- Kourovka 16.2 (R. C. Alperin): a finitely generated solvable group is locally
subgroup-separable if and only if it has no subgroup isomorphic to a solvable Baumslag-Solitar
group `BS(1, n)` with `n > 1`. -/
def solvableLERFIffNoBaumslagSolitar : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → Group.IsSolvable G →
    (IsLocallySubgroupSeparable G ↔ ¬ ∃ n : ℕ, 1 < n ∧ ∃ f : BS1 n →* G, Function.Injective f)

/--
Resolved false: Button (Theorem 2.1) shows that the soluble group `G = ⟨t, ℤ × ℤ⟩`, the ascending
HNN extension of `ℤ × ℤ = ⟨u, v⟩` by the injective endomorphism `u ↦ u⁵ v⁻¹`, `v ↦ u²`, is not LERF
but contains no `BS(1, m)` with `m ≠ 0, ±1`, and concludes that the answer to Problem 16.2 is no;
the Kourovka Archive answers 16.2 "No, it is not", citing Button. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.2 (R. C. Alperin); resolution: J.
O. Button, Strictly ascending HNN extensions in soluble groups, Ricerche di Matematica 61 (2012),
no. 1, 139-145, arXiv:1004.0197, Theorem 2.1 and the remark after it (the soluble ascending HNN
extension G = ⟨t, ℤ × ℤ⟩ with θ(u) = u⁵v⁻¹, θ(v) = u² is not LERF and contains no BS(1, m), m ≠ 0,
±1, so the answer to Problem 16.2 is no); Kourovka Archive, Problem 16.2 (No, it is not),
https://arxiv.org/abs/1004.0197.
-/
public theorem_wanted solvableLERFIffNoBaumslagSolitar_refuted : ¬ solvableLERFIffNoBaumslagSolitar

end MathlibExt.GroupTheory.SolvableLERFBaumslagSolitarKourovka16Problem2Wanted
