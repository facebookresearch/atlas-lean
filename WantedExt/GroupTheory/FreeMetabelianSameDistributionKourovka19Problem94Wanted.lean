/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equally distributed elements of free metabelian groups (Kourovka Notebook Problem 19.94)

Kourovka Notebook, Problem 19.94 (E. I. Timoshenko), marked solved in the 21st issue: two elements
`g₁, g₂` of a free metabelian group `F` with basis `x₁, …, xₙ` have the same distribution if the
equations `g₁(x₁, …, xₙ) = g` and `g₂(x₁, …, xₙ) = g` have the same number of solutions in every
finite metabelian group `G` for every `g ∈ G`. Is it true that `g₁` and `g₂` have the same
distribution if and only if they are conjugate by an automorphism of `F`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.FreeMetabelianSameDistributionKourovka19Problem94Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.94 (E. I. Timoshenko). UnsolvedMath
record UM-00701642 (`KOU-19.94`), dataset ulamai/UnsolvedMath v1.8.0.

`Mₙ = Fₙ / Fₙ''` (`derivedSeries _ 2`); elements of `Mₙ` are given by words `w ∈ Fₙ`, evaluated in a
finite metabelian group (`derivedSeries G 2 = ⊥`) by `FreeGroup.lift`, which depends only on the
image in `Mₙ`. "Conjugate by an automorphism" means mapped one to the other by an automorphism of
`Mₙ`.
-/

/-- The free metabelian group `Mₙ = Fₙ / Fₙ''` of rank `n`. -/
abbrev FreeMetabelian (n : ℕ) :=
  FreeGroup (Fin n) ⧸ derivedSeries (FreeGroup (Fin n)) 2

/-- Words `w₁, w₂ ∈ Fₙ` have the same distribution: for every finite metabelian group `G` and every
`g ∈ G`, the equations `w₁(a₁, …, aₙ) = g` and `w₂(a₁, …, aₙ) = g` have equally many solutions
`(a₁, …, aₙ) ∈ Gⁿ`. Since `G` is metabelian this depends only on the images of `w₁, w₂` in `Mₙ`. -/
def SameDistribution {n : ℕ} (w₁ w₂ : FreeGroup (Fin n)) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], derivedSeries G 2 = ⊥ → ∀ g : G,
    Nat.card {a : Fin n → G // FreeGroup.lift a w₁ = g} =
      Nat.card {a : Fin n → G // FreeGroup.lift a w₂ = g}

/-- Kourovka 19.94 (E. I. Timoshenko): two elements of the free metabelian group `Mₙ` (images of
words `w₁, w₂`) have the same distribution if and only if some automorphism of `Mₙ` maps one to the
other. -/
def sameDistributionIffAutomorphic : Prop :=
  ∀ (n : ℕ) (w₁ w₂ : FreeGroup (Fin n)), SameDistribution w₁ w₂ ↔
    ∃ φ : MulAut (FreeMetabelian n), φ (QuotientGroup.mk w₁) = QuotientGroup.mk w₂

/--
Resolved false: Ionin and Semidetnov (Answer 2.2) give two elements of the free metabelian group of
rank `2` with the same distribution on every finite metabelian group that no automorphism maps one
to the other (the converse direction is automatic). The solution was found with the assistance of
large language models and checked by the authors; the 21st issue of the Kourovka Notebook marks
19.94 solved ("No, it is not true"). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem
19.94 (E. I. Timoshenko); resolution: V. Ionin and A. Semidetnov, On Some More Problems from the
Kourovka Notebook, preprint, arXiv:2608.29219 (2026), Section 2, Answer 2.2 with Proposition 2.3 and
Lemmas 2.6-2.7: in M₂ = ⟨x, y⟩ with c = [x, y] and a^z = z⁻¹az, the elements g₁ =
c^{x²y⁷}(c^x)⁻¹(c^{xy⁷})⁻¹c and g₂ = c^{x³y⁷}(c^x)⁻¹(c^{x²y⁷})⁻¹c have the same distribution on
every finite metabelian group but lie in distinct Aut(M₂)-orbits; found with the assistance of large
language models and checked by the authors; the Kourovka Notebook (21st issue) marks 19.94 solved:
No, it is not true, https://arxiv.org/abs/2608.29219.
-/
public theorem_wanted sameDistributionIffAutomorphic_refuted : ¬ sameDistributionIffAutomorphic

end MathlibExt.GroupTheory.FreeMetabelianSameDistributionKourovka19Problem94Wanted
