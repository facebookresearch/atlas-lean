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

/-- **Free metabelian group of rank $n$ (Kourovka 19.94).** For a natural number $n$, let $F_n$
be the free group on $n$ generators. The free metabelian group of rank $n$ is the quotient
$M_n = F_n / F_n''$ of $F_n$ by its second derived subgroup $F_n'' = [[F_n, F_n], [F_n, F_n]]$. -/
abbrev FreeMetabelian (n : ℕ) :=
  FreeGroup (Fin n) ⧸ derivedSeries (FreeGroup (Fin n)) 2

/-- **Words with the same distribution.** Let $n$ be a natural number and $F_n$ the free group on
generators $x_1, \dots, x_n$. Words $w_1, w_2 \in F_n$ have the same distribution when, for every
finite metabelian group $G$ (that is, $G'' = 1$) and every $g \in G$, the number of tuples
$(a_1, \dots, a_n) \in G^n$ with $w_1(a_1, \dots, a_n) = g$ equals the number of tuples with
$w_2(a_1, \dots, a_n) = g$. Here $w(a_1, \dots, a_n)$ is the image of $w$ under the homomorphism
$F_n \to G$ sending $x_i$ to $a_i$.

Since $G$ is metabelian, this depends only on the images of $w_1, w_2$ in the free metabelian group
$F_n / F_n''$. -/
def SameDistribution {n : ℕ} (w₁ w₂ : FreeGroup (Fin n)) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], derivedSeries G 2 = ⊥ → ∀ g : G,
    Nat.card {a : Fin n → G // FreeGroup.lift a w₁ = g} =
      Nat.card {a : Fin n → G // FreeGroup.lift a w₂ = g}

/-- **Timoshenko's question on equally distributed elements (Kourovka 19.94).** The statement that
for every natural number $n$ and all words $w_1, w_2$ in the free group $F_n$ of rank $n$, the
words $w_1$ and $w_2$ have the same distribution if and only if some automorphism of the free
metabelian group $M_n = F_n / F_n''$ maps the image of $w_1$ in $M_n$ to the image of $w_2$. -/
def sameDistributionIffAutomorphic : Prop :=
  ∀ (n : ℕ) (w₁ w₂ : FreeGroup (Fin n)), SameDistribution w₁ w₂ ↔
    ∃ φ : MulAut (FreeMetabelian n), φ (QuotientGroup.mk w₁) = QuotientGroup.mk w₂

/--
**Equally distributed elements need not be automorphic (Kourovka 19.94).** It is not the case
that for every natural number $n$ and all words $w_1, w_2$ in the free group $F_n$ of rank $n$,
the words $w_1$ and $w_2$ have the same distribution if and only if some automorphism of the free
metabelian group $M_n = F_n / F_n''$ maps the image of $w_1$ in $M_n$ to the image of $w_2$.

Ionin and Semidetnov (Answer 2.2) give two elements of the free metabelian group of rank $2$ with
the same distribution on every finite metabelian group that no automorphism maps one to the other
(the converse direction is automatic). The solution was found with the assistance of large
language models and checked by the authors; the 21st issue of the Kourovka Notebook marks 19.94
solved ("No, it is not true").

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
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
