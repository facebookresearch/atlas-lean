/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Higman's embedding theorem for Burnside varieties (Kourovka Notebook Problem 12.32)

Kourovka Notebook, Archive of Solved Problems, Problem 12.32 (S. V. Ivanov): prove an analogue of
Higman's theorem for the Burnside variety `𝔅ₙ` of groups of odd exponent `n ≫ 1`: every recursively
presented group of exponent `n` embeds in a group of exponent `n` finitely presented in `𝔅ₙ`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.BurnsideHigmanEmbeddingKourovka12Problem32Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.32 (S. V.
Ivanov). UnsolvedMath record UM-00700851 (`KOU-12.32`), dataset ulamai/UnsolvedMath v1.8.0.

Exponent `n` is the identity `xⁿ = 1`, as in the definition of `𝔅ₙ`. A recursively presented group
is given by countably many generators `x₀, x₁, …` and a recursively enumerable set of relators
(words coded as `List (ℕ × Bool)`); this includes every finitely generated recursively presented
group. A group finitely presented in `𝔅ₙ` is `⟨x₀, …, x_{m-1} | S, wⁿ for all words w⟩` with `S`
finite, so it has exponent `n`. "`n ≫ 1`" is read as "every odd `n ≥ n₀`, for some `n₀`".
-/

/-- **Groups finitely presented in a Burnside variety.** For natural numbers $n$ and $m$ and a
finite set $S$ of elements of the free group on $x_0, \dots, x_{m-1}$, this is the group with
generators $x_0, \dots, x_{m-1}$ and relators $S$ together with $w^n$ for every element $w$ of the
free group: the group finitely presented by $S$ in the Burnside variety $\mathfrak{B}_n$ of groups
of exponent $n$. -/
abbrev BurnsidePresented (n m : ℕ) (S : Finset (FreeGroup (Fin m))) : Type :=
  PresentedGroup ((S : Set (FreeGroup (Fin m))) ∪ Set.range fun w : FreeGroup (Fin m) => w ^ n)

/-- **Kourovka Problem 12.32: Higman embedding for Burnside varieties.** There is $n_0$ such that
for every odd $n \ge n_0$ the following holds. Let $G$ be a group given by generators
$x_0, x_1, \dots$ and a recursively enumerable set of relators, and suppose that $g^n = 1$ for
every $g \in G$. Then for some $m$ and some finite set $S$ of elements of the free group on
$x_0, \dots, x_{m-1}$, there is an injective homomorphism from $G$ to the group finitely presented
by $S$ in the Burnside variety $\mathfrak{B}_n$, whose relators are $S$ together with $w^n$ for
every element $w$ of that free group.

The relators are words in the generators, and recursive enumerability refers to these words. -/
def higmanEmbeddingBurnsideVariety : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Odd n → ∀ R : Set (List (ℕ × Bool)), REPred (· ∈ R) →
    (∀ g : PresentedGroup (FreeGroup.mk '' R), g ^ n = 1) →
    ∃ (m : ℕ) (S : Finset (FreeGroup (Fin m)))
      (f : PresentedGroup (FreeGroup.mk '' R) →* BurnsidePresented n m S), Function.Injective f

/-- **Higman embedding theorem for Burnside varieties.** There is $n_0$ such that for every odd
$n \ge n_0$, every group of exponent $n$ given by generators $x_0, x_1, \dots$ and a recursively
enumerable set of relators embeds in a group finitely presented in the Burnside variety
$\mathfrak{B}_n$: a group with generators $x_0, \dots, x_{m-1}$ for some $m$ whose relators are a
finite set $S$ together with $w^n$ for every word $w$.

Olshanskii proves this with the ambient group 2-generated; the statement here does not require it.

Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.32 (S. V. Ivanov); resolution: A.
Yu. Olshanskii, Groups finitely presented in Burnside varieties, J. Algebra 560 (2020), 960-1052,
Theorem 1.1 (finitely generated groups) and Corollary 1.2 (countably many generators; the ambient
group can be taken 2-generated), for all odd n ≥ C; Kourovka Archive, Problem 12.32.
-/
public theorem_wanted higmanEmbeddingBurnsideVariety_holds : higmanEmbeddingBurnsideVariety

end MathlibExt.GroupTheory.BurnsideHigmanEmbeddingKourovka12Problem32Wanted
