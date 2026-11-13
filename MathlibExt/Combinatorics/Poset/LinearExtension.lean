/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Extension.Linear

@[expose] public section

/-!
# Linear extensions of finite posets

All linear extensions of a finite poset, represented as bijective monotone
rank functions into `Fin (Fintype.card α)`. Every finite poset has a linear
extension (Szpilrajn), so the family is nonempty and its cardinality is a
valid denominator. Also provides maximal elements of a finset.
-/

namespace FinPoset

/-- **Linear extensions of a finite poset.** Let $\alpha$ be a finite poset with $n$
elements. Its linear extensions are represented as rank functions: the set of linear
extensions of $\alpha$ is the finite set of all maps $\sigma : \alpha \to \{0, 1, \dots, n-1\}$
that are bijective and monotone, meaning that $x \le y$ implies $\sigma(x) \le \sigma(y)$. -/
noncomputable def linearExtensions (α : Type*) [Fintype α] [PartialOrder α] :
    Finset (α → Fin (Fintype.card α)) := by
  classical
  exact Finset.univ.filter fun σ => Function.Bijective σ ∧ Monotone σ

/-- **Membership in the linear extensions.** Let $\alpha$ be a finite poset with $n$
elements. A map $\sigma : \alpha \to \{0, 1, \dots, n-1\}$ belongs to the set of linear
extensions of $\alpha$ if and only if $\sigma$ is bijective and monotone. -/
theorem mem_linearExtensions (α : Type*) [Fintype α] [PartialOrder α]
    (σ : α → Fin (Fintype.card α)) :
    σ ∈ linearExtensions α ↔ Function.Bijective σ ∧ Monotone σ := by
  simp only [linearExtensions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Ranking a Szpilrajn linear extension.** Let $\alpha$ be a finite poset with $n$
elements, and fix a linear order on $\alpha$ extending its partial order (one exists by
Szpilrajn's extension theorem; it is chosen once and for all). This is the order
isomorphism from $\alpha$ with that linear order onto $\{0, 1, \dots, n-1\}$ with its usual
order. -/
noncomputable def linExtOrderIso (α : Type*) [Fintype α] [PartialOrder α] :
    LinearExtension α ≃o Fin (Fintype.card α) := by
  have : Fintype (LinearExtension α) := inferInstanceAs (Fintype α)
  have hcard : Fintype.card (LinearExtension α) = Fintype.card α :=
    Fintype.card_congr (Equiv.refl α : α ≃ LinearExtension α)
  exact (Fintype.orderIsoFinOfCardEq (LinearExtension α) rfl).symm.trans
    (Fin.castOrderIso hcard)

/-- **A chosen linear extension.** Let $\alpha$ be a finite poset with $n$ elements, and
fix a linear order on $\alpha$ extending its partial order (one exists by Szpilrajn's
extension theorem; it is chosen once and for all). The chosen linear extension of
$\alpha$ is the rank function $\alpha \to \{0, 1, \dots, n-1\}$ sending each element to its
position in that linear order, counted from $0$. -/
noncomputable def someLinearExtension (α : Type*) [Fintype α] [PartialOrder α] :
    α → Fin (Fintype.card α) := fun x =>
  linExtOrderIso α (toLinearExtension x)

/-- **The chosen linear extension is bijective.** For every finite poset $\alpha$ with
$n$ elements, the chosen linear extension of $\alpha$, viewed as a rank function
$\alpha \to \{0, 1, \dots, n-1\}$, is a bijection. -/
theorem bijective_someLinearExtension (α : Type*) [Fintype α] [PartialOrder α] :
    Function.Bijective (someLinearExtension α) :=
  (linExtOrderIso α).toEquiv.bijective

/-- **The chosen linear extension is monotone.** For every finite poset $\alpha$ with
$n$ elements, the chosen linear extension of $\alpha$, viewed as a rank function
$\sigma : \alpha \to \{0, 1, \dots, n-1\}$, is monotone: $x \le y$ implies
$\sigma(x) \le \sigma(y)$. -/
theorem monotone_someLinearExtension (α : Type*) [Fintype α] [PartialOrder α] :
    Monotone (someLinearExtension α) := fun _ _ h =>
  (linExtOrderIso α).monotone (toLinearExtension.monotone' h)

/-- Every finite poset has a linear extension. -/
theorem nonempty_linearExtensions (α : Type*) [Fintype α] [PartialOrder α] :
    (linearExtensions α).Nonempty :=
  ⟨someLinearExtension α, by
    rw [mem_linearExtensions]
    exact ⟨bijective_someLinearExtension α, monotone_someLinearExtension α⟩⟩

/-- **The number of linear extensions is positive.** For every finite poset $\alpha$,
the number of linear extensions of $\alpha$ is positive.

So this count is a valid denominator for probabilities over linear extensions. -/
theorem card_linearExtensions_pos (α : Type*) [Fintype α] [PartialOrder α] :
    0 < (linearExtensions α).card :=
  Finset.card_pos.mpr (nonempty_linearExtensions α)

/-- **Maximal elements of a finite set.** For a finite subset $A$ of a partially ordered
set $P$, the maximal elements of $A$ form the subset of those $x \in A$ such that every
$y \in A$ with $x \le y$ equals $x$. -/
noncomputable def maximalElements {P : Type*} [PartialOrder P]
    (A : Finset P) : Finset P := by
  classical
  exact A.filter fun x ↦ ∀ y ∈ A, x ≤ y → y = x

/-- **Membership in the maximal elements.** Let $A$ be a finite subset of a partially
ordered set $P$ and let $x \in P$. Then $x$ belongs to the set of maximal elements of $A$
if and only if $x \in A$ and every $y \in A$ with $x \le y$ equals $x$. -/
theorem mem_maximalElements {P : Type*} [PartialOrder P] (A : Finset P)
    (x : P) : x ∈ maximalElements A ↔ x ∈ A ∧ ∀ y ∈ A, x ≤ y → y = x := by
  simp only [maximalElements, Finset.mem_filter]

end FinPoset
