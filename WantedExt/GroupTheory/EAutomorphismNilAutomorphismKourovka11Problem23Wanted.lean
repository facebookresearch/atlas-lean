/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# e-automorphisms and nil-automorphisms (Kourovka Notebook Problem 11.23)

Kourovka Notebook, Problem 11.23 (V. G. Vilyatser): an automorphism `φ` of a group `G` is a
nil-automorphism if every `a ∈ G` has `[a, ₙ φ] = 1` for some `n`, and an `e`-automorphism if for
any `φ`-invariant subgroups `A ⊄ B` some `a ∈ A \ B` has `[a, φ] ∈ B`. Is every `e`-automorphism a
nil-automorphism?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.EAutomorphismNilAutomorphismKourovka11Problem23Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.23 (V. G. Vilyatser). UnsolvedMath
record UM-00700716 (`KOU-11.23`), dataset ulamai/UnsolvedMath v1.8.0.

`[a, φ] = a⁻¹ φ(a)` and `[a, ₙ φ]` is its `n`-th iterate, as in the source and the resolving
preprint. `φ`-invariant means `φ(A) = A`, written `φ x ∈ A ↔ x ∈ A` for every `x` (for an
automorphism of finite order, such as the order-4 counterexample, `φ(A) ⊆ A` already implies
`φ(A) = A`). No normality or index condition is imposed on `A` or `B`.
-/

/-- **The commutator of an element with an automorphism.** For an automorphism $\varphi$ of a
group $G$ and $x \in G$, $\delta_\varphi(x) = x^{-1} \varphi(x)$. This is the commutator
$[x, \varphi]$ in the Kourovka convention $[x, y] = x^{-1} y^{-1} x y$, with $\varphi$ acting as
$x \mapsto \varphi(x)$; the iterates $\delta_\varphi^n(x)$ are the iterated commutators
$[x, {}_n \varphi]$, with $[x, {}_0 \varphi] = x$. -/
def delta {G : Type*} [Group G] (φ : MulAut G) (x : G) : G := x⁻¹ * φ x

/-- **Nil-automorphisms.** An automorphism $\varphi$ of a group $G$ is a nil-automorphism if for
every $a \in G$ there is $n \ge 0$ with $\delta_\varphi^n(a) = 1$, where
$\delta_\varphi(x) = x^{-1} \varphi(x)$; that is, some iterated commutator $[a, {}_n \varphi]$ is
trivial. -/
def IsNilAutomorphism {G : Type*} [Group G] (φ : MulAut G) : Prop :=
  ∀ a : G, ∃ n : ℕ, (delta φ)^[n] a = 1

/-- **$e$-automorphisms.** An automorphism $\varphi$ of a group $G$ is an $e$-automorphism if for
any two subgroups $A$ and $B$ of $G$ with $\varphi(A) = A$, $\varphi(B) = B$ and
$A \not\subseteq B$, some $a \in A \setminus B$ has $[a, \varphi] = a^{-1} \varphi(a) \in B$. -/
def IsEAutomorphism {G : Type*} [Group G] (φ : MulAut G) : Prop :=
  ∀ A B : Subgroup G, (∀ x, φ x ∈ A ↔ x ∈ A) → (∀ x, φ x ∈ B ↔ x ∈ B) → ¬ A ≤ B →
    ∃ a ∈ A, a ∉ B ∧ delta φ a ∈ B

/-- **Vilyatser's question on $e$-automorphisms (Kourovka 11.23).** The proposition that every
$e$-automorphism $\varphi$ of a group $G$ is a nil-automorphism of $G$. -/
def eAutomorphismIsNil : Prop :=
  ∀ (G : Type) [Group G] (φ : MulAut G), IsEAutomorphism φ → IsNilAutomorphism φ

/--
**An $e$-automorphism need not be a nil-automorphism.** Vilyatser's assertion in Kourovka
Problem 11.23 is false: there are a group $G$ and an automorphism $\varphi$ of $G$ that is an
$e$-automorphism (for any subgroups $A$ and $B$ of $G$ with $\varphi(A) = A$, $\varphi(B) = B$ and
$A \not\subseteq B$, some $a \in A \setminus B$ has $a^{-1} \varphi(a) \in B$) but not a
nil-automorphism: writing $\delta(x) = x^{-1} \varphi(x)$, some $a \in G$ has $\delta^n(a) \ne 1$
for every $n \ge 0$.

Muliarchyk shows that the cyclic shift of order four on the fourth direct power of the first
Grigorchuk group is such an automorphism, using Bartholdi's characterization of the Engel elements
of the Grigorchuk group; the preprint states that the work was carried out with assistance from
ChatGPT. The Kourovka Notebook (21st issue) marks 11.23 solved, "No, not every".

Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Problem 11.23 (V. G. Vilyatser); resolution: K. Muliarchyk, An e-automorphism that is not a
nil-automorphism, preprint (2026), main theorem: the cyclic shift
`(g₀, g₁, g₂, g₃) ↦ (g₁, g₂, g₃, g₀)` on `Γ⁴`, `Γ` the first Grigorchuk group, is an
`e`-automorphism of order four and not a nil-automorphism; the Kourovka Notebook (21st issue) marks
11.23 solved,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_11_23_solution.pdf.
-/
public theorem_wanted eAutomorphismIsNil_refuted : ¬ eAutomorphismIsNil

end MathlibExt.GroupTheory.EAutomorphismNilAutomorphismKourovka11Problem23Wanted
