/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Number of finite groups with a given spectrum (Kourovka Notebook Problem 13.63)

Kourovka Notebook, Archive of Solved Problems, Problem 13.63 (W. J. Shi): for `Γ ⊆ ℕ` let `h(Γ)` be
the number of non-isomorphic finite groups `G` with `π_e(G) = Γ`. Is there `k` such that for every
`Γ` either `h(Γ) ≤ k` or `h(Γ) = ∞`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.ElementOrderSpectrumCountKourovka13Problem63Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.63 (W. J.
Shi). UnsolvedMath record UM-00700981 (`KOU-13.63`), dataset ulamai/UnsolvedMath v1.8.0.

`π_e(G)` is the set of element orders. `h(Γ) ≤ k` is stated as "among any `k + 1` finite groups with
spectrum `Γ` two are isomorphic" and `h(Γ) = ∞` as "for every `n` there are `n` pairwise
non-isomorphic finite groups with spectrum `Γ`", which avoids counting isomorphism classes directly.
-/

/-- **Spectrum of a group (Kourovka 13.63).** For a group $G$, the spectrum $\pi_e(G)$ is the set
of orders of elements of $G$, where an element of infinite order counts as having order $0$. -/
def elementOrders (G : Type*) [Group G] : Set ℕ :=
  Set.range (orderOf : G → ℕ)

/-- **At most $k$ isomorphism types with spectrum $\Gamma$.** For a set $\Gamma$ of natural numbers
and a natural number $k$, this property holds when, for any finite groups $G_0, \dots, G_k$ (not
necessarily distinct) whose spectra $\pi_e(G_i)$ (the sets of orders of elements of $G_i$) all
equal $\Gamma$, there are indices $i \ne j$ with $G_i \cong G_j$.

This expresses $h(\Gamma) \le k$, where $h(\Gamma)$ is the number of isomorphism classes of finite
groups with spectrum $\Gamma$, without counting isomorphism classes directly. -/
def AtMostIsoClasses (Γ : Set ℕ) (k : ℕ) : Prop :=
  ∀ (G : Fin (k + 1) → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)],
    (∀ i, elementOrders (G i) = Γ) → ∃ i j, i ≠ j ∧ Nonempty (G i ≃* G j)

/-- **Infinitely many isomorphism types with spectrum $\Gamma$.** For a set $\Gamma$ of natural
numbers, this property holds when, for every natural number $n$, there are $n$ pairwise
non-isomorphic finite groups $G_0, \dots, G_{n-1}$ whose spectra $\pi_e(G_i)$ (the sets of orders
of elements of $G_i$) all equal $\Gamma$.

This expresses $h(\Gamma) = \infty$, where $h(\Gamma)$ is the number of isomorphism classes of
finite groups with spectrum $\Gamma$. -/
def InfinitelyManyIsoClasses (Γ : Set ℕ) : Prop :=
  ∀ n : ℕ, ∃ (G : Fin n → Type) (_ : ∀ i, Group (G i)) (_ : ∀ i, Finite (G i)),
    (∀ i, elementOrders (G i) = Γ) ∧ ∀ i j, i ≠ j → IsEmpty (G i ≃* G j)

/-- **Kourovka Problem 13.63 (bounded or infinite number of groups per spectrum).** The proposition,
asked about by W. J. Shi, that there is a natural number $k$ such that for every set $\Gamma$ of
natural numbers, either $h(\Gamma) \le k$ or $h(\Gamma) = \infty$, where $h(\Gamma)$ is the number
of isomorphism classes of finite groups $G$ whose spectrum $\pi_e(G)$ (set of element orders) is
$\Gamma$. Here $h(\Gamma) \le k$ means that among any $k + 1$ finite groups with spectrum $\Gamma$
two are isomorphic, and $h(\Gamma) = \infty$ means that for every $n$ there are $n$ pairwise
non-isomorphic finite groups with spectrum $\Gamma$. -/
def spectrumGroupCountBoundedOrInfinite : Prop :=
  ∃ k : ℕ, ∀ Γ : Set ℕ, AtMostIsoClasses Γ k ∨ InfinitelyManyIsoClasses Γ

/--
**No uniform bound on the number of groups with a given spectrum.** For a set $\Gamma$ of natural
numbers, let $h(\Gamma)$ be the number of isomorphism classes of finite groups $G$ whose spectrum
$\pi_e(G)$ (set of element orders) is $\Gamma$; $h(\Gamma) \le k$ means that among any $k + 1$
finite groups with spectrum $\Gamma$ two are isomorphic, and $h(\Gamma) = \infty$ means that for
every $n$ there are $n$ pairwise non-isomorphic finite groups with spectrum $\Gamma$. Kourovka
Problem 13.63 has a negative answer: there is no natural number $k$ such that for every set
$\Gamma$ of natural numbers, either $h(\Gamma) \le k$ or $h(\Gamma) = \infty$.

Zavarnitsine proves $h(\pi_e(L_3(7^{3^r}))) = r + 1$ for every $r \ge 0$, where $L_3(q)$ is the
projective special linear group $\mathrm{PSL}_3(q)$, so $h$ takes every positive finite value and
no $k$ works.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.63
(W. J. Shi); resolution: A. V. Zavarnitsine, J. Group Theory 7 (2004), no. 1, 81-97,
h(π_e(L_3(7^(3^r)))) = r + 1 for every r ≥ 0; Kourovka Archive, Problem 13.63 (answer: No, there is
no such number).
-/
public theorem_wanted spectrumGroupCountBoundedOrInfinite_refuted :
    ¬ spectrumGroupCountBoundedOrInfinite

end MathlibExt.GroupTheory.ElementOrderSpectrumCountKourovka13Problem63Wanted
