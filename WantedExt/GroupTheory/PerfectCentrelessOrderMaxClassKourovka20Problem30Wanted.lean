/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Perfect centreless groups and the largest conjugacy class (Kourovka Notebook Problem 20.30)

Kourovka Notebook, Problem 20.30 (P. M. Neumann and M. R. Vaughan-Lee; I. B. Gorshkov), marked
solved in the 21st issue: let `G` be a perfect and centreless finite group, and let `n` be the
maximum size of a conjugacy class in `G`. Is it true that `|G| ≤ n²`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.IsPerfect

@[expose] public section

namespace MathlibExt.GroupTheory.PerfectCentrelessOrderMaxClassKourovka20Problem30Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.30 (P. M. Neumann and M. R. Vaughan-Lee;
I. B. Gorshkov). UnsolvedMath record UM-00701688 (`KOU-20.30`), dataset ulamai/UnsolvedMath v1.8.0.

Perfect is Mathlib's `Group.IsPerfect G` (`commutator G = ⊤`), centreless is `Subgroup.center G =
⊥`; the class of `x` is `conjugatesOf x`. Since `n = |x^G|` for some `x`, the inequality `|G| ≤ n²`
is stated as `|G| ≤ |x^G|²` for some `x ∈ G`.
-/

/-- **Kourovka 20.30: the order of a perfect centreless group and its largest conjugacy class.**
The proposition that every finite group $G$ that is perfect ($[G, G] = G$) and has trivial centre
contains an element $x$ with $|G| \le |x^G|^2$, where $x^G$ is the conjugacy class of $x$.
Equivalently, $|G| \le n^2$, where $n$ is the largest size of a conjugacy class of $G$. -/
def perfectCentrelessOrderLeMaxClassSq : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsPerfect G → Subgroup.center G = ⊥ →
    ∃ x : G, Nat.card G ≤ (conjugatesOf x).ncard ^ 2

/--
**Perfect centreless groups need not have order at most the square of the largest class size.**
It is not true that every finite group $G$ that is perfect ($[G, G] = G$) and has trivial centre
contains an element $x$ with $|G| \le |x^G|^2$, where $x^G$ is the conjugacy class of $x$. That
is, some perfect centreless finite group $G$ satisfies $|G| > n^2$, where $n$ is the largest size
of a conjugacy class of $G$.

Muliarchyk (Theorem 1.1) constructs a perfect centreless finite group of order $120 \cdot 5^{68}$
whose largest conjugacy class has size $30 \cdot 5^{32}$, so $|G| / n^2 = 250/3 > 1$; the 21st
issue of the Kourovka Notebook marks 20.30 solved ("No, not always"). The preprint acknowledges
assistance from ChatGPT.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.30 (P. M. Neumann
and M. R. Vaughan-Lee; I. B. Gorshkov); resolution: K. Muliarchyk, Perfect centreless groups with
large centralizers, preprint (2026), Kourovka Notebook site, Theorem 1.1: an explicit perfect
centreless finite group of order 120·5^68 whose largest conjugacy class has size 30·5^32, so |G|/n²
= 250/3 > 1 (built from a class-three Baker-Campbell-Hausdorff group over F₅ and an SL₂(F₅)-action);
Theorem 6.1: no bound |G| ≤ C n^c holds for all perfect centreless finite groups; Kourovka Notebook
(21st issue), Problem 20.30: No, not always,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_20_30_solution.pdf.
-/
public theorem_wanted perfectCentrelessOrderLeMaxClassSq_refuted :
    ¬ perfectCentrelessOrderLeMaxClassSq

end MathlibExt.GroupTheory.PerfectCentrelessOrderMaxClassKourovka20Problem30Wanted
