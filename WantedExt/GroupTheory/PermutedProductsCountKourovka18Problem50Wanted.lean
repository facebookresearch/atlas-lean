/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Numbers of distinct permuted products (Kourovka Notebook Problem 18.50)

Kourovka Notebook, Problem 18.50 (S. Kohl), marked solved in the 21st issue: let `n ∈ ℕ`. Is it true
that for every `k ∈ {1, …, n!}` there is some group `G` and pairwise distinct `g₁, …, gₙ ∈ G` such
that the set `{g_{σ(1)} ⋯ g_{σ(n)} | σ ∈ Sₙ}` has cardinality `k`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.GroupTheory.PermutedProductsCountKourovka18Problem50Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.50 (S. Kohl). UnsolvedMath record
UM-00701479 (`KOU-18.50`), dataset ulamai/UnsolvedMath v1.8.0.

The product `g_{σ(1)} ⋯ g_{σ(n)}` is the product of `List.ofFn (g ∘ σ)`; groups are taken in `Type`.
The resolution is an AI-generated solution confirmed by S. Kohl, with an independent account by van
Doorn, Judin, Monticone and Morrison.
-/

/-- **Kohl's permuted-products statement (Kourovka 18.50).** The assertion that for all natural
numbers $n$ and $k$ with $1 \le k \le n!$ there are a group $G$ and pairwise distinct elements
$g_1, \dots, g_n \in G$ such that the set
$\lbrace g_{\sigma(1)} g_{\sigma(2)} \cdots g_{\sigma(n)} : \sigma \in S_n \rbrace$ of products
obtained by permuting the factors has exactly $k$ elements. -/
def permutedProductsTakeEveryCount : Prop :=
  ∀ n k : ℕ, 1 ≤ k → k ≤ n.factorial →
    ∃ (G : Type) (_ : Group G) (g : Fin n → G), Function.Injective g ∧
      (Set.range fun σ : Equiv.Perm (Fin n) => (List.ofFn fun i => g (σ i)).prod).ncard = k

/-- **Every number of distinct permuted products occurs (Kourovka 18.50).** For all natural
numbers $n$ and $k$ with $1 \le k \le n!$ there are a group $G$ and pairwise distinct elements
$g_1, \dots, g_n \in G$ such that the set
$\lbrace g_{\sigma(1)} g_{\sigma(2)} \cdots g_{\sigma(n)} : \sigma \in S_n \rbrace$ of products
obtained by permuting the factors has exactly $k$ elements.

The Kourovka Notebook (21st issue) answers 18.50 "Yes, it is true", by an AI-generated solution
confirmed by S. Kohl (P. Monticone, 2026); van Doorn, Judin, Monticone and Morrison (2026) give
an independent account.

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 18.50 (S. Kohl); resolution: P. Monticone, preprint, 2026 (AI solution confirmed by S.
Kohl), https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/05/18_50.pdf; W. van Doorn,
E. Judin, P. Monticone and D. Morrison, On some problems from the Kourovka Notebook, preprint,
arXiv:2607.17477 (2026), arXiv:2607.17477 abstract: for every 1 ≤ k ≤ n! there is a group containing
n distinct elements whose n! ordered products take exactly k distinct values (found and verified in
Lean by the Aristotle agent); the Kourovka Notebook (21st issue) marks 18.50 solved,
https://arxiv.org/abs/2607.17477.
-/
public theorem_wanted permutedProductsTakeEveryCount_holds : permutedProductsTakeEveryCount

end MathlibExt.GroupTheory.PermutedProductsCountKourovka18Problem50Wanted
