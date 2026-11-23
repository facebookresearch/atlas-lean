/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Large automorphisms of `p`-groups and cyclic subgroups (Kourovka Notebook Problem 15.32)

Kourovka Notebook, Problem 15.32 (Ya. G. Berkovich): does there exist a function `f(k)` (possibly
depending also on `p`) such that if a finite `p`-group `G` of order `pᵐ` with `m ≥ f(k)` has an
automorphism of order `p^(m-k)`, then `G` possesses a cyclic subgroup of index `pᵏ`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.LargeAutomorphismCyclicSubgroupKourovka15Problem32Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.32 (Ya. G. Berkovich). UnsolvedMath
record UM-00701120 (`KOU-15.32`), dataset ulamai/UnsolvedMath v1.8.0.

The function is replaced by the explicit threshold `f(k) = 64k + 2` of the resolution, which does
not depend on `p` and implies the existential reading. `m - k` is natural subtraction, harmless
since `m > k`.
-/

/-- **Kourovka Problem 15.32: large automorphisms and cyclic subgroups.** For every prime $p$ and
all natural numbers $k$ and $m$ with $m \ge 64k + 2$, every finite group $G$ of order $p^m$ that
has an automorphism of order $p^{m-k}$ has a cyclic subgroup of index $p^k$.

Kourovka 15.32 (Ya. G. Berkovich) asks for some threshold $f(k)$ beyond which this holds; the
threshold $f(k) = 64k + 2$ is the one of its resolution. -/
def cyclicSubgroupOfIndexFromLargeAutomorphism : Prop :=
  ∀ p k m : ℕ, p.Prime → 64 * k + 2 ≤ m → ∀ (G : Type) [Group G] [Finite G], Nat.card G = p ^ m →
    (∃ φ : MulAut G, orderOf φ = p ^ (m - k)) → ∃ C : Subgroup G, IsCyclic C ∧ C.index = p ^ k

/--
**Large automorphisms of p-groups force cyclic subgroups of given index.** For every prime $p$ and
all natural numbers $k$ and $m$ with $m \ge 64k + 2$, if a finite group $G$ of order $p^m$ has an
automorphism of order $p^{m-k}$, then $G$ has a cyclic subgroup of index $p^k$.

Resolved true: Jayadevan proved this with the threshold $f(k) = 64k + 2$; the Kourovka Notebook
(21st issue) marks 15.32 solved, "Yes, one can take $f(k) = 64k + 2$" (AI solution confirmed by
A. Caranti).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.32 (Ya. G.
Berkovich); resolution: A. Jayadevan, Large-order automorphisms of finite p-groups force cyclic
subgroups of prescribed index, preprint, Zenodo record 22910914 (2026), AI-generated solution
confirmed by A. Caranti, main theorem (for every k ≥ 0, a group of order p^m with m ≥ 64k + 2 and an
automorphism of order p^(m-k) has a cyclic subgroup of index exactly p^k); the Kourovka Notebook
(21st issue) marks 15.32 solved, https://zenodo.org/records/22910914.
-/
public theorem_wanted cyclicSubgroupOfIndexFromLargeAutomorphism_holds :
    cyclicSubgroupOfIndexFromLargeAutomorphism

end MathlibExt.GroupTheory.LargeAutomorphismCyclicSubgroupKourovka15Problem32Wanted
