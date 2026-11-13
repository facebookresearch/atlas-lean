/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Element orders in extensions of `L_n(q)` (Kourovka Notebook Problem 14.60)

Kourovka Notebook, Archive of Solved Problems, Problem 14.60 (V. D. Mazurov): let `H` be a
non-trivial normal subgroup of a finite group `G` with `G / H ≅ L_n(q)`, `n ≥ 3`. Does `G` have an
element whose order is distinct from the order of every element of `G / H`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.FieldTheory.Finite.GaloisField

@[expose] public section

namespace MathlibExt.GroupTheory.PSLExtensionNewElementOrderKourovka14Problem60Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.60 (V. D.
Mazurov). UnsolvedMath record UM-00701045 (`KOU-14.60`), dataset ulamai/UnsolvedMath v1.8.0.

`L_n(q) = PSL_n(𝔽_q)` is `SL_n(𝔽_q)` modulo its centre, with `𝔽_q = GaloisField p k`, `q = pᵏ`, `k ≥
1`.
-/

/-- **Projective special linear group.** For a natural number $n$ and a field $F$,
$\mathrm{PSL}_n(F)$ is the quotient $\mathrm{SL}_n(F)/Z(\mathrm{SL}_n(F))$ of the special linear
group $\mathrm{SL}_n(F)$ of $n \times n$ matrices over $F$ with determinant $1$ by its centre. -/
abbrev PSL (n : ℕ) (F : Type) [Field F] : Type :=
  Matrix.SpecialLinearGroup (Fin n) F ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)

/-- **Kourovka 14.60: new element orders in extensions of projective special linear groups.**
The proposition that for every $n \ge 3$, every prime $p$ and every $k \ge 1$, with $q = p^k$ and
$\mathbb{F}_q$ the field with $q$ elements, the following holds: whenever $H$ is a nontrivial normal
subgroup of a finite group $G$ and $G/H$ is isomorphic to the projective special linear group
$\mathrm{PSL}_n(\mathbb{F}_q)$, some element of $G$ has an order that is not the order of any
element of $G/H$. -/
def extensionOfPSLHasNewElementOrder : Prop :=
  ∀ (n p k : ℕ) [Fact p.Prime], 3 ≤ n → 0 < k →
    ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) [H.Normal], H ≠ ⊥ →
      Nonempty (G ⧸ H ≃* PSL n (GaloisField p k)) →
      ∃ g : G, ∀ y : G ⧸ H, orderOf y ≠ orderOf g

/--
Resolved true: the Kourovka Archive answers 14.60 "Yes, it is true": Zavarnitsine proved it for `n ≠
4` and Grechkoseeva and Skresanov for `n = 4` (the editors note that an earlier claim of failure for
`n = 4` was erroneous). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 14.60 (V. D. Mazurov); resolution: A. V. Zavarnitsine, Siberian Math. J. 49 (2008), 246-256
(n ≠ 4); M. A. Grechkoseeva and S. V. Skresanov, Siberian Electron. Math. Rep. 17 (2020), 585-589 (n
= 4), Kourovka Archive, Problem 14.60 (answer: Yes, it is true; the editors note that an earlier
claim of failure for n = 4 was erroneous).
-/
public theorem_wanted extensionOfPSLHasNewElementOrder_holds : extensionOfPSLHasNewElementOrder

end MathlibExt.GroupTheory.PSLExtensionNewElementOrderKourovka14Problem60Wanted
