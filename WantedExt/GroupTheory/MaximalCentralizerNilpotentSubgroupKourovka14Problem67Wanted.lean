/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Centralizers of maximal order and normalized nilpotent subgroups (Kourovka Notebook Problem 14.67)

Kourovka Notebook, Problem 14.67 (I. T. Mukhamet'yanov, A. N. Fomin): let `a ≠ 1` in a finite group
`G` with `|C_G(a)| ≥ |C_G(x)|` for every `x ≠ 1`, and let `H` be a nilpotent subgroup normalized by
`C_G(a)`. Is `H ≤ C_G(a)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.MaximalCentralizerNilpotentSubgroupKourovka14Problem67Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.67 (I. T. Mukhamet'yanov, A. N. Fomin).
UnsolvedMath record UM-00701052 (`KOU-14.67`), dataset ulamai/UnsolvedMath v1.8.0.

`C_G(a)` is `Subgroup.centralizer {a}`; "normalized by `C_G(a)`" is `C_G(a) ≤ N_G(H)`.
-/

/-- **Mukhamet'yanov–Fomin problem on centralizers of maximal order.** For an element $x$ of a
group $G$ write $C_G(x)$ for its centralizer. This is the statement that for every finite group
$G$ and every element $a \ne 1$ of $G$ with $|C_G(x)| \le |C_G(a)|$ for every $x \ne 1$ in $G$,
every nilpotent subgroup $H$ of $G$ normalized by $C_G(a)$ (that is, $C_G(a)$ is contained in the
normalizer of $H$) is contained in $C_G(a)$.

This is Kourovka Notebook Problem 14.67 (I. T. Mukhamet'yanov, A. N. Fomin). -/
def maximalCentralizerContainsNormalizedNilpotent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a : G), a ≠ 1 →
    (∀ x : G, x ≠ 1 →
      Nat.card (Subgroup.centralizer {x}) ≤ Nat.card (Subgroup.centralizer {a})) →
    ∀ H : Subgroup G, Group.IsNilpotent H →
      Subgroup.centralizer {a} ≤ Subgroup.normalizer (H : Set G) → H ≤ Subgroup.centralizer {a}

/--
**Centralizers of maximal order need not contain normalized nilpotent subgroups.** For an element
$x$ of a group $G$ write $C_G(x)$ for its centralizer. There exist a finite group $G$, an element
$a \ne 1$ of $G$ with $|C_G(x)| \le |C_G(a)|$ for every $x \ne 1$ in $G$, and a nilpotent subgroup
$H$ of $G$ normalized by $C_G(a)$ (that is, $C_G(a)$ is contained in the normalizer of $H$) such
that $H$ is not contained in $C_G(a)$.

Jayadevan constructs a group $G$ of order $660602880$, an involution $a$ with
$|C_G(a)| = 41287680 \ge |C_G(g)|$ for every $g \ne 1$, and a nilpotent normal subgroup $H$ of
order $16384$ not contained in $C_G(a)$; the Kourovka Notebook (21st issue) answers Problem 14.67
"No, not always".

Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Problem 14.67 (I. T. Mukhamet'yanov, A. N. Fomin); resolution: A. Jayadevan, Centralizers of
maximal order and nilpotent normal subgroups, preprint, Zenodo record 22861469 (2026), main theorem:
a group of order 660602880 with an involution a and a nilpotent normal subgroup H of order 16384
such that |C_G(a)| = 41287680 ≥ |C_G(g)| for every g ≠ 1 but H is not contained in C_G(a); the
Kourovka Notebook (21st issue) marks 14.67 solved (AI solution confirmed by K. Muliarchyk),
https://zenodo.org/records/22861469.
-/
public theorem_wanted maximalCentralizerContainsNormalizedNilpotent_refuted :
    ¬ maximalCentralizerContainsNormalizedNilpotent

end MathlibExt.GroupTheory.MaximalCentralizerNilpotentSubgroupKourovka14Problem67Wanted
