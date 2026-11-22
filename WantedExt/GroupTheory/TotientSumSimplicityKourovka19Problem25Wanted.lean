/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Order and totient sum do not determine simplicity (Kourovka Notebook Problem 19.25)

Kourovka Notebook, Problem 19.25 (B. Curtin, G. R. Pourgholi), marked solved in the 21st issue: let
`G` and `H` be finite groups of the same order with `∑_{g ∈ G} φ(|g|) = ∑_{h ∈ H} φ(|h|)`, where `φ`
is Euler's totient function. Suppose that `G` is simple. Is `H` necessarily simple?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.TotientSumSimplicityKourovka19Problem25Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.25 (B. Curtin, G. R. Pourgholi).
UnsolvedMath record UM-00701573 (`KOU-19.25`), dataset ulamai/UnsolvedMath v1.8.0.

Groups are finite types (`Fintype`) and `|g|` is `orderOf g`; simplicity is Mathlib's
`IsSimpleGroup` (nontrivial, only trivial normal subgroups). The refutation is one explicit pair of
groups of order 6048, whose verification needs the simplicity of `PSU(3, 3)` and is not a decision
procedure on a small object.
-/

/-- Kourovka 19.25 (B. Curtin, G. R. Pourgholi): if finite groups `G` and `H` have the same order
and the same totient sum `∑_{g ∈ G} φ(|g|) = ∑_{h ∈ H} φ(|h|)`, and `G` is simple, then `H` is
simple. -/
def sameOrderTotientSumSimple : Prop :=
  ∀ (G H : Type) [Group G] [Group H] [Fintype G] [Fintype H],
    Fintype.card G = Fintype.card H →
    ∑ g : G, Nat.totient (orderOf g) = ∑ h : H, Nat.totient (orderOf h) →
    IsSimpleGroup G → IsSimpleGroup H

/--
Resolved false: `G = PSU(3, 3)` (simple, order 6048) and `H = C₆ × S₄ × F`, with `F` the Frobenius
group of order 42, have the same order and the same totient sum 23984, and `H` is not simple (van
Doorn, Judin, Monticone and Morrison, Theorem 4.1). The solution was found by the AI system
Aristotle, which also verified it in Lean, and Monticone's note confirms it in GAP; the 21st issue
of the Kourovka Notebook accepts it and marks 19.25 solved ("No, it need not be"). Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 19.25 (B. Curtin, G. R. Pourgholi); resolution: P.
Monticone, Kourovka Notebook Problem 19.25, solution note (2026); W. van Doorn, E. Judin, P.
Monticone and D. Morrison, On Some Problems from the Kourovka Notebook, preprint, arXiv:2607.17477
(2026), Section 4, Theorem 4.1 with Lemma 4.2 (G = PSU(3, 3) is simple, by Iwasawa's criterion, of
order 6048 with totient sum 23984) and Lemma 4.3 (H = C₆ × S₄ × F, F the Frobenius group of order
42, has the same order and totient sum and is not simple); the solution was found and verified in
Lean by the AI system Aristotle (abstract and Appendix A); the Kourovka Notebook (21st issue) marks
19.25 solved: No, it need not be (AI solution confirmed by GAP), https://arxiv.org/abs/2607.17477.
-/
public theorem_wanted sameOrderTotientSumSimple_refuted : ¬ sameOrderTotientSumSimple

end MathlibExt.GroupTheory.TotientSumSimplicityKourovka19Problem25Wanted
