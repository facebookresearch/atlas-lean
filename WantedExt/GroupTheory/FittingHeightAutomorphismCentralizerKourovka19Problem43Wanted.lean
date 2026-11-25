/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fitting height bounded by an automorphism and its centralizer (Kourovka Notebook Problem 19.43)

Kourovka Notebook, Problem 19.43 (E. I. Khukhro), marked solved in the 21st issue: suppose that `φ`
is an automorphism of a finite soluble group `G`. Is the Fitting height of `G` bounded in terms of
`|φ|` and `|C_G(φ)|`?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.FittingHeightAutomorphismCentralizerKourovka19Problem43Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.43 (E. I. Khukhro). UnsolvedMath record
UM-00701591 (`KOU-19.43`), dataset ulamai/UnsolvedMath v1.8.0.

The Fitting height of a finite soluble group is the least length of a normal series with nilpotent
factors; "at most `h`" is stated as the existence of such a series of length `h`, nilpotency of a
factor `G_{i+1} / G_i` as `γ_c(G_{i+1}) ≤ G_i` for some `c`. `|φ|` is `orderOf φ` in `MulAut G` and
`C_G(φ)` the fixed points of `φ`. `FittingHeightLE` is the shared definition in
`WantedExt/GroupTheory/KourovkaNotebookShared.lean`.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared

/-- **Kourovka Problem 19.43: Fitting height, automorphism order and centralizer size.** The
statement that there is a function $f$ assigning a natural number $f(m, n)$ to every pair of
natural numbers $m$, $n$ such that every finite soluble group $G$ with an automorphism $\varphi$
has Fitting height at most $f(|\varphi|, |C_G(\varphi)|)$, where $|\varphi|$ is the order of
$\varphi$ and $|C_G(\varphi)|$ is the number of elements of $G$ fixed by $\varphi$.

The problem was posed by E. I. Khukhro. -/
def fittingHeightBoundedByOrderAndCentralizer : Prop :=
  ∃ f : ℕ → ℕ → ℕ, ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → ∀ φ : MulAut G,
    FittingHeightLE G (f (orderOf φ) (Nat.card {g : G // φ g = g}))

/--
**Fitting height is bounded by the order of an automorphism and its centralizer.** There is a
function $f$ assigning a natural number $f(m, n)$ to every pair of natural numbers $m$, $n$ such
that every finite soluble group $G$ with an automorphism $\varphi$ has Fitting height at most
$f(|\varphi|, |C_G(\varphi)|)$, where $|\varphi|$ is the order of $\varphi$ and $|C_G(\varphi)|$ is
the number of elements of $G$ fixed by $\varphi$.

This answers Kourovka Problem 19.43 (E. I. Khukhro) affirmatively: Khukhro proved the bound, and the
21st issue of the Kourovka Notebook marks 19.43 solved ("Yes, it is").

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.43 (E. I. Khukhro);
resolution: E. Khukhro, Bull. London Math. Soc. 58 (2026), no. 1, Article ID e70206, the Kourovka
Notebook (21st issue) marks 19.43 solved: Yes, it is, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted fittingHeightBoundedByOrderAndCentralizer_holds :
    fittingHeightBoundedByOrderAndCentralizer

end MathlibExt.GroupTheory.FittingHeightAutomorphismCentralizerKourovka19Problem43Wanted
