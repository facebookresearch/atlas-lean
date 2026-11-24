/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Maximal class-size p-parts and normal p-complements (Kourovka Notebook Problem 20.27)

Kourovka Notebook, Problem 20.27 (I. B. Gorshkov), marked solved in the 21st issue: let `G` be a
finite group, `p` a prime number, and let `|x^G|_p` denote the maximum power of `p` that divides the
class size of an element `x ∈ G`. Suppose that there exists a `p`-element `g ∈ G` such that `|g^G|_p
= max_{x ∈ G} |x^G|_p`. Is it true that `G` has a normal `p`-complement?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace MathlibExt.GroupTheory.MaximalClassSizePElementNormalComplementKourovka20Problem27Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.27 (I. B. Gorshkov). UnsolvedMath record
UM-00701685 (`KOU-20.27`), dataset ulamai/UnsolvedMath v1.8.0.

A `p`-element is a `g` with `g ^ p ^ k = 1` for some `k`; `|x^G|_p` is `ordProj[p]` of the size of
the conjugacy class of `x`; "`|g^G|_p` is the maximum" is `|x^G|_p ≤ |g^G|_p` for every `x`. A
normal `p`-complement is a normal subgroup that is a complement of a Sylow `p`-subgroup
(`Subgroup.IsComplement'`, the form of Mathlib's Burnside normal `p`-complement theorem
`MonoidHom.ker_transferSylow_isComplement'`). Groups are in `Type`.
-/

/-- **Groups with a normal p-complement.** A group $G$ has a normal $p$-complement when it has a
normal subgroup $N$ and a Sylow $p$-subgroup $P$ that are complements of each other: every element
of $G$ can be written uniquely as $nq$ with $n \in N$ and $q \in P$. -/
def HasNormalPComplement (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ (N : Subgroup G) (P : Sylow p G), N.Normal ∧ N.IsComplement' P

/-- **Gorshkov's problem on maximal p-parts of class sizes.** For a prime $p$, the $p$-part of a
positive integer $m$ is the largest power of $p$ dividing $m$. This is the statement that for
every finite group $G$, every prime $p$ and every $p$-element $g$ of $G$ (that is, $g^{p^k} = 1$
for some natural number $k$), if for every $x \in G$ the $p$-part of the size of the conjugacy
class of $x$ is at most the $p$-part of the size of the conjugacy class of $g$, then $G$ has a
normal $p$-complement.

This is Kourovka Notebook Problem 20.27 (I. B. Gorshkov). -/
def maximalClassSizePElementGivesNormalComplement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ g : G, (∃ k : ℕ, g ^ p ^ k = 1) →
    (∀ x : G, ordProj[p] (Nat.card (ConjClasses.mk x).carrier) ≤
      ordProj[p] (Nat.card (ConjClasses.mk g).carrier)) →
    HasNormalPComplement p G

/--
**A maximal p-part of a class size does not force a normal p-complement.** For a prime $p$, the
$p$-part of a positive integer $m$ is the largest power of $p$ dividing $m$. There exist a finite
group $G$, a prime $p$ and a $p$-element $g$ of $G$ (that is, $g^{p^k} = 1$ for some natural
number $k$) such that for every $x \in G$ the $p$-part of the size of the conjugacy class of $x$
is at most the $p$-part of the size of the conjugacy class of $g$, but $G$ has no normal
$p$-complement.

Sambale's counterexample is the group $\mathrm{SL}(2, 3) \rtimes Q_8$ of order $192$ (number $945$
in the GAP library of small groups) with $p = 2$. In it an element of order $4$ has class size
$24$, whose $2$-part $8$ is the largest $2$-part of a class size, while the eight elements of
order $3$ form one conjugacy class, so there is no normal subgroup of order $3$, that is, no
normal $2$-complement.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.27 (I. B. Gorshkov); resolution: B.
Sambale, letter of 16 February 2022, recorded in the Kourovka Notebook (21st issue), Problem 20.27:
"No, not necessarily, a counterexample is given by SmallGroup(192,945)",
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted maximalClassSizePElementGivesNormalComplement_refuted :
    ¬ maximalClassSizePElementGivesNormalComplement

end MathlibExt.GroupTheory.MaximalClassSizePElementNormalComplementKourovka20Problem27Wanted
