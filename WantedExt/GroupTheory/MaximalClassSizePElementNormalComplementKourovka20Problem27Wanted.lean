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

/-- `G` has a normal `p`-complement: a normal subgroup that is a complement of a Sylow
`p`-subgroup. -/
def HasNormalPComplement (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ (N : Subgroup G) (P : Sylow p G), N.Normal ∧ N.IsComplement' P

/-- Kourovka 20.27 (I. B. Gorshkov): if a `p`-element `g` of a finite group `G` has
`|g^G|_p = max_{x ∈ G} |x^G|_p`, then `G` has a normal `p`-complement. -/
def maximalClassSizePElementGivesNormalComplement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ g : G, (∃ k : ℕ, g ^ p ^ k = 1) →
    (∀ x : G, ordProj[p] (Nat.card (ConjClasses.mk x).carrier) ≤
      ordProj[p] (Nat.card (ConjClasses.mk g).carrier)) →
    HasNormalPComplement p G

/--
Resolved false: the Kourovka Notebook answers 20.27 "No, not necessarily": Sambale's counterexample
is `SmallGroup(192, 945)` (`SL(2, 3) ⋊ Q₈`) with `p = 2`. In it an element of order `4` has class
size `24`, whose `2`-part `8` is the largest `2`-part of a class size, while the eight elements of
order `3` form one conjugacy class, so there is no normal subgroup of order `3`, that is, no normal
`2`-complement (class data from the degree-16 permutation representation of LMFDB group 192.945).
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.27 (I. B. Gorshkov); resolution: B.
Sambale, letter of 16 February 2022, recorded in the Kourovka Notebook (21st issue), Problem 20.27:
"No, not necessarily, a counterexample is given by SmallGroup(192,945)",
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted maximalClassSizePElementGivesNormalComplement_refuted :
    ¬ maximalClassSizePElementGivesNormalComplement

end MathlibExt.GroupTheory.MaximalClassSizePElementNormalComplementKourovka20Problem27Wanted
