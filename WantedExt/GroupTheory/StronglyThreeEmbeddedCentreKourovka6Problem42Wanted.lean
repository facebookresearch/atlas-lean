/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Strongly 3-embedded subgroups and central elements of order 3 (Kourovka Notebook Problem 6.42)

Kourovka Notebook, Archive of Solved Problems, Problem 6.42 (N. D. Podufalov): let H be a strongly
3-embedded subgroup of a finite group G. Suppose that Z(H/O_3'(H)) contains an element of order 3.
Does Z(G/O_3'(G)) necessarily contain an element of order 3?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.DPiHallIntersectionKourovka18Problem31Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.StronglyThreeEmbeddedCentreKourovka6Problem42Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.42 (N. D.
Podufalov). UnsolvedMath record UM-00700385 (`KOU-6.42`), dataset ulamai/UnsolvedMath v1.8.0.

A subgroup `H` of a finite group `G` is strongly `p`-embedded when `H` is proper, `p` divides `|H|`,
and `p` does not divide `|H ∩ Hᵍ|` for `g ∉ H` (the definition behind Bender's strongly embedded
subgroups, `p = 2`). `O_(3')(K)` is `piCore {p | p ≠ 3} K` of the Kourovka 18.31 module, the join of
the normal subgroups of order prime to `3`, which is the largest such subgroup of a finite group; it
is taken in `H` viewed as a group. An element of order `3` in `Z(K ⧸ O)` is stated in `K`: `h ∉ O`
with `h³ ∈ O` and `[h, k] ∈ O` for every `k ∈ K`.
-/

open MathlibExt.GroupTheory.DPiHallIntersectionKourovka18Problem31Wanted (piCore)

/-- `H` is strongly `p`-embedded in `G`: `H` is proper, `p` divides `|H|`, and `p` does not divide
`|H ∩ H^g|` for `g ∉ H`. -/
def IsStronglyEmbedded {G : Type} [Group G] (p : ℕ) (H : Subgroup G) : Prop :=
  H ≠ ⊤ ∧ p ∣ Nat.card H ∧
    ∀ g ∉ H, ¬ p ∣ Nat.card (H ⊓ H.map (MulAut.conj g).toMonoidHom : Subgroup G)

/-- `Z(K ⧸ O_(3')(K))` contains an element of order `3`, with `O_(3')(K) = piCore {p | p ≠ 3} K`
(the largest normal subgroup of order prime to `3`), stated in `K`: some `h` lies outside
`O_(3')(K)`, has `h³ ∈ O_(3')(K)`, and commutes with every element of `K` modulo `O_(3')(K)`. -/
def HasCentralOrderThree (K : Type) [Group K] : Prop :=
  ∃ h : K, h ∉ piCore {p | p ≠ 3} K ∧ h ^ 3 ∈ piCore {p | p ≠ 3} K ∧
    ∀ k : K, h * k * h⁻¹ * k⁻¹ ∈ piCore {p | p ≠ 3} K

/-- Kourovka 6.42 (N. D. Podufalov): if `H` is strongly `3`-embedded in a finite group `G` and
`Z(H ⧸ O_(3')(H))` contains an element of order `3`, then so does `Z(G ⧸ O_(3')(G))`. -/
def stronglyThreeEmbeddedCentralOrderThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), IsStronglyEmbedded 3 H →
    HasCentralOrderThree H → HasCentralOrderThree G

/--
Resolved true: the Kourovka Archive answers 6.42 "Yes, it does (mod CFSG)", citing Xiao (1990): if a
finite group `G` has a strongly `3`-embedded subgroup `H` such that `Z(H ⧸ O_(3')(H))` contains an
element of order `3`, then so does `Z(G ⧸ O_(3')(G))`. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 6.42 (N. D. Podufalov); resolution: W. Xiao, Sci. China
(A) 33 (1990), 1172-1181, Kourovka Archive, Problem 6.42: Yes, it does (mod CFSG) (Xiao),
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted stronglyThreeEmbeddedCentralOrderThree_holds :
    stronglyThreeEmbeddedCentralOrderThree

end MathlibExt.GroupTheory.StronglyThreeEmbeddedCentreKourovka6Problem42Wanted
