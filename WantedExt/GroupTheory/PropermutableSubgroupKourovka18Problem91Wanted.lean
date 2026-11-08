/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Propermutable subgroups (Kourovka Notebook Problem 18.91)

Kourovka Notebook, Archive of Solved Problems, Problem 18.91 (A. N. Skiba): `H ≤ G` is propermutable
in `G` if there is `B ≤ G` with `G = N_G(H) B` such that `H` permutes with every subgroup of `B`.
(a) Is there a finite group `G` with subgroups `A ≤ B ≤ G` such that `A` is propermutable in `G` but
not in `B`? (b) Let `P` be a non-abelian Sylow 2-subgroup of a finite group `G` with `|P| = 2ⁿ`.
Suppose that there is an integer `k` such that `1 < k < n` and every subgroup of `P` of order `2ᵏ`
is propermutable in `G`, and also, in the case of `k = 1`, every cyclic subgroup of `P` of order `4`
is propermutable in `G`. Is it true that then `G` is 2-nilpotent?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace MathlibExt.GroupTheory.PropermutableSubgroupKourovka18Problem91Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.91 (A. N.
Skiba). UnsolvedMath record UM-00701520 (`KOU-18.91`), dataset ulamai/UnsolvedMath v1.8.0.

`H` permutes with `X` when `HX = XH` as sets. In (b) the printed range `1 < k < n` contradicts the
clause for `k = 1`; the target uses `1 ≤ k < n`, i.e. `1 < 2ᵏ < |P|`, the range of Al-Sharo's
Corollary 1.3, which the paper says answers 18.91(b) (the literal range `1 < k` is the special case
`k ≥ 2`). 2-nilpotent means a normal subgroup of odd order with 2-power index.
-/

open scoped Pointwise

/-- `H` permutes with `X`: `HX = XH` as sets. -/
def Permutes {G : Type} [Group G] (H X : Subgroup G) : Prop :=
  (H : Set G) * (X : Set G) = (X : Set G) * (H : Set G)

/-- `H` is propermutable in `G`: there is a subgroup `B` with `G = N_G(H) B` such that `H` permutes
with every subgroup of `B`. -/
def IsPropermutable {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∃ B : Subgroup G, (Subgroup.normalizer (H : Set G) : Set G) * (B : Set G) = Set.univ ∧
    ∀ X : Subgroup G, X ≤ B → Permutes H X

/-- `G` is 2-nilpotent: it has a normal subgroup of odd order whose index is a power of `2`. -/
def IsTwoNilpotent (G : Type) [Group G] : Prop :=
  ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧ ∃ k : ℕ, N.index = 2 ^ k

/-- Kourovka 18.91(a) (A. N. Skiba): there are a finite group `G` and subgroups `A ≤ B ≤ G` such
that `A` is propermutable in `G` but not in `B`. -/
def propermutableNotInIntermediate : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G) (A B : Subgroup G),
    A ≤ B ∧ IsPropermutable A ∧ ¬ IsPropermutable (A.subgroupOf B)

/-- Kourovka 18.91(b) (A. N. Skiba): let `P` be a non-abelian Sylow 2-subgroup of a finite group
`G`, `|P| = 2ⁿ`, and let `1 ≤ k < n`. If every subgroup of `P` of order `2ᵏ` is propermutable in
`G`, and, when `k = 1`, every cyclic subgroup of `P` of order `4` is propermutable in `G`, then `G`
is 2-nilpotent. -/
def propermutableSylowSubgroupsTwoNilpotent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 2 G),
    (∃ x ∈ (P : Subgroup G), ∃ y ∈ (P : Subgroup G), x * y ≠ y * x) →
    ∀ k : ℕ, 1 ≤ k → 2 ^ k < Nat.card (P : Subgroup G) →
      (∀ H : Subgroup G, H ≤ P → Nat.card H = 2 ^ k → IsPropermutable H) →
      (k = 1 → ∀ H : Subgroup G, H ≤ P → IsCyclic H → Nat.card H = 4 → IsPropermutable H) →
      IsTwoNilpotent G

/--
Resolved true: the Kourovka Archive answers 18.91(a) "Yes, there is" (A. A. Pypka and D. Yu.
Storozhenko, 2017). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 18.91 (A. N. Skiba); resolution: (a) A. A. Pypka and D. Yu. Storozhenko, Dopov. Nac. Akad.
Nauk Ukrain. 2017, no. 7, 18-20 (Ukrainian); (b) Kh. A. Al-Sharo, Finite groups with given systems
of weakly S-propermutable subgroups, J. Group Theory 19 (2016), no. 5, 871-887, Kourovka Archive,
Problem 18.91: a) Yes, there is; b) Yes, it is. Al-Sharo, Corollary 1.3: if X ⊴ G, P ∈ Syl_p(X), (p
- 1, |X|) = 1, and for some 1 < D < P every subgroup of P of order |D| (and, when P is non-abelian
and |D| = 2, every cyclic subgroup of order 4) is S-propermutable in G, then X is p-nilpotent,
https://doi.org/10.1515/jgth-2016-0017.
-/
public theorem_wanted propermutableNotInIntermediate_holds : propermutableNotInIntermediate

/--
Resolved true: the Kourovka Archive answers 18.91(b) "Yes, it is" (Kh. A. Al-Sharo, 2016). Corollary
1.3 of Al-Sharo with `X = G` and `p = 2` (where `(p - 1, |G|) = 1`) gives 2-nilpotency already when
the subgroups in question are `S`-propermutable (permuting with the Sylow subgroups of `B`), a
weaker condition than propermutability. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 18.91 (A. N. Skiba); resolution: (a) A. A. Pypka and D. Yu. Storozhenko,
Dopov. Nac. Akad. Nauk Ukrain. 2017, no. 7, 18-20 (Ukrainian); (b) Kh. A. Al-Sharo, Finite groups
with given systems of weakly S-propermutable subgroups, J. Group Theory 19 (2016), no. 5, 871-887,
Kourovka Archive, Problem 18.91: a) Yes, there is; b) Yes, it is. Al-Sharo, Corollary 1.3: if X ⊴ G,
P ∈ Syl_p(X), (p - 1, |X|) = 1, and for some 1 < D < P every subgroup of P of order |D| (and, when P
is non-abelian and |D| = 2, every cyclic subgroup of order 4) is S-propermutable in G, then X is
p-nilpotent, https://doi.org/10.1515/jgth-2016-0017.
-/
public theorem_wanted propermutableSylowSubgroupsTwoNilpotent_holds :
    propermutableSylowSubgroupsTwoNilpotent

end MathlibExt.GroupTheory.PropermutableSubgroupKourovka18Problem91Wanted
