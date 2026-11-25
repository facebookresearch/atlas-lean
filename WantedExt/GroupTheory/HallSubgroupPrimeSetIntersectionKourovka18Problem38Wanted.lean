/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hall subgroups for intersections of prime sets (Kourovka Notebook Problem 18.38)

Kourovka Notebook, Problem 18.38 (A. V. Zavarnitsine), marked solved in the 21st issue: let `E_π`
denote the class of finite groups that contain a Hall `π`-subgroup. Does the inclusion `E_{π₁} ∩
E_{π₂} ⊆ E_{π₁ ∩ π₂}` hold for arbitrary sets of primes `π₁` and `π₂`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace MathlibExt.GroupTheory.HallSubgroupPrimeSetIntersectionKourovka18Problem38Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.38 (A. V. Zavarnitsine). UnsolvedMath
record UM-00701467 (`KOU-18.38`), dataset ulamai/UnsolvedMath v1.8.0.

A Hall `π`-subgroup has order whose prime divisors lie in `π` and index with no prime divisor in
`π`; sets of primes are subsets of `ℕ` (non-primes in them are ignored).
-/

/-- **π-numbers.** Let $\pi$ be a set of natural numbers. A natural number $n$ is a $\pi$-number
when every prime divisor of $n$ lies in $\pi$. -/
def IsPiNumber (π : Set ℕ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ∈ π

/-- **Hall π-subgroups.** Let $\pi$ be a set of natural numbers and let $H$ be a subgroup of a
group $G$. Then $H$ is a Hall $\pi$-subgroup when its order $|H|$ is a $\pi$-number and no prime
divisor of its index $|G : H|$ lies in $\pi$. -/
def IsHallPiSubgroup {G : Type} [Group G] (π : Set ℕ) (H : Subgroup G) : Prop :=
  IsPiNumber π (Nat.card H) ∧ ∀ p : ℕ, p.Prime → p ∣ H.index → p ∉ π

/-- **The class $E_\pi$ of groups with a Hall π-subgroup.** Let $\pi$ be a set of natural numbers.
A group $G$ belongs to the class $E_\pi$ when $G$ has a Hall $\pi$-subgroup. -/
def HasHallPiSubgroup (π : Set ℕ) (G : Type) [Group G] : Prop :=
  ∃ H : Subgroup G, IsHallPiSubgroup π H

/-- **Zavarnitsine's question on Hall subgroups for intersections of prime sets.** This is the
statement that for all sets $\pi_1$ and $\pi_2$ of natural numbers, every finite group that has a
Hall $\pi_1$-subgroup and a Hall $\pi_2$-subgroup also has a Hall $(\pi_1 \cap \pi_2)$-subgroup;
that is, writing $E_\pi$ for the class of finite groups with a Hall $\pi$-subgroup,
$E_{\pi_1} \cap E_{\pi_2}$ is contained in $E_{\pi_1 \cap \pi_2}$.

This is Kourovka Notebook Problem 18.38 (A. V. Zavarnitsine). -/
def hallSubgroupForIntersectionOfPrimeSets : Prop :=
  ∀ (π₁ π₂ : Set ℕ) (G : Type) [Group G] [Finite G],
    HasHallPiSubgroup π₁ G → HasHallPiSubgroup π₂ G → HasHallPiSubgroup (π₁ ∩ π₂) G

/-- **Hall subgroups exist for intersections of prime sets.** For all sets $\pi_1$ and $\pi_2$ of
natural numbers, every finite group that has a Hall $\pi_1$-subgroup and a Hall $\pi_2$-subgroup
also has a Hall $(\pi_1 \cap \pi_2)$-subgroup; that is, writing $E_\pi$ for the class of finite
groups with a Hall $\pi$-subgroup, $E_{\pi_1} \cap E_{\pi_2}$ is contained in
$E_{\pi_1 \cap \pi_2}$.

This answers Kourovka Notebook Problem 18.38 (A. V. Zavarnitsine) in the affirmative; the 21st
issue records the answer "Yes, it does" (N. Yang and A. A. Buturlakin, 2025).

Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 18.38 (A. V. Zavarnitsine); resolution: N. Yang and A. A.
Buturlakin, A generalization of the Arad-Ward theorem on Hall subgroups, preprint, arXiv:2501.05865
(2025), abstract: E_{π₁} ∩ E_{π₂} is contained in E_{π₁ ∩ π₂}; the Kourovka Notebook (21st issue)
marks 18.38 solved, https://arxiv.org/abs/2501.05865.
-/
public theorem_wanted hallSubgroupForIntersectionOfPrimeSets_holds :
    hallSubgroupForIntersectionOfPrimeSets

end MathlibExt.GroupTheory.HallSubgroupPrimeSetIntersectionKourovka18Problem38Wanted
