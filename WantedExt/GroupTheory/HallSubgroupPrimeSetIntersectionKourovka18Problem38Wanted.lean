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

/-- `n` is a `π`-number: every prime divisor of `n` lies in `π`. -/
def IsPiNumber (π : Set ℕ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ∈ π

/-- `H` is a Hall `π`-subgroup: `|H|` is a `π`-number and `|G : H|` has no prime divisor in `π`. -/
def IsHallPiSubgroup {G : Type} [Group G] (π : Set ℕ) (H : Subgroup G) : Prop :=
  IsPiNumber π (Nat.card H) ∧ ∀ p : ℕ, p.Prime → p ∣ H.index → p ∉ π

/-- `G ∈ E_π`: `G` has a Hall `π`-subgroup. -/
def HasHallPiSubgroup (π : Set ℕ) (G : Type) [Group G] : Prop :=
  ∃ H : Subgroup G, IsHallPiSubgroup π H

/-- Kourovka 18.38 (A. V. Zavarnitsine): `E_{π₁} ∩ E_{π₂} ⊆ E_{π₁ ∩ π₂}` for all sets of primes
`π₁`, `π₂`, that is, a finite group with a Hall `π₁`-subgroup and a Hall `π₂`-subgroup has a Hall
`(π₁ ∩ π₂)`-subgroup. -/
def hallSubgroupForIntersectionOfPrimeSets : Prop :=
  ∀ (π₁ π₂ : Set ℕ) (G : Type) [Group G] [Finite G],
    HasHallPiSubgroup π₁ G → HasHallPiSubgroup π₂ G → HasHallPiSubgroup (π₁ ∩ π₂) G

/--
Resolved true: the Kourovka Notebook (21st issue) answers 18.38 "Yes, it does" (Buturlakin-Yang,
2025), whose abstract states that `E_{π₁} ∩ E_{π₂}` is contained in `E_{π₁ ∩ π₂}`. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 18.38 (A. V. Zavarnitsine); resolution: N. Yang and A. A.
Buturlakin, A generalization of the Arad-Ward theorem on Hall subgroups, preprint, arXiv:2501.05865
(2025), abstract: E_{π₁} ∩ E_{π₂} is contained in E_{π₁ ∩ π₂}; the Kourovka Notebook (21st issue)
marks 18.38 solved, https://arxiv.org/abs/2501.05865.
-/
public theorem_wanted hallSubgroupForIntersectionOfPrimeSets_holds :
    hallSubgroupForIntersectionOfPrimeSets

end MathlibExt.GroupTheory.HallSubgroupPrimeSetIntersectionKourovka18Problem38Wanted
