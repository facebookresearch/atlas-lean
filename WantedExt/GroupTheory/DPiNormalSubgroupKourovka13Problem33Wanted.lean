/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Normal subgroups of `D_π`-groups (Kourovka Notebook Problem 13.33)

Kourovka Notebook, Archive of Solved Problems, Problem 13.33 (F. Gross; V. D. Mazurov): is a normal
subgroup of a finite `D_π`-group (see Archive, 3.62) always a `D_π`-group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace MathlibExt.GroupTheory.DPiNormalSubgroupKourovka13Problem33Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.33 (F.
Gross; V. D. Mazurov). UnsolvedMath record UM-00700951 (`KOU-13.33`), dataset ulamai/UnsolvedMath
v1.8.0.

A Hall `π`-subgroup has order a `π`-number and index a `π'`-number. `D_π` (Archive 3.62): Hall
`π`-subgroups exist, any two are conjugate, and every `π`-subgroup lies in one. `π` is an arbitrary
set of primes, given as a set of naturals (non-primes in it are irrelevant).
-/

/-- **$\pi$-numbers.** Let $\pi$ be a set of natural numbers. A natural number $n$ is a
$\pi$-number when every prime dividing $n$ lies in $\pi$. -/
def IsPiNumber (π : Set ℕ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ∈ π

/-- **Hall $\pi$-subgroups.** Let $\pi$ be a set of natural numbers. A subgroup $H$ of a group $G$
is a Hall $\pi$-subgroup when its order $|H|$ is a $\pi$-number and no prime dividing its index
$|G : H|$ lies in $\pi$. Here an infinite order or index is taken to be $0$, which every prime
divides. -/
def IsHallPiSubgroup (π : Set ℕ) {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  IsPiNumber π (Nat.card H) ∧ ∀ p : ℕ, p.Prime → p ∣ H.index → p ∉ π

/-- **$D_\pi$-groups.** Let $\pi$ be a set of natural numbers (only the primes in $\pi$ matter). A
group $G$ is a $D_\pi$-group (Kourovka Archive 3.62) when $G$ has a Hall $\pi$-subgroup, any two
Hall $\pi$-subgroups $H$ and $K$ of $G$ are conjugate ($K = gHg^{-1}$ for some $g \in G$), and every
subgroup of $G$ whose order is a $\pi$-number lies in some Hall $\pi$-subgroup. Here the order of an
infinite subgroup is taken to be $0$, which every prime divides. -/
def IsDPi (π : Set ℕ) (G : Type*) [Group G] : Prop :=
  (∃ H : Subgroup G, IsHallPiSubgroup π H) ∧
    (∀ H K : Subgroup G, IsHallPiSubgroup π H → IsHallPiSubgroup π K →
      ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom) ∧
    ∀ P : Subgroup G, IsPiNumber π (Nat.card P) → ∃ H : Subgroup G, IsHallPiSubgroup π H ∧ P ≤ H

/-- **Kourovka Problem 13.33.** This is the proposition (F. Gross) that for every set $\pi$ of
natural numbers, every normal subgroup of a finite $D_\pi$-group is itself a $D_\pi$-group. -/
def normalSubgroupOfDPiIsDPi : Prop :=
  ∀ (π : Set ℕ) (G : Type) [Group G] [Finite G], IsDPi π G →
    ∀ N : Subgroup G, N.Normal → IsDPi π N

/--
**Normal subgroups of finite $D_\pi$-groups are $D_\pi$-groups.** Kourovka Problem 13.33 has a
positive answer: for every set $\pi$ of natural numbers, every normal subgroup of a finite
$D_\pi$-group is itself a $D_\pi$-group.

The Kourovka Archive answers 13.33 "Yes, it is" modulo the classification of finite simple groups
(E. P. Vdovin and D. O. Revin, 2006).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.33 (F.
Gross; V. D. Mazurov); resolution: E. P. Vdovin and D. O. Revin, in: Ischia Group Theory 2004,
Contemp. Math. 402, Amer. Math. Soc., 2006, 229-263, Kourovka Archive, Problem 13.33: Yes, it is
mod CFSG.
-/
public theorem_wanted normalSubgroupOfDPiIsDPi_holds : normalSubgroupOfDPiIsDPi

end MathlibExt.GroupTheory.DPiNormalSubgroupKourovka13Problem33Wanted
