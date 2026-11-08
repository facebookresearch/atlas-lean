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

/-- `n` is a `π`-number: all its prime divisors lie in `π`. -/
def IsPiNumber (π : Set ℕ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ∈ π

/-- `H` is a Hall `π`-subgroup: `|H|` is a `π`-number and `|G : H|` is a `π'`-number. -/
def IsHallPiSubgroup (π : Set ℕ) {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  IsPiNumber π (Nat.card H) ∧ ∀ p : ℕ, p.Prime → p ∣ H.index → p ∉ π

/-- `G` is a `D_π`-group (Kourovka Archive 3.62): `G` has a Hall `π`-subgroup, any two Hall
`π`-subgroups are conjugate, and every `π`-subgroup lies in some Hall `π`-subgroup. -/
def IsDPi (π : Set ℕ) (G : Type*) [Group G] : Prop :=
  (∃ H : Subgroup G, IsHallPiSubgroup π H) ∧
    (∀ H K : Subgroup G, IsHallPiSubgroup π H → IsHallPiSubgroup π K →
      ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom) ∧
    ∀ P : Subgroup G, IsPiNumber π (Nat.card P) → ∃ H : Subgroup G, IsHallPiSubgroup π H ∧ P ≤ H

/-- Kourovka 13.33 (F. Gross): every normal subgroup of a finite `D_π`-group is a
`D_π`-group. -/
def normalSubgroupOfDPiIsDPi : Prop :=
  ∀ (π : Set ℕ) (G : Type) [Group G] [Finite G], IsDPi π G →
    ∀ N : Subgroup G, N.Normal → IsDPi π N

/--
Resolved true: the Kourovka Archive answers 13.33 "Yes, it is" modulo the classification of finite
simple groups (E. P. Vdovin and D. O. Revin, 2006). Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 13.33 (F. Gross; V. D. Mazurov); resolution: E. P. Vdovin and D.
O. Revin, in: Ischia Group Theory 2004, Contemp. Math. 402, Amer. Math. Soc., 2006, 229-263,
Kourovka Archive, Problem 13.33: Yes, it is mod CFSG.
-/
public theorem_wanted normalSubgroupOfDPiIsDPi_holds : normalSubgroupOfDPiIsDPi

end MathlibExt.GroupTheory.DPiNormalSubgroupKourovka13Problem33Wanted
