/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Overgroups of Hall subgroups in `C_π`- and `D_π`-groups (Kourovka Notebook Problem 17.44)

Kourovka Notebook, Archive of Solved Problems, Problem 17.44 (E. P. Vdovin, D. O. Revin): let `π` be
a set of primes. A finite group is a `C_π`-group if it possesses exactly one class of conjugate Hall
`π`-subgroups, and a `D_π`-group if any two of its maximal `π`-subgroups are conjugate. a) In a
`C_π`-group, is an overgroup of a Hall `π`-subgroup always a `C_π`-group? b) In a `D_π`-group, is an
overgroup of a Hall `π`-subgroup always a `D_π`-group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace MathlibExt.GroupTheory.HallOvergroupCPiDPiKourovka17Problem44Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.44 (E. P.
Vdovin, D. O. Revin). UnsolvedMath record UM-00701346 (`KOU-17.44`), dataset ulamai/UnsolvedMath
v1.8.0.

`π : Set ℕ` (only its primes matter). A Hall `π`-subgroup has `π`-number order and `π'`-number
index; a maximal `π`-subgroup is a `π`-subgroup contained in no larger one. A `C_π`-group has a Hall
`π`-subgroup and all of them are conjugate. Overgroups are subgroups `K ≥ H` viewed as groups, with
conjugacy inside `K`. One target per part.
-/

/-- **$\pi$-number.** Let $\pi$ be a set of natural numbers (only the primes in it matter). A
natural number $n$ is a $\pi$-number when every prime divisor of $n$ lies in $\pi$. -/
def IsPiNumber (π : Set ℕ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ∈ π

/-- **Hall $\pi$-subgroup.** Let $\pi$ be a set of natural numbers and $G$ a group. A subgroup $H$
of $G$ is a Hall $\pi$-subgroup when its order $|H|$ is a $\pi$-number and no prime divisor of its
index $|G : H|$ lies in $\pi$.

An infinite order or index counts as $0$; the notion is meant for finite groups. -/
def IsHallPiSubgroup (π : Set ℕ) {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  IsPiNumber π (Nat.card H) ∧ ∀ p : ℕ, p.Prime → p ∣ H.index → p ∉ π

/-- **Maximal $\pi$-subgroup.** Let $\pi$ be a set of natural numbers and $G$ a group. A subgroup
$H$ of $G$ is a maximal $\pi$-subgroup when its order $|H|$ is a $\pi$-number and every subgroup $L$
of $G$ that contains $H$ and whose order is a $\pi$-number equals $H$.

An infinite order counts as $0$; the notion is meant for finite groups. -/
def IsMaximalPiSubgroup (π : Set ℕ) {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  IsPiNumber π (Nat.card H) ∧ ∀ L : Subgroup G, H ≤ L → IsPiNumber π (Nat.card L) → L = H

/-- **$C_\pi$-group.** Let $\pi$ be a set of natural numbers. A group $G$ is a $C_\pi$-group when it
has a Hall $\pi$-subgroup and any two Hall $\pi$-subgroups $H$ and $K$ of $G$ are conjugate, that
is, $K = gHg^{-1}$ for some $g \in G$. -/
def IsCPiGroup (π : Set ℕ) (G : Type*) [Group G] : Prop :=
  (∃ H : Subgroup G, IsHallPiSubgroup π H) ∧ ∀ H K : Subgroup G, IsHallPiSubgroup π H →
    IsHallPiSubgroup π K → ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom

/-- **$D_\pi$-group.** Let $\pi$ be a set of natural numbers. A group $G$ is a $D_\pi$-group when
any two maximal $\pi$-subgroups $H$ and $K$ of $G$ are conjugate, that is, $K = gHg^{-1}$ for
some $g \in G$. -/
def IsDPiGroup (π : Set ℕ) (G : Type*) [Group G] : Prop :=
  ∀ H K : Subgroup G, IsMaximalPiSubgroup π H → IsMaximalPiSubgroup π K →
    ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom

/-- **Kourovka Problem 17.44(a): overgroups of Hall subgroups in $C_\pi$-groups.** The statement,
posed by E. P. Vdovin and D. O. Revin, that for every set $\pi$ of natural numbers and every finite
$C_\pi$-group $G$, every subgroup $K$ of $G$ that contains a Hall $\pi$-subgroup of $G$ is itself a
$C_\pi$-group. -/
def hallOvergroupCPi : Prop :=
  ∀ (π : Set ℕ) (G : Type) [Group G] [Finite G], IsCPiGroup π G →
    ∀ H K : Subgroup G, IsHallPiSubgroup π H → H ≤ K → IsCPiGroup π K

/-- **Kourovka Problem 17.44(b): overgroups of Hall subgroups in $D_\pi$-groups.** The statement,
posed by E. P. Vdovin and D. O. Revin, that for every set $\pi$ of natural numbers and every finite
$D_\pi$-group $G$, every subgroup $K$ of $G$ that contains a Hall $\pi$-subgroup of $G$ is itself a
$D_\pi$-group. -/
def hallOvergroupDPi : Prop :=
  ∀ (π : Set ℕ) (G : Type) [Group G] [Finite G], IsDPiGroup π G →
    ∀ H K : Subgroup G, IsHallPiSubgroup π H → H ≤ K → IsDPiGroup π K

/--
**Overgroups of Hall subgroups in $C_\pi$-groups (Vdovin–Revin).** Let $\pi$ be a set of natural
numbers and let $G$ be a finite $C_\pi$-group. Then every subgroup $K$ of $G$ that contains a Hall
$\pi$-subgroup of $G$ is itself a $C_\pi$-group. This answers Kourovka Problem 17.44(a) in the
affirmative.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.44 (E. P.
Vdovin, D. O. Revin); resolution: (a) E. P. Vdovin and D. O. Revin, Siberian Math. J. 54 (2013),
22-28; (b) N. Ch. Manzaeva, preprint, arXiv:1504.03137, and E. P. Vdovin, N. Ch. Manzaeva and D. O.
Revin, Sb. Math. 211 (2020), 309-335, Kourovka Archive, Problem 17.44 (a) Yes, it is; b) Yes, it
is), https://arxiv.org/abs/1504.03137.
-/
public theorem_wanted hallOvergroupCPi_holds : hallOvergroupCPi

/--
**Overgroups of Hall subgroups in $D_\pi$-groups (Manzaeva, Vdovin–Manzaeva–Revin).** Let $\pi$ be
a set of natural numbers and let $G$ be a finite $D_\pi$-group. Then every subgroup $K$ of $G$ that
contains a Hall $\pi$-subgroup of $G$ is itself a $D_\pi$-group. This answers Kourovka Problem
17.44(b) in the affirmative.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.44 (E. P.
Vdovin, D. O. Revin); resolution: (a) E. P. Vdovin and D. O. Revin, Siberian Math. J. 54 (2013),
22-28; (b) N. Ch. Manzaeva, preprint, arXiv:1504.03137, and E. P. Vdovin, N. Ch. Manzaeva and D. O.
Revin, Sb. Math. 211 (2020), 309-335, Kourovka Archive, Problem 17.44 (a) Yes, it is; b) Yes, it
is), https://arxiv.org/abs/1504.03137.
-/
public theorem_wanted hallOvergroupDPi_holds : hallOvergroupDPi

end MathlibExt.GroupTheory.HallOvergroupCPiDPiKourovka17Problem44Wanted
