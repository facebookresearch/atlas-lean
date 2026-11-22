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

/-- `n` is a `π`-number: every prime divisor of `n` lies in `π`. -/
def IsPiNumber (π : Set ℕ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ∈ π

/-- `H` is a Hall `π`-subgroup of the finite group `G`: `|H|` is a `π`-number and `|G : H|` is a
`π'`-number. -/
def IsHallPiSubgroup (π : Set ℕ) {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  IsPiNumber π (Nat.card H) ∧ ∀ p : ℕ, p.Prime → p ∣ H.index → p ∉ π

/-- `H` is a maximal `π`-subgroup: a `π`-subgroup contained in no larger `π`-subgroup. -/
def IsMaximalPiSubgroup (π : Set ℕ) {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  IsPiNumber π (Nat.card H) ∧ ∀ L : Subgroup G, H ≤ L → IsPiNumber π (Nat.card L) → L = H

/-- `G` is a `C_π`-group: it has exactly one conjugacy class of Hall `π`-subgroups. -/
def IsCPiGroup (π : Set ℕ) (G : Type*) [Group G] : Prop :=
  (∃ H : Subgroup G, IsHallPiSubgroup π H) ∧ ∀ H K : Subgroup G, IsHallPiSubgroup π H →
    IsHallPiSubgroup π K → ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom

/-- `G` is a `D_π`-group: any two maximal `π`-subgroups of `G` are conjugate. -/
def IsDPiGroup (π : Set ℕ) (G : Type*) [Group G] : Prop :=
  ∀ H K : Subgroup G, IsMaximalPiSubgroup π H → IsMaximalPiSubgroup π K →
    ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom

/-- Kourovka 17.44(a) (E. P. Vdovin, D. O. Revin): in a finite `C_π`-group, every subgroup
containing a Hall `π`-subgroup is a `C_π`-group. -/
def hallOvergroupCPi : Prop :=
  ∀ (π : Set ℕ) (G : Type) [Group G] [Finite G], IsCPiGroup π G →
    ∀ H K : Subgroup G, IsHallPiSubgroup π H → H ≤ K → IsCPiGroup π K

/-- Kourovka 17.44(b) (E. P. Vdovin, D. O. Revin): in a finite `D_π`-group, every subgroup
containing a Hall `π`-subgroup is a `D_π`-group. -/
def hallOvergroupDPi : Prop :=
  ∀ (π : Set ℕ) (G : Type) [Group G] [Finite G], IsDPiGroup π G →
    ∀ H K : Subgroup G, IsHallPiSubgroup π H → H ≤ K → IsDPiGroup π K

/--
Resolved true: the Kourovka Archive answers 17.44(a) "Yes, it is", citing Vdovin and Revin (2013):
in a finite `C_π`-group every subgroup containing a Hall `π`-subgroup is a `C_π`-group. Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.44 (E. P. Vdovin, D. O.
Revin); resolution: (a) E. P. Vdovin and D. O. Revin, Siberian Math. J. 54 (2013), 22-28; (b) N. Ch.
Manzaeva, preprint, arXiv:1504.03137, and E. P. Vdovin, N. Ch. Manzaeva and D. O. Revin, Sb. Math.
211 (2020), 309-335, Kourovka Archive, Problem 17.44 (a) Yes, it is; b) Yes, it is),
https://arxiv.org/abs/1504.03137.
-/
public theorem_wanted hallOvergroupCPi_holds : hallOvergroupCPi

/--
Resolved true: the Kourovka Archive answers 17.44(b) "Yes, it is", citing Manzaeva
(arXiv:1504.03137) and Vdovin, Manzaeva and Revin (2020): in a finite `D_π`-group every subgroup
containing a Hall `π`-subgroup is a `D_π`-group. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 17.44 (E. P. Vdovin, D. O. Revin); resolution: (a) E. P. Vdovin
and D. O. Revin, Siberian Math. J. 54 (2013), 22-28; (b) N. Ch. Manzaeva, preprint,
arXiv:1504.03137, and E. P. Vdovin, N. Ch. Manzaeva and D. O. Revin, Sb. Math. 211 (2020), 309-335,
Kourovka Archive, Problem 17.44 (a) Yes, it is; b) Yes, it is), https://arxiv.org/abs/1504.03137.
-/
public theorem_wanted hallOvergroupDPi_holds : hallOvergroupDPi

end MathlibExt.GroupTheory.HallOvergroupCPiDPiKourovka17Problem44Wanted
