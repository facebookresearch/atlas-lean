/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# `F*`-groups with the minimal condition for subgroups (Kourovka Notebook Problem 7.42)

Kourovka Notebook, Archive of Solved Problems, Problem 7.42 (A. N. Ostylovskiĭ): (a) is every
primary `F*`-group with the minimal condition for subgroups almost abelian? (b) does every
`F*`-group with the minimal condition for (abelian) subgroups possess a radicable part?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.FStarGroupMinimalConditionKourovka7Problem42Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.42 (A. N.
Ostylovskiĭ). UnsolvedMath record UM-00700439 (`KOU-7.42`), dataset ulamai/UnsolvedMath v1.8.0.

`F_q`- and `F*`-groups follow the definition quoted in the problem (V. P. Shunkov); `π(H)` is the
set of primes that are orders of elements of `H`. The minimal condition is `WellFoundedLT (Subgroup
U)`. In (b) the hypothesis is the minimal condition for all subgroups: it implies the condition for
abelian subgroups, so its refutation is the stronger statement, and the counterexample satisfies it.
"Possesses the radicable part" is read as having a radicable abelian subgroup of finite index
(Chernikov's radicable part).
-/

/-- The quotient `N_U(K)/K` of the normalizer of a subgroup `K` by `K`. -/
abbrev NormalizerQuotient {U : Type*} [Group U] (K : Subgroup U) : Type _ :=
  Subgroup.normalizer (K : Set U) ⧸ K.subgroupOf (Subgroup.normalizer (K : Set U))

/-- `U` is an `F_q`-group: for every finite subgroup `K` and any two elements `a`, `b` of order
`q` in `N_U(K)/K` there is `c` in `N_U(K)/K` with `⟨a, c⁻¹ b c⟩` finite. -/
def IsFq (q : ℕ) (U : Type*) [Group U] : Prop :=
  ∀ K : Subgroup U, (K : Set U).Finite → ∀ a b : NormalizerQuotient K, orderOf a = q →
    orderOf b = q → ∃ c : NormalizerQuotient K,
      (Subgroup.closure {a, c⁻¹ * b * c} : Set (NormalizerQuotient K)).Finite

/-- `U` is an `F*`-group (V. P. Shunkov): every subgroup `H` of `U` is an `F_q`-group for every
prime `q ∈ π(H)`, that is, for every prime `q` that is the order of an element of `H`. -/
def IsFStar (U : Type*) [Group U] : Prop :=
  ∀ H : Subgroup U, ∀ q : ℕ, q.Prime → (∃ h : H, orderOf h = q) → IsFq q H

/-- `U` is primary: it is a `p`-group for some prime `p`. -/
def IsPrimary (U : Type*) [Group U] : Prop :=
  ∃ p : ℕ, p.Prime ∧ IsPGroup p U

/-- `U` is almost abelian: some abelian subgroup has finite index. -/
def IsAlmostAbelian (U : Type*) [Group U] : Prop :=
  ∃ A : Subgroup U, A.FiniteIndex ∧ ∀ x ∈ A, ∀ y ∈ A, x * y = y * x

/-- `U` possesses a radicable part: some abelian subgroup `A` of finite index is radicable, that
is, every element of `A` has an `n`-th root in `A` for every `n ≥ 1`. -/
def HasRadicablePart (U : Type*) [Group U] : Prop :=
  ∃ A : Subgroup U, A.FiniteIndex ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
    ∀ x ∈ A, ∀ n : ℕ, 0 < n → ∃ y ∈ A, y ^ n = x

/-- Kourovka 7.42(a): every primary `F*`-group with the minimal condition for subgroups (no
infinite strictly descending chain of subgroups) is almost abelian. -/
def primaryFStarMinimalAlmostAbelian : Prop :=
  ∀ (U : Type) [Group U], IsPrimary U → IsFStar U → WellFoundedLT (Subgroup U) →
    IsAlmostAbelian U

/-- Kourovka 7.42(b): every `F*`-group with the minimal condition for subgroups possesses a
radicable part. -/
def fStarMinimalHasRadicablePart : Prop :=
  ∀ (U : Type) [Group U], IsFStar U → WellFoundedLT (Subgroup U) → HasRadicablePart U

/--
Resolved false: the Kourovka Archive answers 7.42(a) No. For every large prime `p`, Ol'shanskiĭ's
infinite group all of whose proper nontrivial subgroups are conjugate and of order `p` is a
`p`-group, an `F*`-group (any two subgroups of order `p` are conjugate, and a subgroup of order `p`
is self-normalizing), and satisfies the minimal condition, but every proper subgroup is finite, so
no abelian subgroup has finite index. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 7.42 (A. N. Ostylovskiĭ); resolution: A. Yu. Ol'shanskiĭ, An infinite group
with subgroups of prime orders, Izv. Akad. Nauk SSSR Ser. Mat. 44 (1980), 309-321; Math. USSR-Izv.
16 (1981), 279-289, main theorem; Kourovka Archive, Problem 7.42.
-/
public theorem_wanted primaryFStarMinimalAlmostAbelian_refuted : ¬ primaryFStarMinimalAlmostAbelian

/--
Resolved false: the Kourovka Archive answers 7.42(b) No with the same group: it is an `F*`-group
with the minimal condition for subgroups and has no abelian subgroup of finite index at all, so no
radicable one. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
7.42 (A. N. Ostylovskiĭ); resolution: A. Yu. Ol'shanskiĭ, An infinite group with subgroups of prime
orders, Izv. Akad. Nauk SSSR Ser. Mat. 44 (1980), 309-321; Math. USSR-Izv. 16 (1981), 279-289, main
theorem; Kourovka Archive, Problem 7.42.
-/
public theorem_wanted fStarMinimalHasRadicablePart_refuted : ¬ fStarMinimalHasRadicablePart

end MathlibExt.GroupTheory.FStarGroupMinimalConditionKourovka7Problem42Wanted
