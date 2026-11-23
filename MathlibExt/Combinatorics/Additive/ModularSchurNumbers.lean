/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Modular generalizations of Schur numbers

Statements from Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62.

Following Chappelon, Revuelta Marchena, and Sanz Domínguez (*Modular Schur numbers*,
Electron. J. Combin. 20(2) (2013), #P61, reference [4] of the paper), a set `A` of integers is
`l`-sum-free modulo `m` if it contains no elements `x_1, …, x_l, y` (repetitions allowed) with
`x_1 + ⋯ + x_l ≡ y (mod m)`, and the generalized Schur number modulo `m`, `S_m(k, l)`, is the
largest `n` such that `{1, …, n}` admits a partition into `k` (possibly empty) classes that are
`l`-sum-free modulo `m`. Partitions are encoded as colorings by `Fin k`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Sum-free sets modulo $m$.** For natural numbers $m$ and $l$, a set $A$ of integers is
$l$-sum-free modulo $m$ if there are no $x_1, \dots, x_l, y \in A$ (repetitions allowed) with
$x_1 + \dots + x_l \equiv y \pmod{m}$.

Source: J. Chappelon, M. P. Revuelta Marchena, M. I. Sanz Domínguez, *Modular Schur numbers*,
Electron. J. Combin. 20(2) (2013), Section 1.1, as used in Jourdan D'orville, Kai An Sim,
Kok Bin Wong, and Chee Kit Ho, *Modular Generalizations of Schur Numbers*, INTEGERS 25 (2025),
Article A62, Section 1. -/
def IsSumFreeMod (m l : ℕ) (A : Set ℤ) : Prop :=
  ∀ x : Fin l → ℤ, (∀ i, x i ∈ A) → ∀ y ∈ A, ¬ (∑ i, x i ≡ y [ZMOD m])

/-- **Sum-free partitions modulo $m$.** For natural numbers $m$, $k$, $l$ and $n$, the range
$\{1, \dots, n\}$ admits a partition into $k$ classes that are $l$-sum-free modulo $m$ if there
is a coloring $c$ of the natural numbers with $k$ colors such that, for each color $j$, the set
of integers $a$ with $1 \le a \le n$ and $c(a) = j$ is $l$-sum-free modulo $m$. Classes may be
empty; for $k = 0$ there is no coloring, so the property fails for every $n$, including $n = 0$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Section 1. -/
def HasSumFreePartitionMod (m k l n : ℕ) : Prop :=
  ∃ c : ℕ → Fin k, ∀ j : Fin k,
    IsSumFreeMod m l {x : ℤ | ∃ a : ℕ, 1 ≤ a ∧ a ≤ n ∧ c a = j ∧ x = a}

/-- **Modular Schur number.** For natural numbers $m$, $k$ and $l$, the generalized Schur number
modulo $m$, written $S_m(k, l)$, is the largest natural number $n$ such that $\{1, \dots, n\}$
admits a partition into $k$ (possibly empty) classes that are each $l$-sum-free modulo $m$; it is
$0$ when there is no largest such $n$.

For $m \ge 1$ and $k \ge 1$ such a largest $n$ exists, since $n = 0$ is admissible and every
admissible $n$ is at most $m - 1$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Section 1. -/
noncomputable def modularSchurNumber (m k l : ℕ) : ℕ :=
  sSup {n : ℕ | HasSumFreePartitionMod m k l n}

/-- **The empty range has a sum-free partition.** For all natural numbers $m$, $l$ and
$k \ge 1$, the empty range $\{1, \dots, 0\}$ admits a partition into $k$ classes that are
$l$-sum-free modulo $m$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Section 1
(`0 ≤ S_m(k, l)`). -/
theorem hasSumFreePartitionMod_zero (m k l : ℕ) : HasSumFreePartitionMod m (k + 1) l 0 := by
  refine ⟨fun _ => 0, fun j x _ y hy => ?_⟩
  obtain ⟨a, h1, h2, -⟩ := hy
  omega

/-- **Sets containing a multiple of the modulus are not sum-free.** Let $m$ and $l$ be natural
numbers and let $A$ be a set of integers. If $A$ contains an integer $a$ divisible by $m$, then
$A$ is not $l$-sum-free modulo $m$: the sum of $l$ copies of $a$ is congruent to $a$ modulo $m$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Section 1
(the bound `S_m(k, l) ≤ m - 1`). -/
theorem not_isSumFreeMod_of_dvd_mem (m l : ℕ) {A : Set ℤ} {a : ℤ} (ha : a ∈ A)
    (hm : (m : ℤ) ∣ a) : ¬ IsSumFreeMod m l A := by
  intro h
  refine h (fun _ => a) (fun _ => ha) a ha ?_
  rw [Int.modEq_iff_dvd]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : a - (l : ℤ) * a = (1 - l) * a := by ring
  rw [this]
  exact dvd_mul_of_dvd_right hm _

/-- **$\{1\}$ is $2$-sum-free modulo $3$.** The singleton $\{1\}$ is $2$-sum-free modulo $3$,
since $1 + 1 \not\equiv 1 \pmod{3}$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 2 context. -/
theorem isSumFreeMod_three_two_singleton_one : IsSumFreeMod 3 2 {1} := by
  intro x hx y hy
  simp only [Set.mem_singleton_iff] at hx hy
  subst hy
  rw [Fin.sum_univ_two, hx 0, hx 1]
  decide

/-- **Modular Schur numbers modulo a prime power for many classes.** Let $p$ be a prime, let $i$
and $l$ be positive integers with $l \not\equiv 1 \pmod p$, and let $k$ be a natural number with
$k \ge p^i - 1$. Then the generalized Schur number modulo $p^i$ satisfies
$S_{p^i}(k, l) = p^i - 1$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 7
(`integers-2025-A62-cor-7`). -/
theorem modularSchurNumber_prime_pow_eq (p i k l : ℕ) (hp : p.Prime) (hi : 0 < i)
    (hl : 0 < l) (hlp : ¬ l ≡ 1 [MOD p]) (hk : p ^ i - 1 ≤ k) :
    modularSchurNumber (p ^ i) k l = p ^ i - 1 := by
  have hm : 1 < p ^ i := Nat.one_lt_pow hi.ne' hp.one_lt
  have hcop : (p ^ i).Coprime (l - 1) := by
    apply Nat.Coprime.pow_left
    exact hp.coprime_iff_not_dvd.mpr fun h => hlp ((Nat.modEq_iff_dvd' hl).mpr h).symm
  apply IsGreatest.csSup_eq
  constructor
  · -- Give each integer in the range its own color.
    let c (a : ℕ) : Fin k := ⟨(a - 1) % k, Nat.mod_lt _ (by omega)⟩
    have hc {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ p ^ i - 1) : (c a).val = a - 1 :=
      Nat.mod_eq_of_lt (by omega)
    refine ⟨c, fun j x hx y hy hsum => ?_⟩
    obtain ⟨a, ha, ha', hja, rfl⟩ := hy
    have hx' (t : Fin l) : x t = (a : ℤ) := by
      obtain ⟨b, hb, hb', hjb, hxt⟩ := hx t
      have heq := congrArg Fin.val (hjb.trans hja.symm)
      rw [hc hb hb', hc ha ha'] at heq
      have : b = a := by omega
      simpa only [this] using hxt
    have hmod : l * a ≡ a [MOD p ^ i] := Int.natCast_modEq_iff.mp (by
      simpa only [hx', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Int.natCast_mul] using hsum)
    have hdvd : p ^ i ∣ (l - 1) * a := by
      simpa only [Nat.sub_mul, one_mul] using hmod.symm.dvd'
    have := Nat.le_of_dvd ha (hcop.dvd_of_dvd_mul_left hdvd)
    omega
  · -- Any longer range puts the modulus itself in one of the classes.
    rintro n ⟨c, hc⟩
    by_contra! hn
    refine not_isSumFreeMod_of_dvd_mem (p ^ i) l ?_ (dvd_refl _) (hc (c (p ^ i)))
    exact ⟨p ^ i, by omega, by omega, rfl, rfl⟩

end

end MetaMathlibExt
