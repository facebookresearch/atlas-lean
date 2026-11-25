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

set_option linter.unusedVariables false in
/-- **When a singleton set is sum-free.** Let $a$, $l$ and $m$ be natural numbers with
$l \ge 1$, $m \ge 1$ and $m \nmid a$, and let $d = \gcd(a, m)$. If $d = 1$, then $\{a\}$ is not
$l$-sum-free modulo $m$ if and only if $l \equiv 1 \pmod{m}$. If $d > 1$, then $\{a\}$ is not
$l$-sum-free modulo $m$ if and only if $l \equiv 1 \pmod{m/d}$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 4
(`integers-2025-A62-thm-4`). -/
theorem not_isSumFreeMod_singleton_iff (a l m : ℕ) (hl : 0 < l) (hm : 0 < m)
    (ha : ¬ m ∣ a) :
    (Nat.gcd a m = 1 → (¬ IsSumFreeMod m l {(a : ℤ)} ↔ l ≡ 1 [MOD m])) ∧
      (1 < Nat.gcd a m → (¬ IsSumFreeMod m l {(a : ℤ)} ↔ l ≡ 1 [MOD m / Nat.gcd a m])) := by
  have hle : a ≤ l * a := by simpa using Nat.mul_le_mul_right a hl
  have criterion : ¬ IsSumFreeMod m l {(a : ℤ)} ↔ l ≡ 1 [MOD m / Nat.gcd a m] := calc
    ¬ IsSumFreeMod m l {(a : ℤ)} ↔ l * a ≡ a [MOD m] := by
      rw [← Int.natCast_modEq_iff]
      simp [IsSumFreeMod, ← funext_iff (g := fun _ : Fin l => (a : ℤ))]
    _ ↔ m ∣ a * (l - 1) := by
      rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' hle, Nat.mul_sub, Nat.mul_one, Nat.mul_comm a l]
    _ ↔ m / Nat.gcd a m ∣ l - 1 := by
      rw [Nat.gcd_comm a m, Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left m a)
        (Nat.gcd_pos_of_pos_left a hm), Nat.dvd_gcd_mul_iff_dvd_mul]
    _ ↔ l ≡ 1 [MOD m / Nat.gcd a m] := (Nat.modEq_iff_dvd' hl).symm.trans Nat.ModEq.comm
  exact ⟨fun hd => by simpa only [hd, Nat.div_one] using criterion, fun _ => criterion⟩

/-- **Elements of a sum-free pair are congruent modulo $p$.** Let $p$ be a prime, let $i$ be a
positive integer, and let $l$ be a natural number with $l \ge p^i - 1$ and
$l \not\equiv 1 \pmod{p}$. If $a$ and $b$ are natural numbers such that $\{a, b\}$ is
$l$-sum-free modulo $p^i$, then $a \equiv b \pmod{p}$.

Since subsets of $l$-sum-free sets are $l$-sum-free, the hypothesis says exactly that $a$ and
$b$ lie in a common $l$-sum-free set modulo $p^i$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Lemma 2, part 1
(`integers-2025-A62-lem-2`). -/
theorem modEq_of_isSumFreeMod_pair (p a b i l : ℕ) (hp : p.Prime) (hi : 0 < i)
    (hl : p ^ i - 1 ≤ l) (hlp : ¬ l ≡ 1 [MOD p])
    (hab : IsSumFreeMod (p ^ i) l {(a : ℤ), (b : ℤ)}) : a ≡ b [MOD p] := by
  wlog hle : a ≤ b generalizing a b
  · exact (this b a (by simpa [Set.pair_comm] using hab) (by omega)).symm
  by_contra h
  rw [Nat.modEq_iff_dvd' hle] at h
  have hcop := (hp.coprime_iff_not_dvd.mpr h).symm.pow_right i
  -- Choose the number of copies of a so that the mixed sum is congruent to b.
  obtain ⟨t, ht, hmod⟩ := Nat.exists_mul_mod_eq_of_coprime ((l - 1) * b) hcop
    (pow_ne_zero i hp.ne_zero)
  have hpos : 1 ≤ l := by
    have := Nat.one_lt_pow hi.ne' hp.one_lt
    omega
  have hstep := Int.natCast_modEq_iff.mpr
    (show (b - a) * t ≡ (l - 1) * b [MOD p ^ i] from hmod)
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (show t ≤ l by omega)
  refine hab (Fin.append (fun _ : Fin t => (a : ℤ)) (fun _ : Fin s => (b : ℤ))) ?_ b (by simp) ?_
  · simp [Fin.forall_fin_add]
  · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Fin.sum_const, nsmul_eq_mul]
    apply Int.modEq_iff_dvd.mpr
    convert hstep.symm.dvd using 1
    push_cast [Int.ofNat_sub hle, Int.ofNat_sub hpos]
    ring

namespace modularSchurNumber_two_mul

-- Give each integer its own color, so all summands in its class must equal it.
private theorem partition_of_not_modEq {m k l r : ℕ} (hk : 0 < k) (hr : r ≤ k)
    (h : ∀ a, 1 ≤ a → a ≤ r → ¬ l * a ≡ a [MOD m]) : HasSumFreePartitionMod m k l r := by
  let c (a : ℕ) : Fin k := ⟨(a - 1) % k, Nat.mod_lt _ hk⟩
  have hc {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ r) : (c a).val = a - 1 :=
    Nat.mod_eq_of_lt (by omega)
  refine ⟨c, fun j x hx y hy hsum => ?_⟩
  obtain ⟨a, ha, ha', hja, rfl⟩ := hy
  have hx' (i : Fin l) : x i = (a : ℤ) := by
    obtain ⟨b, hb, hb', hjb, hxi⟩ := hx i
    have heq := congrArg Fin.val (hjb.trans hja.symm)
    rw [hc hb hb', hc ha ha'] at heq
    have : b = a := by omega
    simpa only [this] using hxi
  apply h a ha ha'
  apply Int.natCast_modEq_iff.mp
  simpa only [hx', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Int.natCast_mul] using hsum

-- If the sum of l copies of a is congruent to a, no color class can contain a.
private theorem lt_of_modEq {m k l r a : ℕ} (hp : HasSumFreePartitionMod m k l r)
    (ha : 0 < a) (h : l * a ≡ a [MOD m]) : r < a := by
  by_contra! har
  obtain ⟨c, hc⟩ := hp
  have hmem : (a : ℤ) ∈ {x : ℤ | ∃ b : ℕ, 1 ≤ b ∧ b ≤ r ∧ c b = c a ∧ x = b} :=
    ⟨a, ha, har, rfl, rfl⟩
  apply hc (c a) (fun _ => a) (fun _ => hmem) a hmem
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Int.natCast_mul] using Int.natCast_modEq_iff.mpr h

private theorem mul_two_modEq_iff {n l : ℕ} (hl : 0 < l) (hl1 : ¬ l ≡ 1 [MOD 2 * n]) :
    l * 2 ≡ 2 [MOD 2 * n] ↔ l ≡ n + 1 [MOD 2 * n] := by
  have hcancel : l * 2 ≡ 2 [MOD 2 * n] ↔ l ≡ 1 [MOD n] := by
    simpa only [Nat.mul_comm 2 l, Nat.mul_one] using
      (Nat.ModEq.mul_left_cancel_iff' (a := l) (b := 1) (m := n) (by decide : 2 ≠ 0))
  rw [hcancel]
  constructor
  · intro h
    obtain ⟨q, hq⟩ := (Nat.modEq_iff_exists_eq_add hl).mp h.symm
    obtain ⟨t, ht | ht⟩ := Nat.even_or_odd' q
    · apply (hl1 ?_).elim
      calc
        l = (2 * n) * t + 1 := by rw [hq, ht]; ring
        _ ≡ 1 [MOD 2 * n] := Nat.ModEq.modulus_mul_add
    · calc
        l = (2 * n) * t + (n + 1) := by rw [hq, ht]; ring
        _ ≡ n + 1 [MOD 2 * n] := Nat.ModEq.modulus_mul_add
  · intro h
    exact (h.of_mul_left 2).trans Nat.add_modEq_left

end modularSchurNumber_two_mul

open modularSchurNumber_two_mul

/-- **Modular Schur numbers modulo an even number.** Let $k$, $l$ and $n$ be natural numbers with
$k \ge 2$, $n \ge 2$, $l \ge 1$ and $l \not\equiv 1 \pmod{2n}$, and let $S_{2n}(k, l)$ be the
generalized Schur number modulo $2n$. If $l \equiv n + 1 \pmod{2n}$, then $S_{2n}(k, l) = 1$;
otherwise $S_{2n}(k, l) \ge 2$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 4
(`integers-2025-A62-cor-4`). -/
theorem modularSchurNumber_two_mul (k l n : ℕ) (hk : 2 ≤ k) (hn : 2 ≤ n)
    (hl : 0 < l) (hl1 : ¬ l ≡ 1 [MOD 2 * n]) :
    (l ≡ n + 1 [MOD 2 * n] → modularSchurNumber (2 * n) k l = 1) ∧
      (¬ l ≡ n + 1 [MOD 2 * n] → 2 ≤ modularSchurNumber (2 * n) k l) := by
  have htwo := mul_two_modEq_iff hl hl1
  constructor
  · intro h
    apply IsGreatest.csSup_eq
    constructor
    · apply partition_of_not_modEq (by omega) (by omega)
      intro a ha ha'
      have : a = 1 := by omega
      simpa [this] using hl1
    · intro r hr
      exact Nat.le_of_lt_succ (lt_of_modEq hr (by decide) (htwo.mpr h))
  · intro h
    refine le_csSup (s := {r | HasSumFreePartitionMod (2 * n) k l r}) ?_ ?_
    · refine ⟨2 * n, fun r hr => ?_⟩
      exact (lt_of_modEq hr (by omega : 0 < 2 * n)
        (by simp [Nat.ModEq])).le
    · apply partition_of_not_modEq (by omega) hk
      intro a ha ha'
      obtain rfl | rfl : a = 1 ∨ a = 2 := by omega
      · simpa using hl1
      · exact fun hmod => h (htwo.mp hmod)

private theorem modularSchurNumber_eq_sub_one.of_coprime {m k l : ℕ} (hm : 2 ≤ m)
    (hk : m - 1 ≤ k) (hcop : m.Coprime (l - 1)) : modularSchurNumber m k l = m - 1 := by
  apply IsGreatest.csSup_eq
  constructor
  · apply partition_of_not_modEq (by omega) hk
    intro a ha ha' hmod
    have hdvd : m ∣ (l - 1) * a := by
      simpa only [Nat.sub_mul, one_mul] using hmod.symm.dvd'
    have := Nat.le_of_dvd ha (hcop.dvd_of_dvd_mul_left hdvd)
    omega
  · intro n hn
    have := lt_of_modEq hn (by omega : 0 < m) (by simp [Nat.ModEq])
    omega

/-- **Modular Schur numbers attaining $m - 1$.** Let $l \ge 2$ and $m \ge 2$ be natural numbers
such that $l \not\equiv 1 \pmod{d}$ for every divisor $d \ne 1$ of $m$, and let $k \ge m - 1$.
Then the generalized Schur number $S_m(k, l)$, the largest $n$ such that $\{1, \dots, n\}$
admits a partition into $k$ classes that are $l$-sum-free modulo $m$, equals $m - 1$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 5
(`integers-2025-A62-cor-5`). -/
theorem modularSchurNumber_eq_sub_one (m k l : ℕ) (hl : 2 ≤ l) (hm : 2 ≤ m)
    (hd : ∀ d : ℕ, d ∣ m → d ≠ 1 → ¬ l ≡ 1 [MOD d]) (hk : m - 1 ≤ k) :
    modularSchurNumber m k l = m - 1 := by
  apply modularSchurNumber_eq_sub_one.of_coprime hm hk
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra h
  apply hd _ (Nat.gcd_dvd_left m (l - 1)) h
  exact ((Nat.modEq_iff_dvd' (by omega : 1 ≤ l)).mpr (Nat.gcd_dvd_right m (l - 1))).symm

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
  exact modularSchurNumber_eq_sub_one.of_coprime hm hk hcop

end

end MetaMathlibExt
