/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
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

/-- A set `A` of integers is `l`-sum-free modulo `m` if no `x_1, …, x_l, y ∈ A`
(repetitions allowed) satisfy `x_1 + ⋯ + x_l ≡ y (mod m)`.

Source: J. Chappelon, M. P. Revuelta Marchena, M. I. Sanz Domínguez, *Modular Schur numbers*,
Electron. J. Combin. 20(2) (2013), Section 1.1, as used in Jourdan D'orville, Kai An Sim,
Kok Bin Wong, and Chee Kit Ho, *Modular Generalizations of Schur Numbers*, INTEGERS 25 (2025),
Article A62, Section 1. -/
def IsSumFreeMod (m l : ℕ) (A : Set ℤ) : Prop :=
  ∀ x : Fin l → ℤ, (∀ i, x i ∈ A) → ∀ y ∈ A, ¬ (∑ i, x i ≡ y [ZMOD m])

/-- `{1, …, n}` admits a partition into `k` (possibly empty) classes, each `l`-sum-free
modulo `m`; the partition is a coloring `c` by `Fin k`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Section 1. -/
def HasSumFreePartitionMod (m k l n : ℕ) : Prop :=
  ∃ c : ℕ → Fin k, ∀ j : Fin k,
    IsSumFreeMod m l {x : ℤ | ∃ a : ℕ, 1 ≤ a ∧ a ≤ n ∧ c a = j ∧ x = a}

/-- The generalized Schur number modulo `m`, `S_m(k, l)`: the largest `n` for which
`{1, …, n}` admits a partition into `k` sets that are `l`-sum-free modulo `m`
(for `m ≥ 1` the admissible `n` are at most `m - 1`).

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Section 1. -/
noncomputable def modularSchurNumber (m k l : ℕ) : ℕ :=
  sSup {n : ℕ | HasSumFreePartitionMod m k l n}

/-- The empty range `{1, …, 0}` always admits a partition into `k ≥ 1` sum-free classes.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Section 1
(`0 ≤ S_m(k, l)`). -/
theorem hasSumFreePartitionMod_zero (m k l : ℕ) : HasSumFreePartitionMod m (k + 1) l 0 := by
  refine ⟨fun _ => 0, fun j x _ y hy => ?_⟩
  obtain ⟨a, h1, h2, -⟩ := hy
  omega

/-- A set containing a multiple of `m` is not `l`-sum-free modulo `m` for `l ≥ 1`, since
`a + ⋯ + a ≡ a (mod m)` when `m ∣ a`.

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

/-- `{1}` is `2`-sum-free modulo `3`, since `1 + 1 ≢ 1 (mod 3)`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 2 context. -/
theorem isSumFreeMod_three_two_singleton_one : IsSumFreeMod 3 2 {1} := by
  intro x hx y hy
  simp only [Set.mem_singleton_iff] at hx hy
  subst hy
  rw [Fin.sum_univ_two, hx 0, hx 1]
  decide

/-- The singleton `{1}` is not `l`-sum-free modulo `m` if and only if `l ≡ 1 (mod m)`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 1
(`integers-2025-A62-cor-1`). -/
public theorem_wanted not_isSumFreeMod_singleton_one_iff (m l : ℕ) (hm : 0 < m) :
    ¬ IsSumFreeMod m l {1} ↔ l ≡ 1 [MOD m]

/-- For positive `k, l, m`: `S_m(k, l) = 0` if and only if `l ≡ 1 (mod m)`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 2
(`integers-2025-A62-cor-2`). -/
public theorem_wanted modularSchurNumber_eq_zero_iff (m k l : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hl : 0 < l) : modularSchurNumber m k l = 0 ↔ l ≡ 1 [MOD m]

/-- For positive `k, l` and `1 ≤ a ≤ m - 1` with `d = gcd(a, m)`: if `l ≡ 1 (mod m/d)`, then
`S_m(k, l) < a`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 3
(`integers-2025-A62-cor-3`). -/
public theorem_wanted modularSchurNumber_lt_of_modEq (m k l a : ℕ) (hk : 0 < k) (hl : 0 < l)
    (ha : 0 < a) (ham : a ≤ m - 1) (hla : l ≡ 1 [MOD m / Nat.gcd a m]) :
    modularSchurNumber m k l < a

/-- For `k, n ≥ 2` and positive `l` with `l ≢ 1 (mod 2n)`: `S_{2n}(k, l) = 1` when
`l ≡ n + 1 (mod 2n)`, and `S_{2n}(k, l) ≥ 2` otherwise.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 4
(`integers-2025-A62-cor-4`). -/
public theorem_wanted modularSchurNumber_two_mul (k l n : ℕ) (hk : 2 ≤ k) (hn : 2 ≤ n)
    (hl : 0 < l) (hl1 : ¬ l ≡ 1 [MOD 2 * n]) :
    (l ≡ n + 1 [MOD 2 * n] → modularSchurNumber (2 * n) k l = 1) ∧
      (¬ l ≡ n + 1 [MOD 2 * n] → 2 ≤ modularSchurNumber (2 * n) k l)

/-- For `l, m ≥ 2` with `l ≢ 1 (mod d)` for every divisor `d ≠ 1` of `m`, and `k ≥ m - 1`:
`S_m(k, l) = m - 1`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 5
(`integers-2025-A62-cor-5`). -/
public theorem_wanted modularSchurNumber_eq_sub_one (m k l : ℕ) (hl : 2 ≤ l) (hm : 2 ≤ m)
    (hd : ∀ d : ℕ, d ∣ m → d ≠ 1 → ¬ l ≡ 1 [MOD d]) (hk : m - 1 ≤ k) :
    modularSchurNumber m k l = m - 1

/-- For a prime `p`, positive `i, l` with `l ≢ 1 (mod p)`, and `1 ≤ k ≤ p - 1`:
`S_{p^i}(k, l) ≥ k`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 6
(`integers-2025-A62-cor-6`). -/
public theorem_wanted le_modularSchurNumber_prime_pow (p i k l : ℕ) (hp : p.Prime) (hi : 0 < i)
    (hl : 0 < l) (hlp : ¬ l ≡ 1 [MOD p]) (hk : 1 ≤ k) (hkp : k ≤ p - 1) :
    k ≤ modularSchurNumber (p ^ i) k l

/-- For a prime `p`, positive `i, l` with `l ≢ 1 (mod p)`, and `k ≥ p^i - 1`:
`S_{p^i}(k, l) = p^i - 1`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 7
(`integers-2025-A62-cor-7`). -/
public theorem_wanted modularSchurNumber_prime_pow_eq (p i k l : ℕ) (hp : p.Prime) (hi : 0 < i)
    (hl : 0 < l) (hlp : ¬ l ≡ 1 [MOD p]) (hk : p ^ i - 1 ≤ k) :
    modularSchurNumber (p ^ i) k l = p ^ i - 1

/-- For a prime `p` and `l ≥ p - 1` positive with `l ≢ 1 (mod p)`: `S_p(k, l) = k` for
`1 ≤ k ≤ p - 1` and `S_p(k, l) = p - 1` for `k ≥ p - 1`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 8
(`integers-2025-A62-cor-8`). -/
public theorem_wanted modularSchurNumber_prime (p l : ℕ) (hp : p.Prime) (hl : 0 < l)
    (hlp1 : p - 1 ≤ l) (hlp : ¬ l ≡ 1 [MOD p]) :
    (∀ k, 1 ≤ k → k ≤ p - 1 → modularSchurNumber p k l = k) ∧
      (∀ k, p - 1 ≤ k → modularSchurNumber p k l = p - 1)

/-- For a prime `p`, positive `i, l` with `l ≢ 1 (mod p)`, and `a ≢ 0 (mod p^i)`: the
singleton `{a}` is `l`-sum-free modulo `p^i`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Lemma 1
(`integers-2025-A62-lem-1`). -/
public theorem_wanted isSumFreeMod_singleton_prime_pow (p a i l : ℕ) (hp : p.Prime) (hi : 0 < i)
    (hl : 0 < l) (ha : ¬ p ^ i ∣ a) (hlp : ¬ l ≡ 1 [MOD p]) :
    IsSumFreeMod (p ^ i) l {(a : ℤ)}

/-- Part 1: for a prime `p`, positive `i`, and `l ≥ p^i - 1` with `l ≢ 1 (mod p)`, if `a`
and `b` lie in a common `l`-sum-free set modulo `p^i` (equivalently `{a, b}` is
`l`-sum-free modulo `p^i`), then `a ≡ b (mod p)`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Lemma 2, part 1
(`integers-2025-A62-lem-2`). -/
public theorem_wanted modEq_of_isSumFreeMod_pair (p a b i l : ℕ) (hp : p.Prime) (hi : 0 < i)
    (hl : p ^ i - 1 ≤ l) (hlp : ¬ l ≡ 1 [MOD p])
    (hab : IsSumFreeMod (p ^ i) l {(a : ℤ), (b : ℤ)}) : a ≡ b [MOD p]

/-- For positive `k, l`: `S_2(k, l) = 0` when `l ≡ 1 (mod 2)` and `S_2(k, l) = 1` when
`l ≡ 0 (mod 2)` (quoted from [4]).

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 1
(`integers-2025-A62-thm-1`). -/
public theorem_wanted modularSchurNumber_two (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (l ≡ 1 [MOD 2] → modularSchurNumber 2 k l = 0) ∧
      (l ≡ 0 [MOD 2] → modularSchurNumber 2 k l = 1)

/-- For positive `k, l`: `S_3(k, l) = 0` when `l ≡ 1 (mod 3)`; otherwise `S_3(1, l) = 1` and
`S_3(k, l) = 2` for `k ≥ 2` (quoted from [4]).

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 2
(`integers-2025-A62-thm-2`). -/
public theorem_wanted modularSchurNumber_three (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (l ≡ 1 [MOD 3] → modularSchurNumber 3 k l = 0) ∧
      (¬ l ≡ 1 [MOD 3] →
        (k = 1 → modularSchurNumber 3 k l = 1) ∧ (2 ≤ k → modularSchurNumber 3 k l = 2))

/-- Linear congruences: for `m > 0` and `d = gcd(a, m)`, `a x ≡ b (mod m)` is solvable iff
`d ∣ b`; then it has exactly `d` solutions modulo `m`, and if `x₀` is one solution the
solutions are `x ≡ x₀ + u (m / d) (mod m)` with `0 ≤ u ≤ d - 1`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 3, quoting a
textbook result ([3]) (`integers-2025-A62-thm-3`). -/
public theorem_wanted linear_congruence_solutions (a b : ℤ) (m : ℕ) (hm : 0 < m) :
    ((∃ x : ℤ, a * x ≡ b [ZMOD m]) ↔ (Int.gcd a m : ℤ) ∣ b) ∧
      ((Int.gcd a m : ℤ) ∣ b →
        ((Finset.range m).filter fun x : ℕ => a * x ≡ b [ZMOD m]).card = Int.gcd a m) ∧
      ∀ x₀ : ℤ, a * x₀ ≡ b [ZMOD m] → ∀ x : ℤ,
        (a * x ≡ b [ZMOD m] ↔
          ∃ u : ℕ, u < Int.gcd a m ∧ x ≡ x₀ + u * ((m : ℤ) / Int.gcd a m) [ZMOD m])

/-- For positive `a, l, m` with `a ≢ 0 (mod m)` and `d = gcd(a, m)`: if `d = 1`, `{a}` is not
`l`-sum-free modulo `m` iff `l ≡ 1 (mod m)`; if `d > 1`, iff `l ≡ 1 (mod m/d)`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 4
(`integers-2025-A62-thm-4`). -/
public theorem_wanted not_isSumFreeMod_singleton_iff (a l m : ℕ) (hl : 0 < l) (hm : 0 < m)
    (ha : ¬ m ∣ a) :
    (Nat.gcd a m = 1 → (¬ IsSumFreeMod m l {(a : ℤ)} ↔ l ≡ 1 [MOD m])) ∧
      (1 < Nat.gcd a m → (¬ IsSumFreeMod m l {(a : ℤ)} ↔ l ≡ 1 [MOD m / Nat.gcd a m]))

/-- For `l, m ≥ 2` with `l ≢ 1 (mod m)`: `S_m(1, l) = 1` iff `l = 2` or `l ≥ (m + 1)/2`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 5
(`integers-2025-A62-thm-5`). -/
public theorem_wanted modularSchurNumber_one_eq_one_iff (l m : ℕ) (hl : 2 ≤ l) (hm : 2 ≤ m)
    (hlm : ¬ l ≡ 1 [MOD m]) :
    modularSchurNumber m 1 l = 1 ↔ l = 2 ∨ m + 1 ≤ 2 * l

/-- Values of `S_4(k, l)` for positive `k, l`: `0` if `l ≡ 1 (mod 4)`; otherwise `1` if
`k = 1`, or `k ≥ 2` and `l ≡ 3 (mod 4)`; and `3` if `k ≥ 2` and `l ≡ 0, 2 (mod 4)`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 6
(`integers-2025-A62-thm-6`). -/
public theorem_wanted modularSchurNumber_four (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (l ≡ 1 [MOD 4] → modularSchurNumber 4 k l = 0) ∧
      (¬ l ≡ 1 [MOD 4] →
        ((k = 1 ∨ (2 ≤ k ∧ l ≡ 3 [MOD 4])) → modularSchurNumber 4 k l = 1) ∧
        ((2 ≤ k ∧ (l ≡ 0 [MOD 4] ∨ l ≡ 2 [MOD 4])) → modularSchurNumber 4 k l = 3))

/-- Values of `S_6(k, l)` for positive `k, l`: `0` if `l ≡ 1 (mod 6)`; otherwise
`1` if `k = 1, l ≠ 3` or `k ≥ 2, l ≡ 4`; `2` if `k = 1, l = 3` or `k ≥ 2, l ≡ 3, 5`;
`3` if `k = 2, l ≡ 0, 2, l ≥ 6`; `4` if `k = 2, l = 2`; `5` if `k ≥ 3, l ≡ 0, 2 (mod 6)`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 7
(`integers-2025-A62-thm-7`). -/
public theorem_wanted modularSchurNumber_six (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (l ≡ 1 [MOD 6] → modularSchurNumber 6 k l = 0) ∧
      (¬ l ≡ 1 [MOD 6] →
        (((k = 1 ∧ l ≠ 3) ∨ (2 ≤ k ∧ l ≡ 4 [MOD 6])) → modularSchurNumber 6 k l = 1) ∧
        (((k = 1 ∧ l = 3) ∨ (2 ≤ k ∧ (l ≡ 3 [MOD 6] ∨ l ≡ 5 [MOD 6]))) →
          modularSchurNumber 6 k l = 2) ∧
        ((k = 2 ∧ (l ≡ 0 [MOD 6] ∨ l ≡ 2 [MOD 6]) ∧ 6 ≤ l) → modularSchurNumber 6 k l = 3) ∧
        ((k = 2 ∧ l = 2) → modularSchurNumber 6 k l = 4) ∧
        ((3 ≤ k ∧ (l ≡ 0 [MOD 6] ∨ l ≡ 2 [MOD 6])) → modularSchurNumber 6 k l = 5))

/-- Values of `S_5(k, l)` for positive `k, l`: `0` if `l ≡ 1 (mod 5)`; otherwise `1` if
`k = 1`; `k` if `k ∈ {2, 3}` and `l ≠ 2`; `4` if `k ∈ {2, 3}` and `l = 2`, or `k ≥ 4`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 9
(`integers-2025-A62-thm-9`). -/
public theorem_wanted modularSchurNumber_five (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (l ≡ 1 [MOD 5] → modularSchurNumber 5 k l = 0) ∧
      (¬ l ≡ 1 [MOD 5] →
        (k = 1 → modularSchurNumber 5 k l = 1) ∧
        (((k = 2 ∨ k = 3) ∧ l ≠ 2) → modularSchurNumber 5 k l = k) ∧
        ((((k = 2 ∨ k = 3) ∧ l = 2) ∨ 4 ≤ k) → modularSchurNumber 5 k l = 4))

/-- Values of `S_7(k, l)` for positive `k, l`: `0` if `l ≡ 1 (mod 7)`; otherwise
`1` if `k = 1, l ≠ 3`; `2` if `k = 1, l = 3` or `k = 2, l ≥ 4`; `3` if `k = 2, l ∈ {2, 3}`
or `k = 3, l ≥ 5`; `4` if `k = 4, l ≥ 5`; `5` if `k = 3, l = 3` or `k = 5, l ≥ 5`; and `6`
if `k = 3, l ∈ {2, 4}`, or `k ∈ {4, 5}, l ∈ {2, 3, 4}`, or `k ≥ 6`.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 10
(`integers-2025-A62-thm-10`). -/
public theorem_wanted modularSchurNumber_seven (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (l ≡ 1 [MOD 7] → modularSchurNumber 7 k l = 0) ∧
      (¬ l ≡ 1 [MOD 7] →
        ((k = 1 ∧ l ≠ 3) → modularSchurNumber 7 k l = 1) ∧
        (((k = 1 ∧ l = 3) ∨ (k = 2 ∧ 4 ≤ l)) → modularSchurNumber 7 k l = 2) ∧
        (((k = 2 ∧ (l = 2 ∨ l = 3)) ∨ (k = 3 ∧ 5 ≤ l)) → modularSchurNumber 7 k l = 3) ∧
        ((k = 4 ∧ 5 ≤ l) → modularSchurNumber 7 k l = 4) ∧
        (((k = 3 ∧ l = 3) ∨ (k = 5 ∧ 5 ≤ l)) → modularSchurNumber 7 k l = 5) ∧
        (((k = 3 ∧ (l = 2 ∨ l = 4)) ∨ ((k = 4 ∨ k = 5) ∧ 2 ≤ l ∧ l ≤ 4) ∨ 6 ≤ k) →
          modularSchurNumber 7 k l = 6))

end

end MetaMathlibExt
