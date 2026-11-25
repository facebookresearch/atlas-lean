/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Coprime.Lemmas

import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic.Ring

/-!
# Representations by two coprime generators

`MetaMathlibExt.twoGenerator_dvd_sub_of_eq` gives the divisibility relations between the
coefficients of two representations of the same natural number.
`MetaMathlibExt.exists_eq_of_ncard_twoGeneratorReps` gives a bounded normal form determined
by the exact number of representations.
`MetaMathlibExt.card_primes_ellNumericalSemigroup_eq` counts primes with more than
`ℓ` representations up to the Frobenius bound using a translate of the semigroup.
-/

namespace MetaMathlibExt

/-- **Two representations by coprime generators.** Let $c$ and $d$ be coprime natural numbers.
If natural numbers $x, y, x', y'$ satisfy $cx + dy = cx' + dy'$, then $c$ divides $y - y'$ and
$d$ divides $x - x'$ in the integers.

The paper's standing assumption $1 < c < d$ is not needed and is dropped.

Source: Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and
Skałba, III*, INTEGERS 25 (2025), Article A51, Lemma 1 (`integers-2025-A51-lem-1`). -/
public theorem twoGenerator_dvd_sub_of_eq {c d : ℕ} (hcd : c.Coprime d)
    {x y x' y' : ℕ} (h : c * x + d * y = c * x' + d * y') :
    (c : ℤ) ∣ (y : ℤ) - y' ∧ (d : ℤ) ∣ (x : ℤ) - x' := by
  have hdiff : (c : ℤ) * ((x : ℤ) - x') = d * ((y' : ℤ) - y) := by
    rw [mul_sub, mul_sub, sub_eq_sub_iff_add_eq_add]
    exact_mod_cast h.trans (add_comm ..)
  exact ⟨dvd_sub_comm.mp (hcd.isCoprime.dvd_of_dvd_mul_left ⟨_, hdiff.symm⟩),
    hcd.symm.isCoprime.dvd_of_dvd_mul_left ⟨_, hdiff⟩⟩

private theorem lt_ncard_reps_iff {c d ℓ n : ℕ} (hc : 0 < c) (hd : 0 < d)
    (hcop : c.Coprime d) :
    ℓ < {p : ℕ × ℕ | c * p.1 + d * p.2 = n}.ncard ↔
      ∃ x y : ℕ, n = ℓ * c * d + c * x + d * y := by
  let reps := {p : ℕ × ℕ | c * p.1 + d * p.2 = n}
  change ℓ < reps.ncard ↔ _
  constructor
  · intro hcard
    -- All first coordinates have the same residue modulo d, so their quotients distinguish them.
    have hinj : reps.InjOn (fun p => p.1 / d) := by
      rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq (heq : x / d = x' / d)
      have h : c * x + d * y = c * x' + d * y' := hp.trans hq.symm
      have hmod : x' % d = x % d := Nat.modEq_iff_dvd.mpr (twoGenerator_dvd_sub_of_eq hcop h).2
      have hx : x = x' := by
        simpa only [← hmod, heq, Nat.mod_add_div] using (Nat.mod_add_div x d).symm
      subst x'
      exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel h))
    obtain ⟨⟨x, y⟩, hxy, (hx : ℓ * d ≤ x)⟩ : ∃ p ∈ reps, ℓ * d ≤ p.1 := by
      by_contra! hsmall
      have hmap : ∀ p ∈ reps, p.1 / d ∈ Set.Iio ℓ := fun p hp =>
        (Nat.div_lt_iff_lt_mul hd).2 (hsmall p hp)
      apply hcard.not_ge
      simpa using Set.ncard_le_ncard_of_injOn _ hmap hinj (Set.finite_Iio ℓ)
    obtain ⟨x₀, hx₀⟩ := Nat.exists_eq_add_of_le hx
    refine ⟨x₀, y, ?_⟩
    change c * x + d * y = n at hxy
    rw [← hxy, hx₀]
    ring
  · rintro ⟨x, y, hn⟩
    have hfin : reps.Finite := by
      refine ((Set.finite_Iic n).prod (Set.finite_Iic n)).subset ?_
      rintro ⟨a, b⟩ (hab : c * a + d * b = n)
      rw [← hab]
      exact ⟨(Nat.le_mul_of_pos_left a hc).trans (Nat.le_add_right ..),
        (Nat.le_mul_of_pos_left b hd).trans (Nat.le_add_left ..)⟩
    -- Distribute the ℓ copies of cd between the two summands.
    apply Set.le_ncard_of_inj_on_range (fun i => (x + i * d, y + (ℓ - i) * c)) _ _ hfin
    · intro i hi
      change c * (x + i * d) + d * (y + (ℓ - i) * c) = n
      have hsplit : ℓ = i + (ℓ - i) := by omega
      calc
        _ = (i + (ℓ - i)) * c * d + c * x + d * y := by ring
        _ = n := by rw [← hsplit, hn]
    · intro i _ j _ hij
      exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel (congrArg Prod.fst hij))

/-- **Normal form of a number with exactly $\ell$ representations.** Let $c$ and $d$ be coprime
positive integers, and let $n$ and $\ell$ be natural numbers such that the equation
$n = cx + dy$ has exactly $\ell$ solutions $(x, y)$ in natural numbers. Then there are natural
numbers $x_0 < d$ and $y_0 < c$ with $n = (\ell - 1)cd + cx_0 + dy_0$ in the integers.

The identity is stated over the integers, so $\ell = 0$ is included (then $\ell - 1 = -1$). The
paper's standing assumption $1 < c < d$ is weakened to $0 < c$, $0 < d$.

Source: Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and
Skałba, III*, INTEGERS 25 (2025), Article A51, Lemma 2 (`integers-2025-A51-lem-2`). -/
public theorem exists_eq_of_ncard_twoGeneratorReps {c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (hcd : c.Coprime d) (n ℓ : ℕ) (hℓ : {p : ℕ × ℕ | c * p.1 + d * p.2 = n}.ncard = ℓ) :
    ∃ x₀ < d, ∃ y₀ < c, (n : ℤ) = ((ℓ : ℤ) - 1) * c * d + c * x₀ + d * y₀ := by
  have threshold (k : ℕ) :
      k < ℓ ↔ ∃ x y : ℕ, n = k * c * d + c * x + d * y := by
    rw [← hℓ]
    exact lt_ncard_reps_iff hc hd hcd
  -- Shifting by cd gives a natural-number identity even when n has no representation.
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℕ, n + c * d = ℓ * c * d + c * x + d * y := by
    cases ℓ with
    | zero =>
      obtain ⟨x, y, h⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le c d (n + c * d)
        (by simp [hcd.gcd_eq_one])
        ((Nat.mul_le_mul (Nat.pred_le c) (Nat.pred_le d)).trans (Nat.le_add_left ..))
      exact ⟨x, y, by simpa [mul_comm] using h.symm⟩
    | succ k =>
      obtain ⟨x, y, h⟩ := (threshold k).mp (Nat.lt_succ_self k)
      exact ⟨x, y, by rw [h, Nat.succ_mul, Nat.add_mul]; omega⟩
  -- Either coefficient exceeding its bound would give more than ℓ representations of n.
  have hmax := mt (threshold ℓ).mpr (Nat.lt_irrefl ℓ)
  refine ⟨x, ?_, y, ?_, ?_⟩
  · by_contra! hx
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hx
    apply hmax
    exact ⟨a, y, by rw [Nat.mul_add] at hxy; omega⟩
  · by_contra! hy
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hy
    apply hmax
    exact ⟨x, b, by rw [Nat.mul_add, Nat.mul_comm d c] at hxy; omega⟩
  · rw [sub_mul, sub_mul, one_mul, sub_add_eq_add_sub, sub_add_eq_add_sub, eq_sub_iff_add_eq]
    exact_mod_cast hxy

/-- **Counting primes with more than $\ell$ representations.** Let $c$ and $d$ be coprime
natural numbers with $1 < c < d$, let $\ell$ be a natural number, and put
$g_\ell(c, d) = (\ell + 1)cd - c - d$. Write $\pi_{\ell,c,d}$ for the number of primes
$n \le g_\ell(c, d)$ such that the equation $n = cx + dy$ has more than $\ell$ solutions
$(x, y)$ in natural numbers. Then $\pi_{\ell,c,d}$ equals the number of primes $n$ with
$\ell cd < n \le g_\ell(c, d)$ of the form $n = \ell cd + cx_0 + dy_0$ for some natural numbers
$x_0 \le d$ and $y_0 \le c$.

Source: Yuchen Ding and Takao Komatsu, *On a Conjecture of Ramírez Alfonsín and
Skałba, III*, INTEGERS 25 (2025), Article A51, Lemma 3 (`integers-2025-A51-lem-3`),
with `g_ℓ(c, d)` from equation (1). -/
public theorem card_primes_ellNumericalSemigroup_eq {c d : ℕ} (hc : 1 < c) (hcd : c < d)
    (hcop : c.Coprime d) (ℓ : ℕ) :
    ((Finset.range ((ℓ + 1) * c * d - c - d + 1)).filter fun n =>
        n.Prime ∧ ℓ < {p : ℕ × ℕ | c * p.1 + d * p.2 = n}.ncard).card =
      ((Finset.Ioc (ℓ * c * d) ((ℓ + 1) * c * d - c - d)).filter fun n =>
        n.Prime ∧ ∃ x₀ ≤ d, ∃ y₀ ≤ c, n = ℓ * c * d + c * x₀ + d * y₀).card := by
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Finset.mem_Ioc]
  have hd : 0 < d := by omega
  rw [lt_ncard_reps_iff (by omega : 0 < c) hd hcop]
  constructor
  · rintro ⟨hle, hp, x, y, heq⟩
    have hupper : n ≤ ℓ * c * d + c * d := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_mul] at hle
      omega
    have hne : n ≠ ℓ * c * d := by
      rintro rfl
      exact Nat.not_prime_mul (by simp [show c ≠ 1 by omega]) (by omega) hp
    refine ⟨⟨by omega, hle⟩, hp, x, ?_, y, ?_, heq⟩
    · exact Nat.le_of_mul_le_mul_left (by omega : c * x ≤ c * d) (by omega)
    · apply Nat.le_of_mul_le_mul_left _ hd
      rw [Nat.mul_comm d c]
      omega
  · rintro ⟨⟨_, hle⟩, hp, x, _, y, _, heq⟩
    exact ⟨hle, hp, x, y, heq⟩

end MetaMathlibExt
