/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import MathlibExt.NumberTheory.CoveringSystem
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The Mirsky–Newman bound for covering systems

The reciprocals of the moduli of a distinct covering system with moduli at least two
sum to more than one. A primitive root of unity of order the largest modulus detects
an overlap in a common period.
-/

namespace MetaMathlibExt

open Finset

namespace MirskyNewman

private def multiplicity (classes : Finset (ℤ × ℕ)) (n : ℕ) : ℕ :=
  (classes.filter fun c => n % c.2 = c.1.natMod c.2).card

-- In a whole number of periods, the class consists of r, r + m, r + 2m, ...
private theorem sum_progression {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    {N m r : ℕ} (hd : m ∣ N) (hr : r < m) :
    (∑ n ∈ range N with n % m = r, f n) = ∑ k ∈ range (N / m), f (r + m * k) := by
  have hm : 0 < m := by omega
  symm
  apply sum_bij (fun k _ => r + m * k)
  · intro k hk
    refine mem_filter.mpr ⟨mem_range.mpr ?_, by simp [Nat.mod_eq_of_lt hr]⟩
    calc
      r + m * k < m * (k + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ m * (N / m) := Nat.mul_le_mul_left m (mem_range.mp hk)
      _ = N := Nat.mul_div_cancel' hd
  · intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_left hm (Nat.add_left_cancel hij)
  · intro n hn
    obtain ⟨hn, heq⟩ := mem_filter.mp hn
    refine ⟨n / m, mem_range.mpr ((Nat.div_lt_iff_lt_mul hm).mpr ?_), ?_⟩
    · simpa [Nat.div_mul_cancel hd] using mem_range.mp hn
    · rw [← heq, Nat.mod_add_div]
  · intros
    rfl

-- Count weighted incidences first by the integer covered, then by the class covering it.
private theorem sum_multiplicity {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    {classes : Finset (ℤ × ℕ)} {N : ℕ}
    (hd : ∀ c ∈ classes, c.2 ∣ N) (hpos : ∀ c ∈ classes, 0 < c.2) :
    ∑ n ∈ range N, multiplicity classes n • f n =
      ∑ c ∈ classes, ∑ k ∈ range (N / c.2), f (c.1.natMod c.2 + c.2 * k) := by
  calc
    _ = ∑ n ∈ range N, ∑ c ∈ classes, if n % c.2 = c.1.natMod c.2 then f n else 0 := by
      apply sum_congr rfl
      intro n _
      rw [← sum_filter, sum_const]
      rfl
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro c hc
      rw [← sum_filter]
      exact sum_progression f (hd c hc) (Int.natMod_lt (hpos c hc).ne')

private theorem not_exact_of_distinct {classes : Finset (ℤ × ℕ)} {N : ℕ}
    (hN : 0 < N) (hd : ∀ c ∈ classes, c.2 ∣ N) (hne : classes.Nonempty)
    (hdist : Set.InjOn Prod.snd (classes : Set (ℤ × ℕ))) (htwo : ∀ c ∈ classes, 2 ≤ c.2) :
    ¬ ∀ n ∈ range N, multiplicity classes n = 1 := by
  intro hexact
  obtain ⟨b, hb, hmax⟩ := exists_max_image classes Prod.snd hne
  have hpos (c) (hc : c ∈ classes) : 0 < c.2 := lt_of_lt_of_le (by decide : 0 < 2) (htwo c hc)
  let ζ := Complex.exp (2 * Real.pi * Complex.I / b.2)
  have hζ : IsPrimitiveRoot ζ b.2 := Complex.isPrimitiveRoot_exp _ (hpos b hb).ne'
  have hperiod := (hζ.pow_eq_one_iff_dvd N).mpr (hd b hb)
  -- The sum of the weights over the period vanishes.
  have htotal : (∑ n ∈ range N, multiplicity classes n • ζ ^ n) = 0 := by
    calc
      _ = ∑ n ∈ range N, ζ ^ n := sum_congr rfl fun n hn => by rw [hexact n hn, one_smul]
      _ = 0 := by rw [geom_sum_eq (hζ.ne_one (htwo b hb)), hperiod]; simp
  rw [sum_multiplicity _ hd hpos] at htotal
  -- All classes except the unique one with largest modulus also have weight zero.
  simp_rw [pow_add, pow_mul, ← mul_sum] at htotal
  rw [sum_eq_single_of_mem b hb] at htotal
  · have hquot := Nat.div_pos (Nat.le_of_dvd hN (hd b hb)) (hpos b hb)
    simp [hζ.pow_eq_one, hζ.ne_zero (hpos b hb).ne', hquot.ne'] at htotal
  · intro c hc hcb
    have hlt : c.2 < b.2 := lt_of_le_of_ne (hmax c hc) (fun h => hcb (hdist hc hb h))
    rw [geom_sum_eq (hζ.pow_ne_one_of_pos_of_lt (hpos c hc).ne' hlt), ← pow_mul,
      Nat.mul_div_cancel' (hd c hc), hperiod]
    simp

end MirskyNewman

open MirskyNewman

/-- **Mirsky–Newman bound for distinct covering systems.** Let $a_1 \bmod m_1, \dots,
a_k \bmod m_k$ be residue classes that cover $\mathbb{Z}$, that is, every integer lies in at
least one of them. If the moduli $m_1, \dots, m_k$ are pairwise distinct and all at least $2$,
then $\sum_{i=1}^{k} 1/m_i > 1$.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 5 (`integers-2026-A38-lem-5`), quoting Mirsky and
Newman. -/
public theorem one_lt_sum_inv_moduli_of_distinct_covering (classes : Finset (ℤ × ℕ))
    (hcov : Int.IsCoveringSystem classes) (hdist : Set.InjOn Prod.snd (classes : Set (ℤ × ℕ)))
    (htwo : ∀ c ∈ classes, 2 ≤ c.2) : (1 : ℚ) < ∑ c ∈ classes, (1 : ℚ) / c.2 := by
  let N := classes.lcm Prod.snd
  have hd (c) (hc : c ∈ classes) : c.2 ∣ N := dvd_lcm hc
  have hpos (c) (hc : c ∈ classes) : 0 < c.2 := lt_of_lt_of_le (by decide : 0 < 2) (htwo c hc)
  have hN : 0 < N := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr fun c hc => (hpos c hc).ne')
  have hcovered (n : ℕ) : 1 ≤ multiplicity classes n := by
    obtain ⟨c, hc, h⟩ := hcov n
    apply card_pos.mpr
    exact ⟨c, mem_filter.mpr ⟨hc, congrArg Int.toNat h⟩⟩
  obtain ⟨c, hc, _⟩ := hcov 0
  have hoverlap : ∃ n ∈ range N, 1 < multiplicity classes n := by
    by_contra! h
    exact not_exact_of_distinct hN hd ⟨c, hc⟩ hdist htwo
      (fun n hn => (h n hn).antisymm (hcovered n))
  have hcount : N < ∑ c ∈ classes, N / c.2 := by
    have h := sum_lt_sum (fun n (_ : n ∈ range N) => hcovered n) hoverlap
    simpa using h.trans_eq (by simpa using sum_multiplicity (fun _ => (1 : ℕ)) hd hpos)
  have hrat : (N : ℚ) < ∑ c ∈ classes, ((N / c.2 : ℕ) : ℚ) := by exact_mod_cast hcount
  rw [← mul_lt_mul_iff_right₀ (show (0 : ℚ) < N by exact_mod_cast hN), mul_one, mul_sum]
  refine hrat.trans_eq (sum_congr rfl fun c hc => ?_)
  rw [mul_one_div, Nat.cast_div (hd c hc) (Nat.cast_ne_zero.mpr (hpos c hc).ne')]

end MetaMathlibExt
