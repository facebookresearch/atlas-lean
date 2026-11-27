/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Simultaneous nonresidues of two affine expressions

We count residues for which both $12r + 1$ and $8r + 1$ are nonsquares modulo a prime.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 8 (`integers-2025-A32-thm-8`).
-/

namespace MetaMathlibExt

open Finset

private theorem character_pair_count (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (s t : ℤ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    4 * ((univ.filter fun x : F => quadraticChar F x = s ∧
      quadraticChar F (1 - x) = t).card : ℤ) =
      Fintype.card F - 2 - s - t - s * t * quadraticChar F (-1) := by
  classical
  have pointwise (x : F) :
      4 * (if quadraticChar F x = s ∧ quadraticChar F (1 - x) = t then 1 else 0 : ℤ) =
        1 + s * quadraticChar F x + t * quadraticChar F (1 - x) +
          s * t * (quadraticChar F x * quadraticChar F (1 - x)) -
          (if x = 0 then 1 + t else 0) - (if x = 1 then 1 + s else 0) := by
    by_cases hx : x = 0
    · subst x
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num
    by_cases hx1 : x = 1
    · subst x
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num
    have hy : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      rcases quadraticChar_dichotomy hx with ha | ha <;>
      rcases quadraticChar_dichotomy hy with hb | hb <;>
      simp [hx, hx1, ha, hb]
  have hsum := congrArg (fun f : F → ℤ => ∑ x, f x) (funext pointwise)
  have hj : ∑ x : F, quadraticChar F x * quadraticChar F (1 - x) =
      -quadraticChar F (-1) := by
    have h := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
    rwa [(quadraticChar_isQuadratic F).inv] at h
  have hrev : ∑ x : F, quadraticChar F (1 - x) = 0 := by
    change ∑ x : F, quadraticChar F ((Equiv.subLeft (1 : F)) x) = 0
    rw [(Equiv.subLeft (1 : F)).sum_comp]
    exact quadraticChar_sum_zero hF
  simp only [← mul_sum, sum_boole, sum_add_distrib, sum_sub_distrib,
    ← mul_sum, quadraticChar_sum_zero hF, hrev, hj, sum_const, card_univ,
    nsmul_eq_mul, mul_one, mul_zero, add_zero, sum_ite_eq', mem_univ, ite_true] at hsum
  linarith

private theorem character_scale (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (c a : F) (hc : c ≠ 0) :
    quadraticChar F a = -1 ↔ quadraticChar F (c * a) = -quadraticChar F c := by
  rw [map_mul]
  rcases quadraticChar_dichotomy hc with h | h <;> rw [h] <;>
    constructor <;> intro ha <;> linarith

open scoped Classical in
private theorem affine_card (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (h3 : (3 : ZMod p) ≠ 0) :
    (univ.filter fun r : ZMod p => ¬IsSquare (12 * r + 1) ∧
      ¬IsSquare (8 * r + 1)).card =
      (univ.filter fun x : ZMod p => quadraticChar (ZMod p) x =
        -quadraticChar (ZMod p) (-2) ∧ quadraticChar (ZMod p) (1 - x) =
          -quadraticChar (ZMod p) 3).card := by
  classical
  have h24 : (-24 : ZMod p) ≠ 0 := by
    have he : (-24 : ZMod p) = -(2 ^ 3 * 3) := by ring
    rw [he]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 h2) h3)
  let e : ZMod p ≃ ZMod p := (Equiv.mulLeft₀ (-24) h24).trans (Equiv.addRight (-2))
  apply card_equiv e
  intro r
  simp only [mem_filter, mem_univ, true_and]
  have he : e r = -24 * r - 2 := by dsimp [e]; rw [Equiv.mulLeft₀_apply]; ring
  rw [he, ← quadraticChar_neg_one_iff_not_isSquare,
    ← quadraticChar_neg_one_iff_not_isSquare, character_scale (ZMod p) (-2) _
      (neg_ne_zero.mpr h2), character_scale (ZMod p) 3 _ h3]
  ring_nf

open scoped Classical in
private theorem representative_card (p : ℕ) [Fact p.Prime] :
    ((Icc 1 (p - 1)).filter fun r => ¬IsSquare ((12 * r + 1 : ℕ) : ZMod p) ∧
      ¬IsSquare ((8 * r + 1 : ℕ) : ZMod p)).card =
      (univ.filter fun r : ZMod p => ¬IsSquare (12 * r + 1) ∧
        ¬IsSquare (8 * r + 1)).card := by
  classical
  have hp0 := (Fact.out : p.Prime).pos
  apply card_bij (fun (r : ℕ) _ => (r : ZMod p))
  · intro r hr
    simpa only [mem_filter, mem_univ, true_and, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using (mem_filter.mp hr).2
  · intro r hr s hs he
    have hrp : r < p := by have := (mem_Icc.mp (mem_filter.mp hr).1).2; omega
    have hsp : s < p := by have := (mem_Icc.mp (mem_filter.mp hs).1).2; omega
    have h := congrArg ZMod.val he
    simpa only [ZMod.val_natCast_of_lt hrp, ZMod.val_natCast_of_lt hsp] using h
  · intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      have hns := (mem_filter.mp hx).2.1
      simp [h] at hns
    have hpos : 1 ≤ x.val := by
      have h := (ZMod.val_eq_zero x).not.mpr hx0
      omega
    refine ⟨x.val, mem_filter.mpr ⟨mem_Icc.mpr ⟨hpos, ?_⟩, ?_⟩,
      ZMod.natCast_zmod_val x⟩
    · have h := ZMod.val_lt x
      omega
    · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        ZMod.natCast_zmod_val] using (mem_filter.mp hx).2

open scoped Classical in
private theorem four_mul_count (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (h2 : (2 : ZMod p) ≠ 0) (h3 : (3 : ZMod p) ≠ 0) :
    4 * (((Icc 1 (p - 1)).filter fun r =>
      ¬IsSquare ((12 * r + 1 : ℕ) : ZMod p) ∧
      ¬IsSquare ((8 * r + 1 : ℕ) : ZMod p)).card : ℤ) =
        p - 2 - legendreSym p 6 + legendreSym p 3 + legendreSym p (-2) := by
  classical
  have hs : -quadraticChar (ZMod p) (-2) = 1 ∨
      -quadraticChar (ZMod p) (-2) = -1 := by
    rcases quadraticChar_dichotomy (neg_ne_zero.mpr h2) with h | h <;> simp [h]
  have ht : -quadraticChar (ZMod p) 3 = 1 ∨
      -quadraticChar (ZMod p) 3 = -1 := by
    rcases quadraticChar_dichotomy h3 with h | h <;> simp [h]
  have h := character_pair_count (ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using hp2)
    (-quadraticChar (ZMod p) (-2)) (-quadraticChar (ZMod p) 3) hs ht
  rw [← affine_card p h2 h3, ← representative_card p, ZMod.card] at h
  have hprod : quadraticChar (ZMod p) (-2) * quadraticChar (ZMod p) 3 *
      quadraticChar (ZMod p) (-1) = quadraticChar (ZMod p) 6 := by
    rw [← map_mul, ← map_mul]
    congr 1
    ring
  simp only [neg_mul_neg, hprod] at h
  simpa only [legendreSym, Int.cast_ofNat, Int.cast_neg, sub_neg_eq_add,
    sub_eq_add_neg, neg_neg, add_assoc, add_comm, add_left_comm] using h

private theorem legendre_three (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    legendreSym p 3 = ZMod.χ₄ p * legendreSym 3 p := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h := legendreSym.quadratic_reciprocity' (p := 3) (q := p) (by decide) hp2
  have hodd := (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).mpr hp2
  simpa only [Nat.reduceDiv, Nat.cast_ofNat, one_mul, ← ZMod.χ₄_eq_neg_one_pow hodd] using h

private theorem character_formula (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (p : ℤ) - 2 - legendreSym p 6 + legendreSym p 3 + legendreSym p (-2) =
      4 * ((if p % 24 = 5 then p / 4 - 1 else
        if p % 24 = 11 then p / 4 + 1 else p / 4 : ℕ) : ℤ) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hodd := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp2
  have hmod3 : p % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have he := (hp.dvd_iff_eq (by decide : 3 ≠ 1)).mp hd
    omega
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hthree : legendreSym 3 p = if p % 3 = 1 then 1 else -1 := by
    rw [legendreSym.mod]
    simp only [Nat.cast_ofNat]
    have h : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h with h | h
    · have he : (p : ℤ) % 3 = 1 := by omega
      rw [he]
      norm_num [h]
    · have he : (p : ℤ) % 3 = 2 := by omega
      rw [he]
      norm_num [h]
  rw [show (6 : ℤ) = 2 * 3 by norm_num, legendreSym.mul, legendreSym.at_two hp2,
    legendreSym.at_neg_two hp2]
  simp only [legendre_three p hp2, hthree, ZMod.χ₄_nat_eq_if_mod_four,
    ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈'_nat_eq_if_mod_eight]
  have h4 : p % 4 = (p % 24) % 4 := by omega
  have h8 : p % 8 = (p % 24) % 8 := by omega
  have h3 : p % 3 = (p % 24) % 3 := by omega
  have hclasses : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨
      p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := by omega
  rcases hclasses with h | h | h | h | h | h | h | h <;>
    norm_num [hodd, h4, h8, h3, h] <;> omega

@[expose] public section

open scoped Classical in
/-- **Residues $r$ with $12r + 1$ and $8r + 1$ both non-squares modulo $p$.** For every prime $p$,
let $N$ be the number of integers $r$ with $1 \le r \le p - 1$ such that neither $12r + 1$ nor
$8r + 1$ is a square modulo $p$. Then $N = \lfloor p/4 \rfloor - 1$ if $p \equiv 5 \pmod{24}$,
$N = \lfloor p/4 \rfloor + 1$ if $p \equiv 11 \pmod{24}$, and $N = \lfloor p/4 \rfloor$ otherwise.

Here $0$ counts as a square modulo $p$, so "not a square" means "quadratic nonresidue". The paper
assumes $p \ge 5$; for $p = 2$ and $p = 3$ both sides are $0$. If $0$ were counted as a non-square,
the count at $p = 5$ would be $2$ instead of $0$.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 8 (`integers-2025-A32-thm-8`). -/
public theorem card_not_isSquare_twelve_mul_add_one_eight_mul_add_one (p : ℕ)
    (hp : p.Prime) :
    ((Finset.Icc 1 (p - 1)).filter fun r =>
        ¬IsSquare ((12 * r + 1 : ℕ) : ZMod p) ∧ ¬IsSquare ((8 * r + 1 : ℕ) : ZMod p)).card =
      if p % 24 = 5 then p / 4 - 1 else if p % 24 = 11 then p / 4 + 1 else p / 4 := by
  classical
  by_cases hp2 : p = 2
  · subst p
    have h12 : (12 : ZMod 2) = 0 := by decide
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, h12,
      zero_mul, zero_add, IsSquare.one, not_true, false_and, filter_false, card_empty]
    norm_num
  by_cases hp3 : p = 3
  · subst p
    have h12 : (12 : ZMod 3) = 0 := by decide
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, h12,
      zero_mul, zero_add, IsSquare.one, not_true, false_and, filter_false, card_empty]
    norm_num
  let : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have hodd := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp2
    have := hp.two_le
    omega
  have hsmall (n : ℕ) (hn : 0 < n) (hnp : n < p) : (n : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd hn hd
    omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using hsmall 2 (by decide) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using hsmall 3 (by decide) (by omega)
  have h := four_mul_count p hp2 h2 h3
  rw [character_formula p hp5] at h
  convert (Nat.cast_inj.mp (mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h)) using 1
  congr 1
  ext r
  simp only [mem_filter, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]

end

end MetaMathlibExt
