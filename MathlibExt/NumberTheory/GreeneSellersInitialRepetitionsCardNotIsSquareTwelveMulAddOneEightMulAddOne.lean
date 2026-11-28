/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Simultaneous nonresidues of two affine expressions

For an odd prime $p$ and integers $m,n$ with $p \nmid mn(n-m)$, Lemma 1 counts the
representatives $0 \le r < p$ for which $mr+1$ and $nr+1$ are both quadratic nonresidues.
An affine change of variables reduces the count to prescribing the quadratic characters of $x$
and $1-x$, for which a Jacobi sum evaluates the mixed term. For primes $p \ge 5$, the count
on $1 \le r \le p-1$ for $12r+1$ and $8r+1$ follows by taking $m=12$, $n=8$ and noting
that $r=0$ gives two squares. For $p=2,3$ the specialized count is zero.

## References

* John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
  Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
  pp. 1–12, Lemma 1 and Theorem 8. <https://doi.org/10.5281/zenodo.15283654>
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

private theorem legendre_three (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    legendreSym p 3 = ZMod.χ₄ p * legendreSym 3 p := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h := legendreSym.quadratic_reciprocity' (p := 3) (q := p) (by decide) hp2
  have hodd := (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).mpr hp2
  simpa only [Nat.reduceDiv, Nat.cast_ofNat, one_mul, ← ZMod.χ₄_eq_neg_one_pow hodd] using h

private theorem character_formula (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    4 * ((p / 4 : ℕ) : ℤ) - (legendreSym p 3 - legendreSym p (-1)) * (legendreSym p 2 - 1) =
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
  rw [legendreSym.at_two hp2, legendreSym.at_neg_one hp2]
  simp only [legendre_three p hp2, hthree, ZMod.χ₄_nat_eq_if_mod_four,
    ZMod.χ₈_nat_eq_if_mod_eight]
  have h4 : p % 4 = (p % 24) % 4 := by omega
  have h8 : p % 8 = (p % 24) % 8 := by omega
  have h3 : p % 3 = (p % 24) % 3 := by omega
  have hclasses : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨
      p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := by omega
  rcases hclasses with h | h | h | h | h | h | h | h <;>
    norm_num [hodd, h4, h8, h3, h] <;> omega

@[expose] public section

section

local notation "χ" => quadraticChar _

/-- **Counting $r$ with $mr + 1$ and $nr + 1$ both quadratic nonresidues.** Let $p$ be an odd
prime, write $\left(\frac{a}{p}\right)$ for the Legendre symbol of an integer $a$, and let $m$ and
$n$ be integers with $p \nmid mn(n - m)$. If $N$ is the number of integers $r$ with
$0 \le r \le p - 1$ such that $\left(\frac{mr+1}{p}\right) = \left(\frac{nr+1}{p}\right) = -1$, then

$$4N = 4\left\lfloor \frac{p}{4} \right\rfloor -
\left(\left(\frac{m}{p}\right) - \left(\frac{n-m}{p}\right)\right)
\left(\left(\frac{n}{p}\right) - \left(\frac{m-n}{p}\right)\right).$$

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32, Lemma 1
(`integers-2025-A32-lem-1`). -/
public theorem four_mul_card_legendreSym_pair_eq_neg_one (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (m n : ℤ) (hmn : ¬ (p : ℤ) ∣ m * n * (n - m)) :
    4 * ((((Finset.range p).filter fun r : ℕ =>
        legendreSym p (m * r + 1) = -1 ∧ legendreSym p (n * r + 1) = -1).card : ℕ) : ℤ) =
      4 * ((p / 4 : ℕ) : ℤ) -
        (legendreSym p m - legendreSym p (n - m)) * (legendreSym p n - legendreSym p (m - n)) := by
  let m' : ZMod p := m
  let n' : ZMod p := n
  have h : m' * n' * (n' - m') ≠ 0 := by
    simpa only [Int.cast_mul, Int.cast_sub] using
      (CharP.intCast_eq_zero_iff (ZMod p) p (m * n * (n - m))).not.mpr hmn
  obtain ⟨hmul, hd⟩ := mul_ne_zero_iff.mp h
  obtain ⟨hm, hn⟩ := mul_ne_zero_iff.mp hmul
  have hd' : m' - n' ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hd))
  let a := n' / (n' - m')
  let b := m' / (m' - n')
  have ha : a ≠ 0 := div_ne_zero hn hd
  have hb : b ≠ 0 := div_ne_zero hm hd'
  -- Normalise the two affine forms to complementary arguments.
  let e := (Equiv.mulLeft₀ (a * m') (mul_ne_zero ha hm)).trans (Equiv.addRight a)
  have hx (r : ZMod p) : e r = a * (m' * r + 1) := by
    change (a * m') * r + a = a * (m' * r + 1)
    ring
  have hy (r : ZMod p) : 1 - e r = b * (n' * r + 1) := by
    have had : a * (n' - m') = n' := div_mul_cancel₀ _ hd
    have hbd : b * (n' - m') = -m' := by
      rw [show n' - m' = -(m' - n') by ring, mul_neg]
      exact congrArg Neg.neg (div_mul_cancel₀ m' hd')
    apply mul_right_cancel₀ hd
    rw [hx]
    calc
      _ = (n' - m') - (a * (n' - m')) * (m' * r + 1) := by ring
      _ = (b * (n' - m')) * (n' * r + 1) := by rw [had, hbd]; ring
      _ = _ := by ring
  have hcard₁ : ((range p).filter fun r : ℕ =>
      legendreSym p (m * r + 1) = -1 ∧ legendreSym p (n * r + 1) = -1).card =
      (univ.filter fun r : ZMod p => χ (m' * r + 1) = -1 ∧ χ (n' * r + 1) = -1).card := by
    refine card_nbij' (fun r : ℕ ↦ (r : ZMod p)) ZMod.val ?_ ?_ ?_ ?_
    · intro r hr
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      simpa only [legendreSym, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast] using
        (mem_filter.mp hr).2
    · intro r hr
      refine mem_filter.mpr ⟨mem_range.mpr r.val_lt, ?_⟩
      simpa only [legendreSym, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast,
        ZMod.natCast_zmod_val] using (mem_filter.mp hr).2
    · intro r hr
      exact ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp hr).1)
    · intro r _
      exact ZMod.natCast_zmod_val r
  have hcard₂ : (univ.filter fun r : ZMod p =>
      χ (m' * r + 1) = -1 ∧ χ (n' * r + 1) = -1).card =
      (univ.filter fun x : ZMod p => χ x = -χ a ∧ χ (1 - x) = -χ b).card := by
    apply card_equiv e
    intro r
    simp only [mem_filter, mem_univ, true_and]
    rw [hy, hx, ← character_scale (ZMod p) a _ ha, ← character_scale (ZMod p) b _ hb]
  have hs : -χ a = 1 ∨ -χ a = -1 := by
    rcases quadraticChar_dichotomy ha with h | h <;> simp [h]
  have ht : -χ b = 1 ∨ -χ b = -1 := by
    rcases quadraticChar_dichotomy hb with h | h <;> simp [h]
  have hF : ringChar (ZMod p) ≠ 2 := (ZMod.ringChar_zmod_n p).substr hp
  have hcount := character_pair_count (ZMod p) hF (-χ a) (-χ b) hs ht
  have hdiv (x y : ZMod p) : χ (x / y) = χ x * χ y := by
    rw [div_eq_mul_inv, map_mul, ← MulChar.inv_apply', (quadraticChar_isQuadratic _).inv]
  have haχ : χ a = χ n' * χ (n' - m') := hdiv _ _
  have hbχ : χ b = χ m' * χ (m' - n') := hdiv _ _
  have hnegprod : χ (n' - m') * χ (m' - n') = χ (-1 : ZMod p) := by
    rw [show m' - n' = -1 * (n' - m') by ring, map_mul]
    calc
      _ = χ (-1 : ZMod p) * χ (n' - m') ^ 2 := by ring
      _ = _ := by rw [quadraticChar_sq_one hd, mul_one]
  have hcross : χ a * χ b * χ (-1 : ZMod p) = χ m' * χ n' := by
    rw [haχ, hbχ]
    calc
      _ = χ m' * χ n' * ((χ (n' - m') * χ (m' - n')) * χ (-1 : ZMod p)) := by ring
      _ = _ := by
        rw [hnegprod, ← pow_two (χ (-1 : ZMod p)),
          quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero), mul_one]
  have hfour : (p : ℤ) - 2 = 4 * ((p / 4 : ℕ) : ℤ) - χ (-1 : ZMod p) := by
    have hodd := (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).mpr hp
    rw [quadraticChar_neg_one hF, ZMod.card, ZMod.χ₄_nat_eq_if_mod_four]
    have hmod : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hmod with hmod | hmod <;> simp [hmod] <;> omega
  calc
    _ = (p : ℤ) - 2 + χ a + χ b - χ a * χ b * χ (-1 : ZMod p) := by
      simpa only [← hcard₂, ← hcard₁, ZMod.card, sub_neg_eq_add, neg_mul_neg] using hcount
    _ = _ := by
      rw [hfour, hcross, haχ, hbχ, ← hnegprod]
      simp only [legendreSym, Int.cast_sub]
      ring

end

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
  have hmn : ¬ (p : ℤ) ∣ 12 * 8 * (8 - 12) := by
    rw [← CharP.intCast_eq_zero_iff (ZMod p) p]
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_ofNat]
    rw [show (12 : ZMod p) * 8 * (8 - 12) = -(2 ^ 7 * 3) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 7 h2) h3)
  have hcard : ((Icc 1 (p - 1)).filter fun r =>
      ¬IsSquare ((12 * r + 1 : ℕ) : ZMod p) ∧ ¬IsSquare ((8 * r + 1 : ℕ) : ZMod p)).card =
      ((range p).filter fun r : ℕ =>
        legendreSym p (12 * r + 1) = -1 ∧ legendreSym p (8 * r + 1) = -1).card := by
    congr 1
    ext r
    simp only [mem_filter, mem_Icc, mem_range, legendreSym.eq_neg_one_iff, Int.cast_add,
      Int.cast_mul, Int.cast_one, Int.cast_ofNat, Int.cast_natCast, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat]
    by_cases hr : r = 0
    · subst r
      simp [IsSquare.one]
    · rw [show (1 ≤ r ∧ r ≤ p - 1) ↔ r < p by omega]
  have h4 : legendreSym p 4 = 1 := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
    exact legendreSym.sq_one' p (by simpa only [Int.cast_ofNat] using h2)
  have h4mul (z : ℤ) : legendreSym p (4 * z) = legendreSym p z := by
    rw [legendreSym.mul, h4, one_mul]
  have hnegFour : legendreSym p (-4) = legendreSym p (-1) := by
    rw [show (-4 : ℤ) = 4 * (-1) by norm_num, h4mul]
  have h := four_mul_card_legendreSym_pair_eq_neg_one p hp2 12 8 hmn
  rw [← hcard, show (8 : ℤ) - 12 = -4 by norm_num, show (12 : ℤ) - 8 = 4 by norm_num,
    show legendreSym p 12 = legendreSym p 3 from h4mul 3,
    show legendreSym p 8 = legendreSym p 2 from h4mul 2,
    hnegFour, h4, character_formula p hp5] at h
  convert (Nat.cast_inj.mp (mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h)) using 1
  congr 1
  ext r
  simp only [mem_filter]

end

end MetaMathlibExt
