/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.Ring

/-!
# Quadratic nonresidues in the initial-repetitions congruences

We count the residue classes for which both `16 * r + 1` and `8 * r + 1` are nonsquares.
-/

namespace MetaMathlibExt

open Finset
open scoped BigOperators

local notation "χ" => quadraticChar _

private theorem sum_quadraticChar_mul_add_one {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (hF : ringChar F ≠ 2) :
    ∑ x : F, χ x * χ (x + 1) = -1 := by
  -- Off zero, divide the argument of the character by the square x².
  have h (x : F) : χ x * χ (x + 1) = χ (x⁻¹ + 1) - (if x = 0 then 1 else 0) := by
    by_cases hx : x = 0
    · simp [hx]
    have he : x * (x⁻¹ + 1) = x + 1 := by
      rw [mul_add, mul_inv_cancel₀ hx, mul_one, add_comm]
    calc
      _ = χ x * (χ x * χ (x⁻¹ + 1)) := by rw [← map_mul (χ : MulChar F ℤ) x (x⁻¹ + 1), he]
      _ = _ := by
        rw [← mul_assoc, ← pow_two, quadraticChar_sq_one hx, one_mul, ite_eq_right hx, sub_zero]
  have hsum : (∑ x : F, χ (x⁻¹ + 1)) = 0 :=
    (Equiv.sum_comp ((Equiv.inv F).trans (Equiv.addRight (1 : F))) (fun x ↦ χ x)).trans
      (quadraticChar_sum_zero hF)
  simp_rw [h, sum_sub_distrib, hsum]
  simp

private theorem card_filter_nonsquares {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (htwo : (2 : ZMod p) ≠ 0) :
    (univ.filter fun x : ZMod p ↦ ¬ IsSquare x ∧ ¬ IsSquare ((x + 1) / 2)).card = p / 4 := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  have hχ (x : ZMod p) : χ ((x + 1) / 2) = χ (2 : ZMod p) * χ (x + 1) := by
    calc
      _ = (χ (2 : ZMod p) * χ (2 : ZMod p)) * χ ((x + 1) / 2) := by
        rw [← pow_two, quadraticChar_sq_one htwo, one_mul]
      _ = _ := by
        rw [mul_assoc, ← map_mul, mul_comm (2 : ZMod p), div_mul_cancel₀ _ htwo]
  have hzero := quadraticChar_sum_zero hF
  have hshift : (∑ x : ZMod p, χ (x + 1)) = 0 :=
    (Equiv.sum_comp (Equiv.addRight (1 : ZMod p)) (fun x ↦ χ x)).trans hzero
  have hcross := sum_quadraticChar_mul_add_one hF
  have hsum : (∑ x : ZMod p, (1 - χ x) * (1 - χ ((x + 1) / 2))) = (p : ℤ) - χ (2 : ZMod p) := by
    calc
      _ = ∑ x : ZMod p, (1 - χ x - χ (2 : ZMod p) * χ (x + 1) +
          χ (2 : ZMod p) * (χ x * χ (x + 1))) := by
        apply sum_congr rfl
        intro x _
        rw [hχ]
        ring
      _ = _ := by
        rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum,
          hzero, hshift, hcross]
        simp [ZMod.card, sub_eq_add_neg]
  -- The weight is four at each qualifying residue; the two zero arguments need corrections.
  have hweight (x : ZMod p) :
      (1 - χ x) * (1 - χ ((x + 1) / 2)) =
        (if ¬ IsSquare x ∧ ¬ IsSquare ((x + 1) / 2) then 4 else 0) +
        (if x = 0 then 1 - χ (2 : ZMod p) else 0) +
        (if x = -1 then 1 - χ (-1 : ZMod p) else 0) := by
    by_cases hx : x = 0
    · subst x
      rw [hχ]
      simp [IsSquare.zero]
    by_cases hx' : x = -1
    · subst x
      simp [hx, IsSquare.zero]
    have hy : (x + 1) / 2 ≠ 0 := div_ne_zero (fun h ↦ hx' (eq_neg_of_add_eq_zero_left h)) htwo
    rcases quadraticChar_dichotomy hx with h | h <;>
      rcases quadraticChar_dichotomy hy with h' | h' <;>
      simp [← quadraticChar_neg_one_iff_not_isSquare, hx, hx', h, h']
  simp_rw [hweight, sum_add_distrib, Fintype.sum_ite_eq'] at hsum
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_comm _ (4 : ℤ)] at hsum
  -- Either sign of χ(-1) gives the same quotient after division by four.
  rcases quadraticChar_dichotomy (neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0)) with h | h <;>
    rw [h] at hsum <;> omega

open scoped Classical in
/-- **Residues $r$ with $16r + 1$ and $8r + 1$ both non-squares modulo $p$.** For every prime $p$,
the number of integers $r$ with $1 \le r \le p - 1$ such that neither $16r + 1$ nor $8r + 1$ is a
square modulo $p$ equals $\lfloor p/4 \rfloor$.

Here $0$ counts as a square modulo $p$, so "not a square" means "quadratic nonresidue". The paper
assumes $p \ge 5$; for $p = 2$ and $p = 3$ both sides are $0$. If $0$ were counted as a non-square,
the count at $p = 5$ would be $2$ instead of $1$.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 5 (`integers-2025-A32-thm-5`). -/
public theorem card_not_isSquare_sixteen_mul_add_one_eight_mul_add_one (p : ℕ)
    (hp : p.Prime) :
    ((Finset.Icc 1 (p - 1)).filter fun r =>
        ¬IsSquare ((16 * r + 1 : ℕ) : ZMod p) ∧ ¬IsSquare ((8 * r + 1 : ℕ) : ZMod p)).card =
      p / 4 := by
  by_cases hp₂ : p = 2
  · subst p
    simp [show (16 : ZMod 2) = 0 by decide, IsSquare.one]
  -- The statement uses a classical filter; primality supplies a decidable square predicate.
  let P (r : ℕ) :=
    ¬ IsSquare ((16 * r + 1 : ℕ) : ZMod p) ∧ ¬ IsSquare ((8 * r + 1 : ℕ) : ZMod p)
  let s := (Icc 1 (p - 1)).filter P
  change s.card = p / 4
  let : Fact p.Prime := ⟨hp⟩
  rw [show s = (Icc 1 (p - 1)).filter (fun r ↦
    ¬ IsSquare ((16 * r + 1 : ℕ) : ZMod p) ∧ ¬ IsSquare ((8 * r + 1 : ℕ) : ZMod p)) from
    filter_congr_decidable _ P _]
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).elim hp.ne_one hp₂
  have hsixteen : (16 : ZMod p) ≠ 0 := by
    rw [show (16 : ZMod p) = 2 ^ 4 by ring]
    exact pow_ne_zero _ htwo
  let f (r : ZMod p) := 16 * r + 1
  have hf : Function.Bijective f :=
    (AddGroup.addRight_bijective (1 : ZMod p)).comp (mulLeft_bijective₀ (16 : ZMod p) hsixteen)
  have hform (r : ZMod p) : (f r + 1) / 2 = 8 * r + 1 := by
    apply (div_eq_iff htwo).mpr
    dsimp [f]
    ring
  have hpred (r : ℕ) :
      (¬IsSquare ((16 * r + 1 : ℕ) : ZMod p) ∧ ¬IsSquare ((8 * r + 1 : ℕ) : ZMod p)) ↔
        (¬IsSquare (f r) ∧ ¬IsSquare ((f r + 1) / 2)) := by
    simp [hform, f]
  rw [← card_filter_nonsquares hp₂ htwo]
  refine card_nbij (fun r : ℕ ↦ f r) ?_ ?_ ?_
  · intro r hr
    exact mem_filter.2 ⟨mem_univ _, (hpred r).mp (mem_filter.mp hr).2⟩
  · intro r hr s hs hrs
    have hp1 := hp.pos
    have hr' := mem_Icc.mp (mem_filter.mp hr).1
    have hs' := mem_Icc.mp (mem_filter.mp hs).1
    have he := congrArg ZMod.val (hf.injective hrs)
    simpa only [ZMod.val_natCast_of_lt (by omega : r < p),
      ZMod.val_natCast_of_lt (by omega : s < p)] using he
  · intro x hx
    obtain ⟨a, ha⟩ := hf.surjective x
    have ha0 : a ≠ 0 := by
      intro hz
      have hx1 : x = 1 := by simpa [f, hz] using ha.symm
      exact (mem_filter.mp hx).2.1 (hx1.symm ▸ IsSquare.one)
    have hav := ZMod.val_lt a
    have hav0 := (ZMod.val_ne_zero a).2 ha0
    refine ⟨a.val, mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, (hpred a.val).mpr ?_⟩, ?_⟩
    · rw [ZMod.natCast_zmod_val, ha]
      exact (mem_filter.mp hx).2
    · change f (a.val : ZMod p) = x
      rw [ZMod.natCast_zmod_val, ha]

end MetaMathlibExt
