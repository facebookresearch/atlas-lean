/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

private noncomputable def xpoly (n k : ℚ) : ℚ :=
  (-58 - 392*n - 1042*n^2 - 1364*n^3 - 880*n^4 - 224*n^5)
  + k*(207/2 + 1113/2*n + 1107*n^2 + 966*n^3 + 312*n^4)
  + k^2*(-147/2 - 297*n - 396*n^2 - 174*n^3)
  + k^3*(24 + 66*n + 45*n^2)
  + k^4*(-3 - 9/2*n)

private noncomputable def npoly (n k : ℚ) : ℚ :=
  (n+1)^2 * ((2*n+2)*(2*n+1))^3
  + 3*(3*n+1)*(3*n+2)*((2*n+2-k)^3*((2*n+1-k)^3))

private lemma gosper_identity (n k : ℚ) :
    -((2*n+2-k)^3) * xpoly n (k+1) - k^3 * xpoly n k = npoly n k := by
  unfold xpoly npoly
  ring

private noncomputable def Fq (n k : ℕ) : ℚ :=
  (-1 : ℚ)^k * ((Nat.choose (2*n) k : ℕ) : ℚ)^3

private noncomputable def Gq (n k : ℕ) : ℚ :=
  if k = 0 ∨ 2*n+3 ≤ k then 0
  else (-1 : ℚ)^k * ((Nat.factorial (2*n) : ℕ) : ℚ)^3 * xpoly (n : ℚ) (k : ℚ)
    / ((((Nat.factorial (k-1) : ℕ) : ℚ)^3) * (((Nat.factorial (2*n+2-k) : ℕ) : ℚ)^3))


private lemma key_interior (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * n) :
    ((n : ℚ)+1)^2 * Fq (n+1) k + 3*(3*(n : ℚ)+1)*(3*(n : ℚ)+2) * Fq n k
      = Gq n (k+1) - Gq n k := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i+1 := ⟨k-1, by omega⟩
  have hk2' : i+1 ≤ 2*n := hk2
  have gk : ¬ (i+1 = 0 ∨ 2*n+3 ≤ i+1) := by omega
  have gk1 : ¬ (i+1+1 = 0 ∨ 2*n+3 ≤ i+1+1) := by omega
  unfold Fq Gq
  rw [ite_eq_right gk, ite_eq_right gk1]
  simp only [Nat.add_sub_cancel]
  have e2n : 2*n+2-(i+1+1) = 2*n+1-(i+1) := by omega
  rw [e2n]
  have hneg : (-1:ℚ)^(i+1+1) = -(-1:ℚ)^(i+1) := by rw [pow_succ]; ring
  rw [hneg]
  have hC0q : ((Nat.choose (2*n) (i+1) : ℕ):ℚ) * (Nat.factorial (i+1) : ℚ)
        * (Nat.factorial (2*n-(i+1)) : ℚ) = (Nat.factorial (2*n) : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk2'
  have hC1q : ((Nat.choose (2*(n+1)) (i+1) : ℕ):ℚ) * (Nat.factorial (i+1) : ℚ)
        * (Nat.factorial (2*(n+1)-(i+1)) : ℚ) = (Nat.factorial (2*(n+1)) : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega)
  have e2np1 : 2*(n+1) = 2*n+2 := by omega
  rw [e2np1] at hC1q
  have hB : ((Nat.factorial (i+1) : ℕ):ℚ) = (((i:ℕ):ℚ)+1) * ((Nat.factorial i : ℕ):ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hA2 : ((Nat.factorial (2*n+2) : ℕ):ℚ)
      = ((2:ℚ)*n+2)*((2:ℚ)*n+1) * ((Nat.factorial (2*n) : ℕ):ℚ) := by
    have e1 : 2*n+2 = (2*n+1)+1 := by omega
    have e2 : 2*n+1 = (2*n)+1 := by omega
    rw [e1, Nat.factorial_succ, e2, Nat.factorial_succ]
    push_cast
    ring
  have hD1 : ((Nat.factorial (2*n+2-(i+1)) : ℕ):ℚ)
      = (((2*n+1-(i+1) : ℕ):ℚ)+1) * ((Nat.factorial (2*n+1-(i+1)) : ℕ):ℚ) := by
    have e1 : 2*n+2-(i+1) = (2*n+1-(i+1))+1 := by omega
    rw [e1, Nat.factorial_succ]
    push_cast
    ring
  have hF1 : ((Nat.factorial (2*n+1-(i+1)) : ℕ):ℚ)
      = (((2*n-(i+1) : ℕ):ℚ)+1) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ) := by
    have e2 : 2*n+1-(i+1) = (2*n-(i+1))+1 := by omega
    rw [e2, Nat.factorial_succ]
    push_cast
    ring
  have hBi : ((Nat.factorial (i+1) : ℕ):ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hC0f : ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hC0' : ((Nat.choose (2*n) (i+1) : ℕ):ℚ)
      = ((Nat.factorial (2*n) : ℚ)) /
        (((Nat.factorial (i+1) : ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℚ))) := by
    rw [eq_div_iff (mul_ne_zero hBi hC0f)]
    linear_combination hC0q
  have hD1ne : ((Nat.factorial (2*n+2-(i+1)) : ℕ):ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hC1' : ((Nat.choose (2*n+2) (i+1) : ℕ):ℚ)
      = ((Nat.factorial (2*n+2) : ℚ)) /
        (((Nat.factorial (i+1) : ℚ)) * ((Nat.factorial (2*n+2-(i+1)) : ℚ))) := by
    rw [eq_div_iff (mul_ne_zero hBi hD1ne)]
    linear_combination hC1q
  rw [e2np1, hC0', hC1', hB, hA2, hD1, hF1]
  have s2 : ((2*n-(i+1) : ℕ):ℚ) = 2*(n:ℚ)-(((i:ℕ):ℚ)+1) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have t1 : ((2*n+1-(i+1) : ℕ):ℚ) = (2*(n:ℚ)+1-(((i:ℕ):ℚ)+1)) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  simp only [s2, t1]
  have u1 : ((2*(n:ℚ)+1-(((i:ℕ):ℚ)+1))+1) = (2*(n:ℚ)+1-(i:ℚ)) := by ring
  have u2 : ((2*(n:ℚ)-(((i:ℕ):ℚ)+1))+1) = (2*(n:ℚ)-(i:ℚ)) := by ring
  simp only [u1, u2]
  push_cast
  -- Nonvanishing facts for the atoms.
  have hk2q : (i:ℚ)+1 ≤ 2*(n:ℚ) := by exact_mod_cast hk2'
  have hI1 : ((i:ℚ)+1) ≠ 0 := by positivity
  have hM : ((Nat.factorial i : ℕ):ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hC : ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hA : ((Nat.factorial (2*n) : ℕ):ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hJ0 : (2*(n:ℚ)-(i:ℚ)) ≠ 0 := ne_of_gt (by linarith)
  have hJ2 : (2*(n:ℚ)+1-(i:ℚ)) ≠ 0 := ne_of_gt (by linarith)
  -- Ring-normalized variants (field_simp normalizes denominators before discharging).
  have hJ0n : ((n:ℚ)*2 - (i:ℚ)) ≠ 0 := ne_of_gt (by linarith)
  have hJ2n : (1 + (n:ℚ)*2 - (i:ℚ)) ≠ 0 := ne_of_gt (by linarith)
  have hU : (-1:ℚ)^(i+1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hkf : ((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ) ≠ 0 := mul_ne_zero hI1 hM
  have hd : (2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ) ≠ 0 :=
    mul_ne_zero hJ0 hC
  have he1 : (2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)) ≠ 0 :=
    mul_ne_zero hJ2 hd
  have hda : ((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ) *
      ((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))) ≠ 0 :=
    mul_ne_zero hkf he1
  have hdb : ((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ) ≠ 0 :=
    mul_ne_zero hkf hC
  have hdc : (((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ))^3 *
      ((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hkf) (pow_ne_zero 3 hd)
  have hdd : ((Nat.factorial i : ℕ):ℚ)^3 *
      ((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hM) (pow_ne_zero 3 he1)
  have hDEN0 : (((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ))^3 *
      ((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3 *
      (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
      (((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3 *
      (((Nat.factorial i : ℕ):ℚ))^3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hkf)
      (pow_ne_zero 3 he1)) (pow_ne_zero 3 hC)) (pow_ne_zero 3 hd)) (pow_ne_zero 3 hM)
  -- Bridge: (LHS - RHS) * DEN0 = U * A^3 * P.
  -- Clear rewrite-equalities so `field_simp` cannot loop on them.
  clear hC0q hC1q hB hA2 hD1 hF1 hC0' hC1' s2 t1 u1 u2 e2n hneg e2np1 gk gk1 hk1 hk2 hk2'
  -- Four small bridges: each cleared separately so `field_simp` stays small.
  have hbr1 : (((n:ℚ)+1)^2 *
        ((-1:ℚ)^(i+1) *
          (((2*(n:ℚ)+2)*(2*(n:ℚ)+1) * ((Nat.factorial (2*n) : ℕ):ℚ) /
            (((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ) *
              ((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) *
                ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))))^3))
      * ((((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ))^3 *
        (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) *
          ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
        (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
        ((((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
        ((((Nat.factorial i : ℕ):ℚ)))^3)
      = (-1:ℚ)^(i+1) * (((Nat.factorial (2*n) : ℕ):ℚ))^3 *
        (((n:ℚ)+1)^2 * ((2*(n:ℚ)+2)*(2*(n:ℚ)+1))^3 *
          (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
          (((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3 *
          (((Nat.factorial i : ℕ):ℚ))^3) := by
    field_simp
    linear_combination mul_inv_cancel₀ hJ2n
  have hbr2 : (3*(3*(n:ℚ)+1)*(3*(n:ℚ)+2) *
        ((-1:ℚ)^(i+1) * (((Nat.factorial (2*n) : ℕ):ℚ) /
          (((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ) *
            ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3))
      * ((((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ))^3 *
        (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) *
          ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
        (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
        ((((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
        ((((Nat.factorial i : ℕ):ℚ)))^3)
      = (-1:ℚ)^(i+1) * (((Nat.factorial (2*n) : ℕ):ℚ))^3 *
        ((3*(3*(n:ℚ)+1)*(3*(n:ℚ)+2)) *
          (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
          (((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3 *
          (((Nat.factorial i : ℕ):ℚ))^3) := by
    field_simp
  have hbr3 : (((-1:ℚ)^(i+1) * ((Nat.factorial (2*n) : ℕ):ℚ)^3 *
          xpoly (n:ℚ) ((i:ℚ)+1+1) /
          ((((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ))^3 *
            (((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3)))
      * ((((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ))^3 *
        (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) *
          ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
        (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
        ((((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
        ((((Nat.factorial i : ℕ):ℚ)))^3)
      = (-1:ℚ)^(i+1) * (((Nat.factorial (2*n) : ℕ):ℚ))^3 *
        (xpoly (n:ℚ) ((i:ℚ)+1+1) *
          (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
          (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
          (((Nat.factorial i : ℕ):ℚ))^3) := by
    field_simp
  have hbr4 : (((-1:ℚ)^(i+1) * ((Nat.factorial (2*n) : ℕ):ℚ)^3 *
          xpoly (n:ℚ) ((i:ℚ)+1) /
          ((((Nat.factorial i : ℕ):ℚ))^3 *
            (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) *
              ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3)))
      * ((((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ))^3 *
        (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) *
          ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
        (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
        ((((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
        ((((Nat.factorial i : ℕ):ℚ)))^3)
      = (-1:ℚ)^(i+1) * (((Nat.factorial (2*n) : ℕ):ℚ))^3 *
        (xpoly (n:ℚ) ((i:ℚ)+1) *
          ((((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ)))^3 *
          (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
          (((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3) := by
    field_simp
  -- Cleared numerator identity, a multiple of the Gosper identity.
  have hP : ((n:ℚ)+1)^2 * ((2*(n:ℚ)+2)*(2*(n:ℚ)+1))^3 *
        (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
        (((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3 *
        (((Nat.factorial i : ℕ):ℚ))^3
      + (3*(3*(n:ℚ)+1)*(3*(n:ℚ)+2)) *
        (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
        (((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3 *
        (((Nat.factorial i : ℕ):ℚ))^3
      + xpoly (n:ℚ) ((i:ℚ)+1+1) *
        (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
        (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
        (((Nat.factorial i : ℕ):ℚ))^3
      + xpoly (n:ℚ) ((i:ℚ)+1) *
        ((((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ)))^3 *
        (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
        (((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3 = 0 := by
    have g := gosper_identity (n:ℚ) ((i:ℚ)+1)
    unfold npoly at g
    linear_combination (-((((Nat.factorial i : ℕ):ℚ))^3 *
      (2*(n:ℚ)+1-((i:ℚ)+1))^3 * (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^6)) * g
  have hfin : (((n:ℚ)+1)^2 *
        ((-1:ℚ)^(i+1) *
          (((2*(n:ℚ)+2)*(2*(n:ℚ)+1) * ((Nat.factorial (2*n) : ℕ):ℚ) /
            (((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ) *
              ((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) *
                ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))))^3) +
      3*(3*(n:ℚ)+1)*(3*(n:ℚ)+2) *
        ((-1:ℚ)^(i+1) * (((Nat.factorial (2*n) : ℕ):ℚ) /
          (((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ) *
            ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3)
      - (-(-1:ℚ)^(i+1) * ((Nat.factorial (2*n) : ℕ):ℚ)^3 *
          xpoly (n:ℚ) ((i:ℚ)+1+1) /
          ((((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ))^3 *
            (((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3) -
        (-1:ℚ)^(i+1) * ((Nat.factorial (2*n) : ℕ):ℚ)^3 *
          xpoly (n:ℚ) ((i:ℚ)+1) /
          ((((Nat.factorial i : ℕ):ℚ))^3 *
            (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) *
              ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3)))
      * ((((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ))^3 *
        (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) *
          ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
        (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
        ((((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
        ((((Nat.factorial i : ℕ):ℚ)))^3) = 0 := calc
    (((n:ℚ)+1)^2 *
        ((-1:ℚ)^(i+1) *
          (((2*(n:ℚ)+2)*(2*(n:ℚ)+1) * ((Nat.factorial (2*n) : ℕ):ℚ) /
            (((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ) *
              ((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) *
                ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))))^3) +
      3*(3*(n:ℚ)+1)*(3*(n:ℚ)+2) *
        ((-1:ℚ)^(i+1) * (((Nat.factorial (2*n) : ℕ):ℚ) /
          (((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ) *
            ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3)
      - (-(-1:ℚ)^(i+1) * ((Nat.factorial (2*n) : ℕ):ℚ)^3 *
          xpoly (n:ℚ) ((i:ℚ)+1+1) /
          ((((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ))^3 *
            (((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3) -
        (-1:ℚ)^(i+1) * ((Nat.factorial (2*n) : ℕ):ℚ)^3 *
          xpoly (n:ℚ) ((i:ℚ)+1) /
          ((((Nat.factorial i : ℕ):ℚ))^3 *
            (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) *
              ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3)))
      * ((((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ))^3 *
        (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) *
          ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
        (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
        ((((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
        ((((Nat.factorial i : ℕ):ℚ)))^3)
        = (-1:ℚ)^(i+1) * (((Nat.factorial (2*n) : ℕ):ℚ))^3 *
        (((n:ℚ)+1)^2 * ((2*(n:ℚ)+2)*(2*(n:ℚ)+1))^3 *
          (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
          (((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3 *
          (((Nat.factorial i : ℕ):ℚ))^3
        + (3*(3*(n:ℚ)+1)*(3*(n:ℚ)+2)) *
          (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
          (((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3 *
          (((Nat.factorial i : ℕ):ℚ))^3
        + xpoly (n:ℚ) ((i:ℚ)+1+1) *
          (((2*(n:ℚ)+1-(i:ℚ)) * ((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))))^3 *
          (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
          (((Nat.factorial i : ℕ):ℚ))^3
        + xpoly (n:ℚ) ((i:ℚ)+1) *
          ((((i:ℚ)+1) * ((Nat.factorial i : ℕ):ℚ)))^3 *
          (((Nat.factorial (2*n-(i+1)) : ℕ):ℚ))^3 *
          (((2*(n:ℚ)-(i:ℚ)) * ((Nat.factorial (2*n-(i+1)) : ℕ):ℚ)))^3) := by
      linear_combination hbr1 + hbr2 + hbr3 + hbr4
    _ = 0 := by rw [hP, mul_zero]
  have h2 := (mul_eq_zero.mp hfin).resolve_right hDEN0
  exact sub_eq_zero.mp h2

private lemma key_k0 (n : ℕ) :
    ((n : ℚ)+1)^2 * Fq (n+1) 0 + 3*(3*(n : ℚ)+1)*(3*(n : ℚ)+2) * Fq n 0
      = Gq n 1 - Gq n 0 := by
  have g0 : Gq n 0 = 0 := by simp [Gq]
  rw [g0, sub_zero]
  have hF1 : Fq (n+1) 0 = 1 := by unfold Fq; simp
  have hF0 : Fq n 0 = 1 := by unfold Fq; simp
  rw [hF1, hF0, mul_one, mul_one]
  have h1 : ¬ ((1:ℕ) = 0 ∨ 2*n+3 ≤ 1) := by omega
  unfold Gq
  rw [ite_eq_right h1]
  have e1 : (1:ℕ)-1 = 0 := by omega
  have e2 : 2*n+2-(1:ℕ) = 2*n+1 := by omega
  rw [e1, e2]
  simp only [Nat.factorial_zero, Nat.cast_one, one_pow, pow_one]
  have h21 : ((Nat.factorial (2*n+1) : ℕ):ℚ) = ((2:ℚ)*n+1) * ((Nat.factorial (2*n) : ℕ):ℚ) := by
    have e : 2*n+1 = (2*n)+1 := by omega
    rw [e, Nat.factorial_succ]
    push_cast
    ring
  rw [h21]
  have hpos1 : ((2:ℚ)*n+1) ≠ 0 := by positivity
  have hfact : ((Nat.factorial (2*n) : ℕ):ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hD : ((2:ℚ)*n+2)^3 ≠ 0 := by
    apply pow_ne_zero 3
    positivity
  field_simp
  have gosp := gosper_identity (n:ℚ) 0
  unfold npoly at gosp
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
    sub_zero, zero_add] at gosp
  have hmul : (-(((2:ℚ)*n+2)^3)) *
      ((((n:ℚ)+1)^2 + 3*(3*(n:ℚ)+1)*(3*(n:ℚ)+2)) * ((n:ℚ)*2+1)^3 +
        xpoly (n:ℚ) 1) = 0 := by
    linear_combination gosp
  have h2 := (mul_eq_zero.mp hmul).resolve_left (by simpa using hD)
  linear_combination h2

private lemma key_upper1 (n : ℕ) :
    ((n : ℚ)+1)^2 * Fq (n+1) (2*n+1) + 3*(3*(n : ℚ)+1)*(3*(n : ℚ)+2) * Fq n (2*n+1)
      = Gq n (2*n+2) - Gq n (2*n+1) := by
  have hF0 : Fq n (2*n+1) = 0 := by
    unfold Fq
    have h : Nat.choose (2*n) (2*n+1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h]
    simp
  have hC : Nat.choose (2*(n+1)) (2*n+1) = 2*n+2 := by
    have e : 2*(n+1) = (2*n+1)+1 := by omega
    rw [e, Nat.choose_succ_self_right]
  have hodd : Odd (2*n+1) := ⟨n, rfl⟩
  have hev : Even (2*n+2) := ⟨n+1, by ring⟩
  have hF1 : Fq (n+1) (2*n+1) = -((2*(n:ℚ)+2)^3) := by
    unfold Fq
    rw [hC, hodd.neg_one_pow]
    push_cast
    ring
  rw [hF1, hF0, mul_zero, add_zero]
  have g2 : ¬ (2*n+2 = 0 ∨ 2*n+3 ≤ 2*n+2) := by omega
  have g1 : ¬ (2*n+1 = 0 ∨ 2*n+3 ≤ 2*n+1) := by omega
  unfold Gq
  rw [ite_eq_right g2, ite_eq_right g1]
  have e1 : (2*n+2-1 : ℕ) = 2*n+1 := by omega
  have e2 : (2*n+2-(2*n+2) : ℕ) = 0 := by omega
  have e3 : (2*n+1-1 : ℕ) = 2*n := by omega
  have e4 : (2*n+2-(2*n+1) : ℕ) = 1 := by omega
  rw [e1, e2, e3, e4]
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, one_pow, mul_one]
  rw [hev.neg_one_pow, hodd.neg_one_pow]
  have h21 : ((Nat.factorial (2*n+1) : ℕ):ℚ) = ((2:ℚ)*n+1) * ((Nat.factorial (2*n) : ℕ):ℚ) := by
    have e : 2*n+1 = (2*n)+1 := by omega
    rw [e, Nat.factorial_succ]
    push_cast
    ring
  rw [h21]
  have ecast : ((2*n+2 : ℕ):ℚ) = ((2*n+1 : ℕ):ℚ)+1 := by push_cast; ring
  rw [ecast]
  have c1 : ((2*n+1 : ℕ):ℚ) = 2*(n:ℚ)+1 := by push_cast; ring
  rw [c1]
  have hpos1 : ((2:ℚ)*n+1) ≠ 0 := by positivity
  have hfact : ((Nat.factorial (2*n) : ℕ):ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  have gosp := gosper_identity (n:ℚ) ((n:ℚ)*2+1)
  unfold npoly at gosp
  linear_combination gosp

private lemma key_upper2 (n : ℕ) :
    ((n : ℚ)+1)^2 * Fq (n+1) (2*n+2) + 3*(3*(n : ℚ)+1)*(3*(n : ℚ)+2) * Fq n (2*n+2)
      = Gq n (2*n+3) - Gq n (2*n+2) := by
  have hev : Even (2*n+2) := ⟨n+1, by ring⟩
  have hF1 : Fq (n+1) (2*n+2) = 1 := by
    unfold Fq
    have e : 2*(n+1) = 2*n+2 := by omega
    rw [e, Nat.choose_self, hev.neg_one_pow]
    simp
  have hF0 : Fq n (2*n+2) = 0 := by
    unfold Fq
    have h : Nat.choose (2*n) (2*n+2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h]
    simp
  have g3 : Gq n (2*n+3) = 0 := by simp [Gq]
  rw [hF1, hF0, g3, mul_one, mul_zero, add_zero, zero_sub]
  have gk : ¬ (2*n+2 = 0 ∨ 2*n+3 ≤ 2*n+2) := by omega
  unfold Gq
  rw [ite_eq_right gk]
  have e1 : (2*n+2-1 : ℕ) = 2*n+1 := by omega
  have e2 : (2*n+2-(2*n+2) : ℕ) = 0 := by omega
  rw [e1, e2]
  simp only [Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
  rw [hev.neg_one_pow]
  have h21 : ((Nat.factorial (2*n+1) : ℕ):ℚ) = ((2:ℚ)*n+1) * ((Nat.factorial (2*n) : ℕ):ℚ) := by
    have e : 2*n+1 = (2*n)+1 := by omega
    rw [e, Nat.factorial_succ]
    push_cast
    ring
  rw [h21]
  have ecast : ((2*n+2 : ℕ):ℚ) = ((2*n+1 : ℕ):ℚ)+1 := by push_cast; ring
  rw [ecast]
  have c1 : ((2*n+1 : ℕ):ℚ) = (n:ℚ)*2+1 := by push_cast; ring
  rw [c1]
  have hpos1 : ((2:ℚ)*n+1) ≠ 0 := by positivity
  have hfact : ((Nat.factorial (2*n) : ℕ):ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hD : ((n:ℚ)*2+2)^3 ≠ 0 := by
    apply pow_ne_zero 3
    positivity
  field_simp
  have gosp := gosper_identity (n:ℚ) ((n:ℚ)*2+1+1)
  unfold npoly at gosp
  have hmul : (-(((n:ℚ)*2+2)^3)) *
      (((n:ℚ)+1)^2 * (((n:ℚ)*2+1)^3) + xpoly (n:ℚ) ((n:ℚ)*2+1+1)) = 0 := by
    linear_combination gosp
  have h2 := (mul_eq_zero.mp hmul).resolve_left (by simpa using hD)
  linear_combination h2

private lemma key_tail (n k : ℕ) (hk : 2 * n + 3 ≤ k) :
    ((n : ℚ)+1)^2 * Fq (n+1) k + 3*(3*(n : ℚ)+1)*(3*(n : ℚ)+2) * Fq n k
      = Gq n (k+1) - Gq n k := by
  have hFk1 : Fq (n+1) k = 0 := by
    unfold Fq
    have h : Nat.choose (2*(n+1)) k = 0 := by
      apply Nat.choose_eq_zero_of_lt
      omega
    rw [h]
    simp
  have hFk : Fq n k = 0 := by
    unfold Fq
    have h : Nat.choose (2*n) k = 0 := by
      apply Nat.choose_eq_zero_of_lt
      omega
    rw [h]
    simp
  have gk : (k = 0 ∨ 2*n+3 ≤ k) := Or.inr hk
  have gk1 : (k+1 = 0 ∨ 2*n+3 ≤ k+1) := Or.inr (by omega)
  have e1 : Gq n k = 0 := by simp [Gq, gk]
  have e2 : Gq n (k+1) = 0 := by
    unfold Gq
    rw [ite_eq_left gk1]
  rw [hFk1, hFk, e1, e2]
  ring

private noncomputable def Sq (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (2*n+1), Fq n k

private noncomputable def Dq (n : ℕ) : ℚ :=
  (-1 : ℚ)^n * (Nat.factorial (3*n) : ℚ) / ((Nat.factorial n : ℚ)^3)

private lemma key_identity (n k : ℕ) :
    ((n : ℚ)+1)^2 * Fq (n+1) k + 3*(3*(n : ℚ)+1)*(3*(n : ℚ)+2) * Fq n k
      = Gq n (k+1) - Gq n k := by
  by_cases hk0 : k = 0
  · subst hk0
    exact key_k0 n
  · by_cases hk2 : k ≤ 2*n
    · by_cases hk1 : 1 ≤ k
      · exact key_interior n k hk1 hk2
      · omega
    · by_cases hk3 : k ≤ 2*n+2
      · by_cases hk4 : k ≤ 2*n+1
        · have hkk : k = 2*n+1 := by omega
          rw [hkk]
          exact key_upper1 n
        · have hkk : k = 2*n+2 := by omega
          rw [hkk]
          exact key_upper2 n
      · exact key_tail n k (by omega)

private lemma Fq_eq_zero_of_lt (n k : ℕ) (h : 2 * n < k) : Fq n k = 0 := by
  unfold Fq
  have hh : Nat.choose (2*n) k = 0 := Nat.choose_eq_zero_of_lt h
  rw [hh]
  simp

private lemma Sq_recurrence (n : ℕ) :
    ((n : ℚ)+1)^2 * Sq (n+1) + 3*(3*(n : ℚ)+1)*(3*(n : ℚ)+2) * Sq n = 0 := by
  have h2 : 2*(n+1)+1 = 2*n+3 := by omega
  unfold Sq
  rw [h2]
  have hF1 : Fq n (2*n+1) = 0 := Fq_eq_zero_of_lt n _ (by omega)
  have hF2 : Fq n (2*n+2) = 0 := Fq_eq_zero_of_lt n _ (by omega)
  have hsum : ∑ k ∈ Finset.range (2*n+3), Fq n k = ∑ k ∈ Finset.range (2*n+1), Fq n k := by
    have e1 : 2*n+3 = (2*n+2)+1 := by omega
    have e2 : 2*n+2 = (2*n+1)+1 := by omega
    rw [e1, Finset.sum_range_succ, e2, Finset.sum_range_succ, hF1, hF2, add_zero, add_zero]
  have hH : (∑ k ∈ Finset.range (2*n+3),
      (((n:ℚ)+1)^2 * Fq (n+1) k + 3*(3*(n:ℚ)+1)*(3*(n:ℚ)+2) * Fq n k))
      = ((n:ℚ)+1)^2 * (∑ k ∈ Finset.range (2*n+3), Fq (n+1) k)
        + 3*(3*(n:ℚ)+1)*(3*(n:ℚ)+2) * (∑ k ∈ Finset.range (2*n+3), Fq n k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [hsum] at hH
  have htel : (∑ k ∈ Finset.range (2*n+3),
      (((n:ℚ)+1)^2 * Fq (n+1) k + 3*(3*(n:ℚ)+1)*(3*(n:ℚ)+2) * Fq n k)) = 0 := by
    have hterm : ∀ k ∈ Finset.range (2*n+3),
        (((n:ℚ)+1)^2 * Fq (n+1) k + 3*(3*(n:ℚ)+1)*(3*(n:ℚ)+2) * Fq n k)
        = (Gq n (k+1) - Gq n k) := fun k _ => key_identity n k
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_range_sub]
    have g0 : Gq n 0 = 0 := by simp [Gq]
    have g3 : Gq n (2*n+3) = 0 := by simp [Gq]
    rw [g3, g0, sub_zero]
  rw [htel] at hH
  linarith

private lemma Dq_recurrence (n : ℕ) :
    ((n : ℚ)+1)^2 * Dq (n+1) + 3*(3*(n : ℚ)+1)*(3*(n : ℚ)+2) * Dq n = 0 := by
  unfold Dq
  have hfact : ∀ m : ℕ, ((Nat.factorial m : ℕ) : ℚ) ≠ 0 := fun m =>
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have h1 : ((Nat.factorial (3*(n+1)) : ℕ):ℚ) =
      ((3*(n:ℚ)+3)*(3*(n:ℚ)+2)*(3*(n:ℚ)+1)) * ((Nat.factorial (3*n) : ℕ):ℚ) := by
    have e : 3*(n+1) = (3*n+2)+1 := by omega
    have e2 : 3*n+2 = (3*n+1)+1 := by omega
    have e3 : 3*n+1 = (3*n)+1 := by omega
    rw [e, Nat.factorial_succ, e2, Nat.factorial_succ, e3, Nat.factorial_succ]
    push_cast
    ring
  have h2 : ((Nat.factorial (n+1) : ℕ):ℚ) = ((n:ℚ)+1) * ((Nat.factorial n : ℕ):ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hneg : (-1:ℚ)^(n+1) = -(-1:ℚ)^n := by rw [pow_succ]; ring
  rw [h1, h2, hneg]
  have hn1 : ((n:ℚ)+1) ≠ 0 := by positivity
  field_simp
  ring

private lemma Sq_eq_Dq (n : ℕ) : Sq n = Dq n := by
  induction n with
  | zero =>
    have hS0 : Sq 0 = 1 := by
      have hr : Finset.range (2*0+1) = {0} := by decide
      unfold Sq
      rw [hr, Finset.sum_singleton]
      unfold Fq
      simp
    have hD0 : Dq 0 = 1 := by
      unfold Dq
      simp
    rw [hS0, hD0]
  | succ k ih =>
    have hS := Sq_recurrence k
    have hD := Dq_recurrence k
    have h2 : ((k:ℚ)+1)^2 * (Sq (k+1) - Dq (k+1)) = 0 := by
      have hS' := hS
      rw [ih] at hS'
      linear_combination hS' - hD
    have hne : ((k:ℚ)+1)^2 ≠ 0 := by positivity
    have h3 : Sq (k+1) - Dq (k+1) = 0 := (mul_eq_zero.mp h2).resolve_left hne
    exact sub_eq_zero.mp h3

private lemma choose_prod_eq (n : ℕ) :
    ((Nat.choose (2*n) n : ℕ) : ℚ) * ((Nat.choose (3*n) (2*n) : ℕ) : ℚ)
      = (Nat.factorial (3*n) : ℚ) / ((Nat.factorial n : ℚ)^3) := by
  have h1 : Nat.choose (2*n) n * Nat.factorial n * Nat.factorial n = Nat.factorial (2*n) := by
    have hle : n ≤ 2*n := Nat.le_mul_of_pos_left n (by omega)
    have h := Nat.choose_mul_factorial_mul_factorial hle
    have hsub : 2*n - n = n := by omega
    rwa [hsub] at h
  have h2 : Nat.choose (3*n) (2*n) * Nat.factorial (2*n) * Nat.factorial n
      = Nat.factorial (3*n) := by
    have hle : 2*n ≤ 3*n := by omega
    have h := Nat.choose_mul_factorial_mul_factorial hle
    have hsub : 3*n - 2*n = n := by omega
    rwa [hsub] at h
  have hfact : ∀ m : ℕ, ((Nat.factorial m : ℕ) : ℚ) ≠ 0 := fun m =>
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have h1q : ((Nat.choose (2*n) n : ℕ) : ℚ) * (Nat.factorial n : ℚ) * (Nat.factorial n : ℚ)
      = (Nat.factorial (2*n) : ℚ) := by exact_mod_cast h1
  have h2q : ((Nat.choose (3*n) (2*n) : ℕ) : ℚ) * (Nat.factorial (2*n) : ℚ) * (Nat.factorial n : ℚ)
      = (Nat.factorial (3*n) : ℚ) := by exact_mod_cast h2
  field_simp
  linear_combination (((Nat.choose (3*n) (2*n) : ℕ) : ℚ) * (Nat.factorial n : ℚ)) * h1q + h2q

/-- **Dixon's alternating cubic binomial sum.** For every natural number $n$,
$\sum_{k=0}^{2n} (-1)^k \binom{2n}{k}^3 = (-1)^n \binom{2n}{n} \binom{3n}{2n}$.

Mikić attributes the identity to A. C. Dixon, "On the sum of the cubes of the
coefficients in a certain expansion by the binomial theorem", Messenger of
Mathematics 20 (1891), 79--80. This is the specialization of Dixon's three-parameter
identity in which all three parameters equal $n$; the three-parameter identity is not stated.

Proves `Wanted` entry `dixon_alternating_cubic_binomial_sum`.

Source: Jovan Mikić, "A Method For Examining Divisibility Properties Of Some
Binomial Sums", Journal of Integer Sequences 21 (2018), Article 18.8.7,
<https://cs.uwaterloo.ca/journals/JIS/VOL21/Mikic/mikic25.tex>,
equation (2.0.1), lines 119--124. Source file SHA-256
`6a6fc0f14a3e02c8d5cbbbb626412ac1151d9853c1ebf6ce8860b8b98d4306a2`,
canonical source-span SHA-256
`8511f3d8adc6b3c69d4bcc08bd4f88b9c62c93b1ff2fd0c01dd3fe720b7df3a2`.
-/
theorem dixon_alternating_cubic_binomial_sum (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1),
      (-1 : ℤ) ^ k * (Nat.choose (2 * n) k : ℤ) ^ 3 =
      (-1 : ℤ) ^ n * (Nat.choose (2 * n) n : ℤ) *
        (Nat.choose (3 * n) (2 * n) : ℤ) := by
  have hQ := Sq_eq_Dq n
  have hSQ : ((∑ k ∈ Finset.range (2*n+1), (-1:ℤ)^k * ((Nat.choose (2*n) k : ℤ))^3 : ℤ) : ℚ)
      = Sq n := by
    unfold Sq Fq
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hDQ : (((-1:ℤ)^n * (Nat.choose (2*n) n : ℤ) * (Nat.choose (3*n) (2*n) : ℤ) : ℤ) : ℚ)
      = Dq n := by
    unfold Dq
    have h := choose_prod_eq n
    push_cast
    linear_combination (-1:ℚ)^n * h
  have hcast : ((∑ k ∈ Finset.range (2*n+1), (-1:ℤ)^k * ((Nat.choose (2*n) k : ℤ))^3 : ℤ) : ℚ)
      = (((-1:ℤ)^n * (Nat.choose (2*n) n : ℤ) * (Nat.choose (3*n) (2*n) : ℤ) : ℤ) : ℚ) := by
    rw [hSQ, hDQ, hQ]
  exact_mod_cast hcast

end MetaMathlibExt
