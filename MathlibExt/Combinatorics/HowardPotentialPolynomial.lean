/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.PartialBellPolynomial
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

-- Helper lemmas for the proof below (degree bound for the RHS sum).
-- The remaining hard step is the pointwise evaluation identity, which needs a
-- Bell-polynomial / power-series coefficient identity with no Mathlib API.
namespace MetaMathlibExt

open scoped BigOperators

section

private theorem howard_rhs_summand_natDegree_le (n i : ℕ) (hi : i ≤ n) :
    (Polynomial.C (((-1 : Rat) ^ i) * ((2 : Rat) ^ i) *
      (((n.factorial : Rat) * (i.factorial : Rat)) / (((n + 2 * i).factorial : Rat)))) *
    ((ascPochhammer Rat i) * Polynomial.C (((i.factorial : Rat))⁻¹)) *
    (((descPochhammer Rat (n - i)).comp (Polynomial.X + Polynomial.C (n : Rat))) *
      Polynomial.C ((((n - i).factorial : Rat))⁻¹)) *
    Polynomial.C (MetaMathlibExt.partialBellPolynomial (n + 2 * i) i
      (fun j => if 2 ≤ j then (1 : Rat) else 0))).natDegree ≤ n := by
  have h1 : ((ascPochhammer Rat i) * Polynomial.C (((i.factorial : Rat))⁻¹)).natDegree ≤ i := by
    calc ((ascPochhammer Rat i) * Polynomial.C (((i.factorial : Rat))⁻¹)).natDegree
        ≤ (ascPochhammer Rat i).natDegree := Polynomial.natDegree_mul_C_le _ _
      _ = i := ascPochhammer_natDegree _ _
  have h2 : (((descPochhammer Rat (n - i)).comp (Polynomial.X + Polynomial.C (n : Rat))) *
      Polynomial.C ((((n - i).factorial : Rat))⁻¹)).natDegree ≤ n - i := by
    calc (((descPochhammer Rat (n - i)).comp (Polynomial.X + Polynomial.C (n : Rat))) *
        Polynomial.C ((((n - i).factorial : Rat))⁻¹)).natDegree
        ≤ ((descPochhammer Rat (n - i)).comp (Polynomial.X + Polynomial.C (n : Rat))).natDegree :=
          Polynomial.natDegree_mul_C_le _ _
      _ = n - i := by
          rw [Polynomial.natDegree_comp, descPochhammer_natDegree,
            Polynomial.natDegree_X_add_C, mul_one]
  have h3 : (Polynomial.C (((-1 : Rat) ^ i) * ((2 : Rat) ^ i) *
      (((n.factorial : Rat) * (i.factorial : Rat)) / (((n + 2 * i).factorial : Rat)))) *
    ((ascPochhammer Rat i) * Polynomial.C (((i.factorial : Rat))⁻¹)) *
    (((descPochhammer Rat (n - i)).comp (Polynomial.X + Polynomial.C (n : Rat))) *
      Polynomial.C ((((n - i).factorial : Rat))⁻¹))).natDegree ≤ i + (n - i) := by
    calc (Polynomial.C (((-1 : Rat) ^ i) * ((2 : Rat) ^ i) *
        (((n.factorial : Rat) * (i.factorial : Rat)) / (((n + 2 * i).factorial : Rat)))) *
      ((ascPochhammer Rat i) * Polynomial.C (((i.factorial : Rat))⁻¹)) *
      (((descPochhammer Rat (n - i)).comp (Polynomial.X + Polynomial.C (n : Rat))) *
        Polynomial.C ((((n - i).factorial : Rat))⁻¹))).natDegree
        ≤ (Polynomial.C (((-1 : Rat) ^ i) * ((2 : Rat) ^ i) *
          (((n.factorial : Rat) * (i.factorial : Rat)) / (((n + 2 * i).factorial : Rat)))) *
        ((ascPochhammer Rat i) * Polynomial.C (((i.factorial : Rat))⁻¹))).natDegree +
          ((((descPochhammer Rat (n - i)).comp (Polynomial.X + Polynomial.C (n : Rat))) *
            Polynomial.C ((((n - i).factorial : Rat))⁻¹))).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ i + (n - i) := by
          have hfront : (Polynomial.C (((-1 : Rat) ^ i) * ((2 : Rat) ^ i) *
            (((n.factorial : Rat) * (i.factorial : Rat)) / (((n + 2 * i).factorial : Rat)))) *
          ((ascPochhammer Rat i) * Polynomial.C (((i.factorial : Rat))⁻¹))).natDegree ≤ i :=
            le_trans (Polynomial.natDegree_C_mul_le _ _) h1
          exact Nat.add_le_add hfront h2
  calc (Polynomial.C (((-1 : Rat) ^ i) * ((2 : Rat) ^ i) *
      (((n.factorial : Rat) * (i.factorial : Rat)) / (((n + 2 * i).factorial : Rat)))) *
    ((ascPochhammer Rat i) * Polynomial.C (((i.factorial : Rat))⁻¹)) *
    (((descPochhammer Rat (n - i)).comp (Polynomial.X + Polynomial.C (n : Rat))) *
      Polynomial.C ((((n - i).factorial : Rat))⁻¹)) *
    Polynomial.C (MetaMathlibExt.partialBellPolynomial (n + 2 * i) i
      (fun j => if 2 ≤ j then (1 : Rat) else 0))).natDegree
      ≤ (Polynomial.C (((-1 : Rat) ^ i) * ((2 : Rat) ^ i) *
        (((n.factorial : Rat) * (i.factorial : Rat)) / (((n + 2 * i).factorial : Rat)))) *
      ((ascPochhammer Rat i) * Polynomial.C (((i.factorial : Rat))⁻¹)) *
      (((descPochhammer Rat (n - i)).comp (Polynomial.X + Polynomial.C (n : Rat))) *
        Polynomial.C ((((n - i).factorial : Rat))⁻¹))).natDegree :=
        Polynomial.natDegree_mul_C_le _ _
    _ ≤ i + (n - i) := h3
    _ = n := Nat.add_sub_cancel' hi

private theorem howard_rhs_natDegree_le (n : ℕ) :
    (Finset.sum (Finset.range (n + 1)) (fun i =>
      Polynomial.C (((-1 : Rat) ^ i) * ((2 : Rat) ^ i) *
        (((n.factorial : Rat) * (i.factorial : Rat)) / (((n + 2 * i).factorial : Rat)))) *
      ((ascPochhammer Rat i) * Polynomial.C (((i.factorial : Rat))⁻¹)) *
      (((descPochhammer Rat (n - i)).comp (Polynomial.X + Polynomial.C (n : Rat))) *
        Polynomial.C ((((n - i).factorial : Rat))⁻¹)) *
      Polynomial.C (MetaMathlibExt.partialBellPolynomial (n + 2 * i) i
        (fun j => if 2 ≤ j then (1 : Rat) else 0)))).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [Finset.mem_range] at hi
  exact howard_rhs_summand_natDegree_le n i (Nat.lt_succ_iff.mp hi)

private theorem howard_eq_of_deg_le_of_eval_eq (n : ℕ) (P Q : Polynomial Rat)
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n)
    (heq : ∀ m : ℕ, m ≤ n → Q.eval (↑m : Rat) = P.eval (↑m : Rat)) :
    P = Q := by
  have hsub_deg : (P - Q).natDegree ≤ n :=
    le_trans (Polynomial.natDegree_sub_le _ _) (max_le hP hQ)
  have hroots : ∀ i : Fin (n + 1), (P - Q).eval ((i.val : ℕ) : Rat) = 0 := by
    intro i
    rw [Polynomial.eval_sub, heq i.val (Nat.lt_succ_iff.mp i.isLt), sub_self]
  have hinj : Function.Injective (fun i : Fin (n + 1) => ((i.val : ℕ) : Rat)) := by
    intro a b hab
    simp only at hab
    have hcast : (a.val : ℕ) = (b.val : ℕ) := by exact_mod_cast hab
    exact Fin.ext hcast
  have hlt : (P - Q).natDegree < Fintype.card (Fin (n + 1)) := by
    rw [Fintype.card_fin]
    exact Nat.lt_succ_of_le hsub_deg
  have hzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (P - Q) hinj hroots hlt
  exact sub_eq_zero.mp hzero

private noncomputable def howardG : PowerSeries Rat :=
  PowerSeries.mk (fun k => (2 : Rat) / (((k + 2).factorial : Rat)))

private theorem howardG_coeff (k : ℕ) :
    PowerSeries.coeff k howardG = (2 : Rat) / (((k + 2).factorial : Rat)) := by
  rw [howardG, PowerSeries.coeff_mk]

private theorem howardG_constantCoeff : PowerSeries.constantCoeff howardG = 1 := by
  have h0 : (((0 + 2).factorial : ℕ) : Rat) = 2 := by norm_num
  have h : PowerSeries.constantCoeff howardG
      = (2 : Rat) / (((0 + 2).factorial : Rat)) := by
    rw [howardG, PowerSeries.constantCoeff_mk]
  rw [h, h0]
  norm_num

private theorem howardG_constantCoeff_ne_zero :
    PowerSeries.constantCoeff howardG ≠ 0 := by
  rw [howardG_constantCoeff]
  norm_num

private theorem howardG_inv_mul : howardG⁻¹ * howardG = 1 :=
  PowerSeries.inv_mul_cancel howardG howardG_constantCoeff_ne_zero

private theorem howardG_mul_inv : howardG * howardG⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel howardG howardG_constantCoeff_ne_zero

private theorem howard_inv_pow_mul_pow (t : ℕ) :
    (howardG⁻¹ ^ t) * (howardG ^ t) = 1 := by
  have h1 : howardG⁻¹ * howardG = 1 := howardG_inv_mul
  calc (howardG⁻¹ ^ t) * (howardG ^ t)
      = (howardG⁻¹ * howardG) ^ t := by rw [mul_pow]
    _ = 1 := by rw [h1, one_pow]

private theorem howard_pow_mul_inv_pow (t : ℕ) :
    (howardG ^ t) * (howardG⁻¹ ^ t) = 1 := by
  have h1 : howardG * howardG⁻¹ = 1 := howardG_mul_inv
  calc (howardG ^ t) * (howardG⁻¹ ^ t)
      = (howardG * howardG⁻¹) ^ t := by rw [mul_pow]
    _ = 1 := by rw [h1, one_pow]

private theorem howard_sub_one_X_dvd : PowerSeries.X ∣ (howardG - 1) := by
  rw [PowerSeries.X_dvd_iff, map_sub, howardG_constantCoeff,
    PowerSeries.constantCoeff_one, sub_self]

private theorem howard_sub_one_pow_X_dvd (k : ℕ) :
    (PowerSeries.X ^ k) ∣ ((howardG - 1) ^ k) :=
  pow_dvd_pow_of_dvd howard_sub_one_X_dvd k

private noncomputable def howardRsummand (n i : ℕ) : Polynomial Rat :=
  Polynomial.C (((-1 : Rat) ^ i) * ((2 : Rat) ^ i) *
      (((n.factorial : Rat) * (i.factorial : Rat)) / (((n + 2 * i).factorial : Rat)))) *
    ((ascPochhammer Rat i) * Polynomial.C (((i.factorial : Rat))⁻¹)) *
    (((descPochhammer Rat (n - i)).comp (Polynomial.X + Polynomial.C (n : Rat))) *
      Polynomial.C ((((n - i).factorial : Rat))⁻¹)) *
    Polynomial.C (MetaMathlibExt.partialBellPolynomial (n + 2 * i) i
      (fun j => if 2 ≤ j then (1 : Rat) else 0))

private noncomputable def howardR (n : ℕ) : Polynomial Rat :=
  Finset.sum (Finset.range (n + 1)) (fun i => howardRsummand n i)

private theorem howard_asc_eval_neg (i j : ℕ) :
    (ascPochhammer Rat i).eval (-(j : Rat))
      = (-1 : Rat) ^ i * ((j.descFactorial i : ℕ) : Rat) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_descFactorial]

private theorem howard_desc_comp_eval (n i j : ℕ) (hj : j ≤ n) :
    ((descPochhammer Rat (n - i)).comp
      (Polynomial.X + Polynomial.C (n : Rat))).eval (-(j : Rat))
      = ((((n - j).descFactorial (n - i)) : ℕ) : Rat) := by
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  have hcast : (-(j : Rat) + (n : Rat)) = (((n - j : ℕ)) : Rat) := by
    have hsub : (((n - j : ℕ)) : Rat) = (n : Rat) - (j : Rat) := Nat.cast_sub hj
    rw [hsub]
    ring
  rw [hcast, descPochhammer_eval_eq_descFactorial]

private theorem howardRsummand_eval (n i j : ℕ) (hj : j ≤ n) :
    (howardRsummand n i).eval (-(j : Rat))
      = (((-1 : Rat) ^ i) * ((2 : Rat) ^ i) *
          (((n.factorial : Rat) * (i.factorial : Rat))
            / (((n + 2 * i).factorial : Rat)))) *
        (((-1 : Rat) ^ i * ((j.descFactorial i : ℕ) : Rat))
          * (((i.factorial : Rat))⁻¹)) *
        (((((n - j).descFactorial (n - i) : ℕ)) : Rat)
          * ((((n - i).factorial : Rat))⁻¹)) *
        (MetaMathlibExt.partialBellPolynomial (n + 2 * i) i
          (fun j => if 2 ≤ j then (1 : Rat) else 0)) := by
  rw [howardRsummand, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_mul, howard_asc_eval_neg,
    Polynomial.eval_C, Polynomial.eval_mul, howard_desc_comp_eval n i j hj,
    Polynomial.eval_C, Polynomial.eval_C]

private theorem howardRsummand_eval_eq_zero_of_gt (n i j : ℕ) (hj : j ≤ n)
    (h : j < i) : (howardRsummand n i).eval (-(j : Rat)) = 0 := by
  rw [howardRsummand_eval n i j hj]
  have hz : (((j.descFactorial i : ℕ)) : Rat) = 0 := by
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero]
  simp only [hz, mul_zero, zero_mul]

private theorem howardRsummand_eval_eq_zero_of_lt (n i j : ℕ) (hj : j ≤ n)
    (h : i < j) : (howardRsummand n i).eval (-(j : Rat)) = 0 := by
  rw [howardRsummand_eval n i j hj]
  have hlt : n - j < n - i := by omega
  have hz : (((((n - j).descFactorial (n - i)) : ℕ)) : Rat) = 0 := by
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt, Nat.cast_zero]
  simp only [hz, mul_zero, zero_mul]

private theorem howardR_eval_neg_eq_summand (n j : ℕ) (hj : j ≤ n) :
    (howardR n).eval (-(j : Rat))
      = (howardRsummand n j).eval (-(j : Rat)) := by
  rw [howardR, Polynomial.eval_finsetSum]
  apply Finset.sum_eq_single_of_mem j
  · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)
  · intro i hi hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact howardRsummand_eval_eq_zero_of_lt n i j hj h
    · exact howardRsummand_eval_eq_zero_of_gt n i j hj h

private theorem howard_neg_pow_mul_self (j : ℕ) :
    ((-1 : Rat) ^ j) * ((-1 : Rat) ^ j) = 1 := by
  rw [← pow_add]
  have h2j : j + j = 2 * j := by ring
  rw [h2j, pow_mul]
  have hsq : ((-1 : Rat) ^ 2) = 1 := by norm_num
  rw [hsq, one_pow]

private theorem howardRsummand_self (n j : ℕ) (hj : j ≤ n) :
    (howardRsummand n j).eval (-(j : Rat))
      = (((2 : Rat) ^ j * (n.factorial : Rat) * (j.factorial : Rat)
          / (((n + 2 * j).factorial : Rat)))
        * MetaMathlibExt.partialBellPolynomial (n + 2 * j) j
          (fun j => if 2 ≤ j then (1 : Rat) else 0)) := by
  have hdesc_j : j.descFactorial j = j.factorial := Nat.descFactorial_self j
  have hdesc_n : (n - j).descFactorial (n - j) = (n - j).factorial :=
    Nat.descFactorial_self _
  have hj_ne : ((j.factorial : ℕ) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hnj_ne : ((((n - j).factorial : ℕ)) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (n - j).factorial_ne_zero
  rw [howardRsummand_eval n j j hj, hdesc_j, hdesc_n]
  have hA : (((-1 : Rat) ^ j * ((j.factorial : ℕ) : Rat))
      * (((j.factorial : ℕ) : Rat)⁻¹)) = (-1 : Rat) ^ j := by
    rw [mul_assoc, mul_inv_cancel₀ hj_ne, mul_one]
  have hB : (((((n - j).factorial : ℕ)) : Rat)
      * (((((n - j).factorial : ℕ)) : Rat)⁻¹)) = 1 :=
    mul_inv_cancel₀ hnj_ne
  rw [hA, hB, mul_one]
  have hC : (((-1 : Rat) ^ j * (2 : Rat) ^ j *
      (((n.factorial : Rat) * (j.factorial : Rat))
        / (((n + 2 * j).factorial : Rat)))) * (-1 : Rat) ^ j)
      = ((2 : Rat) ^ j * (((n.factorial : Rat) * (j.factorial : Rat))
        / (((n + 2 * j).factorial : Rat)))) := by
    have hneg := howard_neg_pow_mul_self j
    calc (((-1 : Rat) ^ j * (2 : Rat) ^ j *
          (((n.factorial : Rat) * (j.factorial : Rat))
            / (((n + 2 * j).factorial : Rat)))) * (-1 : Rat) ^ j)
        = (((-1 : Rat) ^ j * (-1 : Rat) ^ j) *
          ((2 : Rat) ^ j * (((n.factorial : Rat) * (j.factorial : Rat))
            / (((n + 2 * j).factorial : Rat))))) := by ring
      _ = (1 : Rat) *
          ((2 : Rat) ^ j * (((n.factorial : Rat) * (j.factorial : Rat))
            / (((n + 2 * j).factorial : Rat)))) := by rw [hneg]
      _ = ((2 : Rat) ^ j * (((n.factorial : Rat) * (j.factorial : Rat))
          / (((n + 2 * j).factorial : Rat)))) := by rw [one_mul]
  rw [hC]
  ring

private theorem howard_prod_monomial {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (a : ι → Rat) :
    ∏ i ∈ s, PowerSeries.monomial (d i) (a i)
      = PowerSeries.monomial (∑ i ∈ s, d i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Finset.prod_insert hx, ih,
        PowerSeries.monomial_mul_monomial]

private theorem howard_bell_index_set (n k : ℕ) :
    (Finset.univ.piAntidiag k).filter (fun κ : Fin (n + 1) → ℕ => n = ∑ i, (κ i) * (i.val + 1))
      = (Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range (n + 1))).filter
          (fun j => (∑ i, j i = k) ∧ (∑ i, (i.val + 1) * j i = n)) := by
  ext κ
  simp only [Finset.mem_filter, Finset.mem_piAntidiag, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨⟨hsum, _⟩, hn⟩
    refine ⟨fun i => ?_, hsum, ?_⟩
    · have hle : κ i ≤ ∑ j, (κ j) * (j.val + 1) := by
        calc κ i ≤ (κ i) * (i.val + 1) := Nat.le_mul_of_pos_right _ (by omega)
          _ ≤ ∑ j, (κ j) * (j.val + 1) :=
              Finset.single_le_sum (f := fun j => κ j * (j.val + 1))
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    · calc ∑ i, (i.val + 1) * κ i
            = ∑ i, κ i * (i.val + 1) := Finset.sum_congr rfl (fun i _ => Nat.mul_comm _ _)
        _ = n := hn.symm
  · rintro ⟨_, hsum, hn⟩
    refine ⟨⟨hsum, fun i _ => Finset.mem_univ i⟩, ?_⟩
    calc n = ∑ i, (i.val + 1) * κ i := hn.symm
      _ = ∑ i, κ i * (i.val + 1) := Finset.sum_congr rfl (fun i _ => Nat.mul_comm _ _)

private theorem howard_bell_coeff_pow (c : ℕ → Rat) (n k : ℕ) :
    PowerSeries.coeff n ((PowerSeries.mk (fun m => if m = 0 then 0 else c m)) ^ k)
      = (k.factorial : Rat) * ∑ j ∈ (Fintype.piFinset
          (fun _ : Fin (n + 1) => Finset.range (n + 1))).filter
          (fun j => (∑ i, j i = k) ∧ (∑ i, (i.val + 1) * j i = n)),
          ∏ i, ((c (i.val + 1)) ^ (j i) / (((j i).factorial : ℕ) : Rat)) := by
  have hA : PowerSeries.coeff n ((PowerSeries.mk (fun m => if m = 0 then 0 else c m)) ^ k)
      = PowerSeries.coeff n ((∑ i : Fin (n + 1), PowerSeries.monomial (i.val + 1) (c (i.val + 1))) ^
          k) := by
    set C := PowerSeries.mk (fun m => if m = 0 then 0 else c m) with hCdef
    have hCC : ∀ m, m ≤ n → PowerSeries.coeff m C
        = PowerSeries.coeff m (∑ i : Fin (n + 1), PowerSeries.monomial (i.val + 1)
            (c (i.val + 1))) := by
      intro m hm
      rw [hCdef, PowerSeries.coeff_mk, map_sum]
      simp_rw [PowerSeries.coeff_monomial]
      rw [Fin.sum_univ_eq_sum_range (fun j => if m = j + 1 then c (j + 1) else 0) (n + 1)]
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; simp
      · rw [Finset.sum_eq_single (m - 1)]
        · have h1 : m - 1 + 1 = m := by omega
          rw [h1]; simp [show ¬ m = 0 by omega]
        · intro j _ hjne; rw [ite_eq_right (by omega)]
        · intro hnm; exact absurd (Finset.mem_range.mpr (by omega)) hnm
    rw [PowerSeries.coeff_pow, PowerSeries.coeff_pow]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mem_finsuppAntidiag] at hl
    apply Finset.prod_congr rfl
    intro i hi
    exact hCC (l i) (by rw [← hl.1]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)
  have hB : PowerSeries.coeff n ((∑ i : Fin (n + 1), PowerSeries.monomial (i.val + 1)
      (c (i.val + 1))) ^ k)
      = ∑ κ ∈ (Finset.univ : Finset (Fin (n + 1))).piAntidiag k,
          (↑(Nat.multinomial Finset.univ κ) : Rat)
            * (if n = ∑ i, (κ i) * (i.val + 1) then ∏ i, c (i.val + 1) ^ (κ i) else 0) := by
    rw [Finset.sum_pow_eq_sum_piAntidiag, map_sum]
    apply Finset.sum_congr rfl
    intro κ _
    have hp : ∏ i, (PowerSeries.monomial (i.val + 1) (c (i.val + 1)) : PowerSeries Rat) ^ (κ i)
        = PowerSeries.monomial (∑ i, (κ i) * (i.val + 1)) (∏ i, c (i.val + 1) ^ (κ i)) := by
      simp_rw [PowerSeries.monomial_pow]; rw [howard_prod_monomial]
    rw [hp, ← nsmul_eq_mul, map_nsmul, PowerSeries.coeff_monomial, nsmul_eq_mul]
  rw [hA, hB]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, howard_bell_index_set n k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro κ hκ
  rw [Finset.mem_filter, Fintype.mem_piFinset] at hκ
  have hsum : ∑ i, κ i = k := hκ.2.1
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin (n + 1))) κ
  rw [hsum] at hspec
  have hprodne : (∏ i, ((κ i).factorial : Rat)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _; exact_mod_cast (κ i).factorial_ne_zero
  have hspecR : (∏ i, ((κ i).factorial : Rat)) * (Nat.multinomial Finset.univ κ : Rat) =
      (k.factorial : Rat) := by
    exact_mod_cast hspec
  rw [Finset.prod_div_distrib]
  have hmul : (↑(Nat.multinomial Finset.univ κ) : Rat) = ↑k.factorial /
      (∏ i, ((κ i).factorial : Rat)) := by
    rw [eq_div_iff hprodne, mul_comm]; exact hspecR
  rw [hmul]; ring

private theorem howard_partialBell_coeff_dvd {n : ℕ} (m : Fin (n + 1) → ℕ)
    (hm : ∑ i, (i.val + 1) * m i = n) :
    ∏ i, (m i).factorial * (i.val + 1).factorial ^ m i ∣ n.factorial := by
  calc ∏ i, (m i).factorial * (i.val + 1).factorial ^ m i
      ∣ ∏ i, ((i.val + 1) * m i).factorial := Finset.prod_dvd_prod_of_dvd _ _ fun i _ =>
        Dvd.intro_left (Nat.uniformBell (m i) (i.val + 1)) (by
          rw [mul_comm (i.val + 1), ← Nat.uniformBell_mul_eq (m i) (Nat.succ_ne_zero i.val)]
          ring)
    _ ∣ (∑ i, (i.val + 1) * m i).factorial := Nat.prod_factorial_dvd_factorial_sum _ _
    _ = n.factorial := by rw [hm]

private theorem howard_bell_summand_eq_partialBellPolynomial (c : ℕ → Rat) (n k : ℕ) :
    (k.factorial : Rat) *
      ∑ j ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range (n + 1))).filter
        (fun j => (∑ i, j i = k) ∧ (∑ i, (i.val + 1) * j i = n)),
      ∏ i, ((c (i.val + 1)) ^ (j i) / (((j i).factorial : ℕ) : Rat))
    = (k.factorial : Rat) / n.factorial *
      partialBellPolynomial n k (fun m => (m.factorial : Rat) * c m) := by
  rw [partialBellPolynomial, div_mul_eq_mul_div, mul_div_assoc, Finset.sum_div]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun _ _ => and_comm) fun j hj => ?_
  have hdvd := howard_partialBell_coeff_dvd j (Finset.mem_filter.mp hj).2.1
  have hP : ((∏ i, (j i).factorial * (i.val + 1).factorial ^ j i : ℕ) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_of_dvd_of_pos hdvd n.factorial_pos).ne'
  have hn : (n.factorial : Rat) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [Nat.cast_div hdvd hP]
  push_cast at hP ⊢
  rw [Finset.prod_mul_distrib] at hP ⊢
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_div_distrib]
  obtain ⟨hB, hP'⟩ := mul_ne_zero_iff.mp hP
  field_simp

private noncomputable def howardBellC : ℕ → Rat :=
  fun m => if m = 1 then 0 else ((m.factorial : Rat)⁻¹)

private theorem howardBellC_mul (m : ℕ) (hm : 1 ≤ m) :
    (m.factorial : Rat) * howardBellC m = if 2 ≤ m then 1 else 0 := by
  have hdef : howardBellC m = (if m = 1 then (0 : Rat) else ((m.factorial : Rat)⁻¹)) := rfl
  rw [hdef]
  by_cases h1 : m = 1
  · subst h1
    norm_num
  · have h2 : 2 ≤ m := by omega
    rw [ite_eq_right h1, ite_eq_left h2]
    have hm_ne : ((m.factorial : ℕ) : Rat) ≠ 0 :=
      Nat.cast_ne_zero.mpr m.factorial_ne_zero
    exact mul_inv_cancel₀ hm_ne

private noncomputable def howardCSeries : PowerSeries Rat :=
  PowerSeries.mk (fun m => if m = 0 then 0 else howardBellC m)

private theorem howardCSeries_eq :
    howardCSeries
      = PowerSeries.X ^ 2 * (PowerSeries.C (1 / 2 : Rat) * howardG) := by
  apply PowerSeries.ext
  intro m
  have hL : PowerSeries.coeff m howardCSeries
      = (if m = 0 then (0 : Rat) else howardBellC m) := by
    rw [howardCSeries, PowerSeries.coeff_mk]
  rw [hL, PowerSeries.coeff_X_pow_mul']
  by_cases h2 : 2 ≤ m
  · rw [ite_eq_left h2, PowerSeries.coeff_C_mul, howardG_coeff]
    have hm0 : m ≠ 0 := by omega
    have hm1 : m ≠ 1 := by omega
    rw [ite_eq_right hm0]
    have hC : howardBellC m = ((m.factorial : Rat)⁻¹) := by
      have hdef : howardBellC m
          = (if m = 1 then (0 : Rat) else ((m.factorial : Rat)⁻¹)) := rfl
      rw [hdef, ite_eq_right hm1]
    rw [hC]
    have hsub : m - 2 + 2 = m := Nat.sub_add_cancel h2
    rw [hsub]
    have hm_ne : ((m.factorial : ℕ) : Rat) ≠ 0 :=
      Nat.cast_ne_zero.mpr m.factorial_ne_zero
    field_simp
  · rw [ite_eq_right h2]
    have h01 : m = 0 ∨ m = 1 := by omega
    rcases h01 with rfl | rfl
    · rw [ite_eq_left rfl]
    · rw [ite_eq_right (by norm_num : (1 : ℕ) ≠ 0)]
      have hC1 : howardBellC 1 = 0 := rfl
      rw [hC1]

private theorem howardCSeries_pow_coeff (n j : ℕ) :
    PowerSeries.coeff (n + 2 * j) (howardCSeries ^ j)
      = ((1 / 2 : Rat) ^ j) * PowerSeries.coeff n (howardG ^ j) := by
  have hpow : howardCSeries ^ j
      = PowerSeries.X ^ (2 * j)
        * (PowerSeries.C ((1 / 2 : Rat) ^ j) * howardG ^ j) := by
    rw [howardCSeries_eq, mul_pow]
    have hX : ((PowerSeries.X : PowerSeries Rat) ^ 2) ^ j
        = (PowerSeries.X : PowerSeries Rat) ^ (2 * j) := by
      rw [← pow_mul]
    have hH : (PowerSeries.C (1 / 2 : Rat) * howardG) ^ j
        = PowerSeries.C ((1 / 2 : Rat) ^ j) * howardG ^ j := by
      rw [mul_pow, ← map_pow]
    rw [hX, hH]
  rw [hpow]
  have hadd : n + 2 * j = n + (2 * j) := rfl
  rw [hadd, PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_C_mul]

private theorem howard_Bell_eq_indicator (N k : ℕ) :
    partialBellPolynomial N k (fun m => (m.factorial : Rat) * howardBellC m)
      = partialBellPolynomial N k (fun j => if 2 ≤ j then (1 : Rat) else 0) := by
  unfold partialBellPolynomial
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have h := howardBellC_mul (i.val + 1) (Nat.succ_pos _)
  exact congrArg (fun x => x ^ m i) h

private theorem howard_Bell_eq_coeff (n j : ℕ) :
    partialBellPolynomial (n + 2 * j) j (fun j => if 2 ≤ j then (1 : Rat) else 0)
      = ((((n + 2 * j).factorial : Rat) / (j.factorial : Rat))
        * (((1 / 2 : Rat) ^ j) * PowerSeries.coeff n (howardG ^ j))) := by
  set N := n + 2 * j with hNdef
  have hCeq : (PowerSeries.mk (fun m => if m = 0 then (0 : Rat) else howardBellC m)
      : PowerSeries Rat) = howardCSeries := rfl
  have h1 := howard_bell_coeff_pow howardBellC N j
  rw [hCeq] at h1
  have h2 := howard_bell_summand_eq_partialBellPolynomial howardBellC N j
  have h3 := howard_Bell_eq_indicator N j
  have h4 := howardCSeries_pow_coeff n j
  have hN : N = n + 2 * j := rfl
  rw [hN] at h1 h2 h3
  have hj_ne : ((j.factorial : ℕ) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hN_ne : ((N.factorial : ℕ) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr N.factorial_ne_zero
  have heq : ((j.factorial : Rat) / (N.factorial : Rat))
      * partialBellPolynomial N j (fun j => if 2 ≤ j then (1 : Rat) else 0)
      = ((1 / 2 : Rat) ^ j) * PowerSeries.coeff n (howardG ^ j) := by
    calc ((j.factorial : Rat) / (N.factorial : Rat))
          * partialBellPolynomial N j (fun j => if 2 ≤ j then (1 : Rat) else 0)
        = ((j.factorial : Rat) / (N.factorial : Rat))
          * partialBellPolynomial N j (fun m => (m.factorial : Rat) * howardBellC m) := by
          rw [← h3]
      _ = PowerSeries.coeff N (howardCSeries ^ j) := by rw [← h2, ← h1]
      _ = ((1 / 2 : Rat) ^ j) * PowerSeries.coeff n (howardG ^ j) := by
          rw [hNdef]
          exact h4
  have hB : partialBellPolynomial N j (fun j => if 2 ≤ j then (1 : Rat) else 0)
      = ((((N.factorial : Rat) / (j.factorial : Rat)))
        * ((((1 / 2 : Rat) ^ j) * PowerSeries.coeff n (howardG ^ j)))) := by
    rw [← heq]
    field_simp
  rw [hNdef] at hB ⊢
  exact hB

private theorem howard_two_pow_mul_half_pow (j : ℕ) :
    ((2 : Rat) ^ j) * ((1 / 2 : Rat) ^ j) = 1 := by
  rw [← mul_pow]
  have h21 : (2 : Rat) * (1 / 2) = 1 := by norm_num
  rw [h21, one_pow]

private theorem howardR_neg_eq_coeff (n j : ℕ) (hj : j ≤ n) :
    (howardR n).eval (-(j : Rat))
      = (n.factorial : Rat) * PowerSeries.coeff n (howardG ^ j) := by
  rw [howardR_eval_neg_eq_summand n j hj, howardRsummand_self n j hj,
    howard_Bell_eq_coeff n j]
  have hj_ne : ((j.factorial : ℕ) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hN_ne : ((((n + 2 * j).factorial : ℕ)) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (n + 2 * j).factorial_ne_zero
  have h2 := howard_two_pow_mul_half_pow j
  have hJ : ((j.factorial : Rat) * ((j.factorial : Rat)⁻¹)) = 1 :=
    mul_inv_cancel₀ hj_ne
  have hNinv : (((n + 2 * j).factorial : Rat)⁻¹ * ((n + 2 * j).factorial : Rat)) = 1 :=
    inv_mul_cancel₀ hN_ne
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc (((2 : Rat) ^ j * (n.factorial : Rat) * (j.factorial : Rat)
          * (((n + 2 * j).factorial : Rat)⁻¹))
        * ((((n + 2 * j).factorial : Rat) * ((j.factorial : Rat)⁻¹))
          * (((1 / 2 : Rat) ^ j) * PowerSeries.coeff n (howardG ^ j))))
      = ((n.factorial : Rat) * PowerSeries.coeff n (howardG ^ j))
        * ((((2 : Rat) ^ j * ((1 / 2 : Rat) ^ j))
          * (((j.factorial : Rat) * ((j.factorial : Rat)⁻¹))))
          * ((((n + 2 * j).factorial : Rat)⁻¹
            * ((n + 2 * j).factorial : Rat)))) := by ring
    _ = ((n.factorial : Rat) * PowerSeries.coeff n (howardG ^ j))
        * (((1 * 1)) * 1) := by
        rw [h2, hJ, hNinv]
    _ = (n.factorial : Rat) * PowerSeries.coeff n (howardG ^ j) := by ring

private noncomputable def howardH (n : ℕ) : ℕ → Rat :=
  fun k => PowerSeries.coeff n ((howardG⁻¹ ^ n) * (howardG ^ k))

private theorem howard_fwdDiff_iter (n k y : ℕ) :
    (fwdDiff (1 : ℕ))^[k] (howardH n) y
      = PowerSeries.coeff n
        ((howardG⁻¹ ^ n) * (howardG ^ y) * ((howardG - 1) ^ k)) := by
  induction k generalizing y with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    rw [howardH]
    simp only [pow_zero, mul_one]
  | succ k ih =>
    have hiter : (fwdDiff (1 : ℕ))^[k + 1] (howardH n) y
        = (fwdDiff (1 : ℕ) ((fwdDiff (1 : ℕ))^[k] (howardH n))) y := by
      rw [show k + 1 = k.succ from rfl, Function.iterate_succ_apply']
    rw [hiter]
    have hfd : (fwdDiff (1 : ℕ) ((fwdDiff (1 : ℕ))^[k] (howardH n))) y
        = (fwdDiff (1 : ℕ))^[k] (howardH n) (y + 1)
          - (fwdDiff (1 : ℕ))^[k] (howardH n) y := rfl
    rw [hfd, ih (y + 1), ih y, ← map_sub]
    have hpow_y : howardG ^ (y + 1) = howardG ^ y * howardG := pow_succ _ _
    have hpow_k : (howardG - 1) ^ (k + 1) = (howardG - 1) ^ k * (howardG - 1) :=
      pow_succ _ _
    have hring : ((howardG⁻¹ ^ n) * (howardG ^ (y + 1)) * ((howardG - 1) ^ k)
          - (howardG⁻¹ ^ n) * (howardG ^ y) * ((howardG - 1) ^ k))
          = (howardG⁻¹ ^ n) * (howardG ^ y) * ((howardG - 1) ^ (k + 1)) := by
      rw [hpow_y, hpow_k]
      ring
    rw [hring]

private theorem howard_fwdDiff_eq_zero_of_lt (n k y : ℕ) (hk : n < k) :
    (fwdDiff (1 : ℕ))^[k] (howardH n) y = 0 := by
  rw [howard_fwdDiff_iter]
  have hdvd : (PowerSeries.X ^ k)
      ∣ ((howardG⁻¹ ^ n) * (howardG ^ y) * ((howardG - 1) ^ k)) :=
    (howard_sub_one_pow_X_dvd k).mul_left _
  exact PowerSeries.X_pow_dvd_iff.mp hdvd n hk

private noncomputable def howardP (n : ℕ) : Polynomial Rat :=
  Finset.sum (Finset.range (n + 1)) (fun k =>
    Polynomial.C ((fwdDiff (1 : ℕ))^[k] (howardH n) 0 / (k.factorial : Rat))
      * (descPochhammer Rat k))

private theorem howardP_summand_natDegree_le (n k : ℕ) (hk : k ≤ n) :
    (Polynomial.C ((fwdDiff (1 : ℕ))^[k] (howardH n) 0 / (k.factorial : Rat))
      * (descPochhammer Rat k)).natDegree ≤ n := by
  calc (Polynomial.C ((fwdDiff (1 : ℕ))^[k] (howardH n) 0 / (k.factorial : Rat))
        * (descPochhammer Rat k)).natDegree
      ≤ (descPochhammer Rat k).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ = k := descPochhammer_natDegree _ _
    _ ≤ n := hk

private theorem howardP_natDegree_le (n : ℕ) : (howardP n).natDegree ≤ n := by
  rw [howardP]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  rw [Finset.mem_range] at hk
  exact howardP_summand_natDegree_le n k (Nat.lt_succ_iff.mp hk)

private theorem howardP_eval_eq_sum_mul_choose (n m : ℕ) :
    (howardP n).eval ((m : ℕ) : Rat)
      = ∑ k ∈ Finset.range (n + 1),
        ((m.choose k : ℕ) : Rat) * ((fwdDiff (1 : ℕ))^[k] (howardH n) 0) := by
  rw [howardP, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial]
  have hdesc : (((m.descFactorial k : ℕ)) : Rat)
      = ((k.factorial : Rat) * ((m.choose k : ℕ) : Rat)) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  rw [hdesc]
  have hk_ne : ((k.factorial : ℕ) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hcancel : (((k.factorial : Rat)⁻¹ * (k.factorial : Rat))) = 1 :=
    inv_mul_cancel₀ hk_ne
  have hterm : (((fwdDiff (1 : ℕ))^[k] (howardH n) 0 / (k.factorial : Rat))
      * ((k.factorial : Rat) * ((m.choose k : ℕ) : Rat)))
      = (((m.choose k : ℕ) : Rat) * ((fwdDiff (1 : ℕ))^[k] (howardH n) 0)) := by
    rw [div_eq_mul_inv]
    calc (((fwdDiff (1 : ℕ))^[k] (howardH n) 0 * ((k.factorial : Rat)⁻¹))
          * ((k.factorial : Rat) * ((m.choose k : ℕ) : Rat)))
        = ((((m.choose k : ℕ) : Rat) * ((fwdDiff (1 : ℕ))^[k] (howardH n) 0)))
          * (((k.factorial : Rat)⁻¹ * (k.factorial : Rat))) := by ring
      _ = ((((m.choose k : ℕ) : Rat) * ((fwdDiff (1 : ℕ))^[k] (howardH n) 0))) * 1 := by
          rw [hcancel]
      _ = (((m.choose k : ℕ) : Rat) * ((fwdDiff (1 : ℕ))^[k] (howardH n) 0)) := by
          rw [mul_one]
  exact hterm

private theorem howardH_Gregory (n m : ℕ) :
    howardH n m
      = ∑ k ∈ Finset.range (m + 1),
        ((m.choose k : ℕ) : Rat) * ((fwdDiff (1 : ℕ))^[k] (howardH n) 0) := by
  have hGN := shift_eq_sum_fwdDiff_iter (M := ℕ) (G := Rat) (h := (1 : ℕ)) (howardH n) m 0
  have h0m : (0 : ℕ) + m • (1 : ℕ) = m := by simp
  rw [h0m] at hGN
  rw [hGN]
  apply Finset.sum_congr rfl
  intro k _
  rw [nsmul_eq_mul]

private theorem howardP_eval (n m : ℕ) :
    (howardP n).eval ((m : ℕ) : Rat) = howardH n m := by
  have hP := howardP_eval_eq_sum_mul_choose n m
  have hH := howardH_Gregory n m
  set T := n + m + 1 with hTdef
  have hsub_n : Finset.range (n + 1) ⊆ Finset.range T := by
    rw [hTdef]
    exact Finset.range_subset_range.mpr (by omega)
  have hsub_m : Finset.range (m + 1) ⊆ Finset.range T := by
    rw [hTdef]
    exact Finset.range_subset_range.mpr (by omega)
  have h_eq_n : (∑ k ∈ Finset.range (n + 1),
        ((m.choose k : ℕ) : Rat) * ((fwdDiff (1 : ℕ))^[k] (howardH n) 0))
      = ∑ k ∈ Finset.range T,
        ((m.choose k : ℕ) : Rat) * ((fwdDiff (1 : ℕ))^[k] (howardH n) 0) := by
    apply Finset.sum_subset hsub_n
    intro k hkT hkn
    have hmem : ¬ k < n + 1 := fun hlt => hkn (Finset.mem_range.mpr hlt)
    have hnk : n < k := by omega
    have hΔ : (fwdDiff (1 : ℕ))^[k] (howardH n) 0 = 0 :=
      howard_fwdDiff_eq_zero_of_lt n k 0 hnk
    rw [hΔ, mul_zero]
  have h_eq_m : (∑ k ∈ Finset.range (m + 1),
        ((m.choose k : ℕ) : Rat) * ((fwdDiff (1 : ℕ))^[k] (howardH n) 0))
      = ∑ k ∈ Finset.range T,
        ((m.choose k : ℕ) : Rat) * ((fwdDiff (1 : ℕ))^[k] (howardH n) 0) := by
    apply Finset.sum_subset hsub_m
    intro k hkT hkm
    have hmem : ¬ k < m + 1 := fun hlt => hkm (Finset.mem_range.mpr hlt)
    have hmk : m < k := by omega
    have hch : m.choose k = 0 := Nat.choose_eq_zero_of_lt hmk
    have hchR : (((m.choose k : ℕ)) : Rat) = 0 := by rw [hch, Nat.cast_zero]
    rw [hchR, zero_mul]
  calc (howardP n).eval ((m : ℕ) : Rat)
      = ∑ k ∈ Finset.range (n + 1),
        ((m.choose k : ℕ) : Rat) * ((fwdDiff (1 : ℕ))^[k] (howardH n) 0) := hP
    _ = ∑ k ∈ Finset.range T,
        ((m.choose k : ℕ) : Rat) * ((fwdDiff (1 : ℕ))^[k] (howardH n) 0) := h_eq_n
    _ = ∑ k ∈ Finset.range (m + 1),
        ((m.choose k : ℕ) : Rat) * ((fwdDiff (1 : ℕ))^[k] (howardH n) 0) := h_eq_m.symm
    _ = howardH n m := hH.symm

private noncomputable def howardQ (n : ℕ) : Polynomial Rat :=
  Polynomial.C (n.factorial : Rat)
    * ((howardP n).comp (Polynomial.C (n : Rat) - Polynomial.X))

private theorem howard_inner_natDegree (n : ℕ) :
    (Polynomial.C (n : Rat) - Polynomial.X).natDegree = 1 := by
  have heq : (Polynomial.C (n : Rat) - Polynomial.X)
      = -(Polynomial.X - Polynomial.C (n : Rat)) := by ring
  rw [heq, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]

private theorem howardQ_natDegree_le (n : ℕ) : (howardQ n).natDegree ≤ n := by
  have hInner_le : (Polynomial.C (n : Rat) - Polynomial.X).natDegree ≤ 1 :=
    le_of_eq (howard_inner_natDegree n)
  have hcomp : ((howardP n).comp
      (Polynomial.C (n : Rat) - Polynomial.X)).natDegree ≤ n := by
    calc ((howardP n).comp (Polynomial.C (n : Rat) - Polynomial.X)).natDegree
        ≤ (howardP n).natDegree * (Polynomial.C (n : Rat) - Polynomial.X).natDegree :=
          Polynomial.natDegree_comp_le
      _ ≤ n * 1 := Nat.mul_le_mul (howardP_natDegree_le n) hInner_le
      _ = n := mul_one n
  exact le_trans (Polynomial.natDegree_C_mul_le _ _) hcomp

private theorem howardQ_eval_nat (n m : ℕ) (hm : m ≤ n) :
    (howardQ n).eval ((m : ℕ) : Rat)
      = (n.factorial : Rat) * howardH n (n - m) := by
  rw [howardQ, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
  have hcast : ((n : Rat) - ((m : ℕ) : Rat)) = ((((n - m : ℕ))) : Rat) :=
    (Nat.cast_sub hm).symm
  rw [hcast, howardP_eval]

private theorem howardQ_eval_neg (n j : ℕ) :
    (howardQ n).eval (-(j : Rat))
      = (n.factorial : Rat) * howardH n (n + j) := by
  rw [howardQ, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
  have hcast : ((n : Rat) - (-(j : Rat))) = ((((n + j : ℕ))) : Rat) := by
    push_cast
    ring
  rw [hcast, howardP_eval]

private theorem howardH_sub (n m : ℕ) (hm : m ≤ n) :
    howardH n (n - m) = PowerSeries.coeff n ((howardG⁻¹ ^ m)) := by
  have hseries : ((howardG⁻¹ ^ n) * (howardG ^ (n - m)) : PowerSeries Rat)
      = (howardG⁻¹ ^ m) := by
    have hN : n = m + (n - m) := (Nat.add_sub_cancel' hm).symm
    have hpow : (howardG⁻¹ ^ n : PowerSeries Rat)
        = (howardG⁻¹ ^ (m + (n - m))) := by conv_lhs => rw [hN]
    rw [hpow, pow_add, mul_assoc, howard_inv_pow_mul_pow, mul_one]
  have hH : howardH n (n - m)
      = PowerSeries.coeff n ((howardG⁻¹ ^ n) * (howardG ^ (n - m))) := rfl
  rw [hH, hseries]

private theorem howardH_add (n j : ℕ) :
    howardH n (n + j) = PowerSeries.coeff n (howardG ^ j) := by
  have hseries : ((howardG⁻¹ ^ n) * (howardG ^ (n + j)) : PowerSeries Rat)
      = (howardG ^ j) := by
    rw [pow_add, ← mul_assoc, howard_inv_pow_mul_pow, one_mul]
  have hH : howardH n (n + j)
      = PowerSeries.coeff n ((howardG⁻¹ ^ n) * (howardG ^ (n + j))) := rfl
  rw [hH, hseries]

private theorem howard_eq_of_deg_le_of_eval_neg_eq (n : ℕ) (P Q : Polynomial Rat)
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n)
    (heq : ∀ j : ℕ, j ≤ n → Q.eval (-(j : Rat)) = P.eval (-(j : Rat))) :
    P = Q := by
  have hsub_deg : (P - Q).natDegree ≤ n :=
    le_trans (Polynomial.natDegree_sub_le _ _) (max_le hP hQ)
  have hroots : ∀ i : Fin (n + 1), (P - Q).eval (-(((i.val : ℕ)) : Rat)) = 0 := by
    intro i
    rw [Polynomial.eval_sub, heq i.val (Nat.lt_succ_iff.mp i.isLt), sub_self]
  have hinj : Function.Injective (fun i : Fin (n + 1) => (-(((i.val : ℕ)) : Rat))) := by
    intro a b hab
    simp only at hab
    have hcast : (((a.val : ℕ)) : Rat) = (((b.val : ℕ)) : Rat) := neg_inj.mp hab
    have hnat : (a.val : ℕ) = (b.val : ℕ) := by exact_mod_cast hcast
    exact Fin.ext hnat
  have hlt : (P - Q).natDegree < Fintype.card (Fin (n + 1)) := by
    rw [Fintype.card_fin]
    exact Nat.lt_succ_of_le hsub_deg
  have hzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (P - Q) hinj hroots hlt
  exact sub_eq_zero.mp hzero

private theorem howardG_mk_eq :
    howardG = PowerSeries.mk (fun k => (2 : Rat) / (((k + 2).factorial : Rat))) := rfl

private theorem howardG_inv_bridge :
    (PowerSeries.inv howardG : PowerSeries Rat) = howardG⁻¹ := rfl

end

end MetaMathlibExt

namespace MetaMathlibExt

section

/-- **Howard's formula for the series $\sum_{k \ge 0} 2x^k/(k+2)!$.** Let $n$ be a natural
number, let
$$h(x) = \sum_{k \ge 0} \frac{2}{(k+2)!}\, x^k \in \mathbb{Q}[[x]],$$
let $h^{-1}$ be its inverse in $\mathbb{Q}[[x]]$, and write $[x^n]\, f$ for the coefficient of
$x^n$ in a power series $f$. Let $G_n \in \mathbb{Q}[X]$ be a polynomial of degree at most $n$
such that $G_n(m) = n!\, [x^n]\, (h^{-1})^m$ for every natural number $m \le n$. Then
$$G_n(X) = \sum_{i=0}^{n} (-1)^i\, 2^i\, \frac{n!\, i!}{(n+2i)!} \cdot
\frac{X(X+1)\cdots(X+i-1)}{i!} \cdot \frac{(X+n)(X+n-1)\cdots(X+i+1)}{(n-i)!} \cdot
B_{n+2i,\,i}(0, 1, 1, \dots),$$
where empty products equal $1$ and $B_{n+2i,\,i}(0, 1, 1, \dots)$ is the partial Bell
polynomial evaluated at the sequence whose first term is $0$ and whose other terms are all $1$.

Source: G. Nemes, Journal of Integer Sequences 13 (2010).
Source URL: https://cs.uwaterloo.ca/journals/JIS/VOL13/Nemes/nemes2.tex
Generic span: lines 120-133; specialization span: lines 166-173.
File SHA256: f3556d7fdb4d3f9366c3505d2cd20564f431d71a337e9f3a4fc7c24431df2daf
Span SHA256 (generic): c3e6c35fd19388416b9e1105e7b027a70c3956f58c8d204c44e88a0936273a04
Span SHA256 (specialization): bcc9e205ea075840eda33c04ff69e3f762b50e16bdc4627ed06ac9351fd4348c
Statement IDs: jis_f8773fd39faf6ec979df6672 and jis_rank35_proof_specialization_lines_166_173
Grounded concept ID: jis_grounded_097dd40d7498e5b441a12749
Exact-rational probe: passed 75 comparisons across r=1,2,3, n=0,...,4, natural z=0,...,n+2; finite
evidence only.

Proves `Wanted` entry `howard_potentialPolynomial_rTwo_eq_partialBell`.
-/
theorem howard_potentialPolynomial_rTwo_eq_partialBell
  (G : ℕ → Polynomial Rat) (n : ℕ)
  (hdeg : (G n).natDegree ≤ n)
  (heval : ∀ m : ℕ, m ≤ n →
    (G n).eval (↑m : Rat) = (n.factorial : Rat) *
      PowerSeries.coeff n
        ((PowerSeries.inv (PowerSeries.mk (fun k => (2 : Rat) /
          (((k + 2).factorial : Rat))))) ^ m)) :
  G n = Finset.sum (Finset.range (n + 1)) (fun i =>
    Polynomial.C (((-1 : Rat) ^ i) * ((2 : Rat) ^ i) *
      (((n.factorial : Rat) * (i.factorial : Rat)) / (((n + 2 * i).factorial : Rat)))) *
    ((ascPochhammer Rat i) * Polynomial.C (((i.factorial : Rat))⁻¹)) *
    (((descPochhammer Rat (n - i)).comp (Polynomial.X + Polynomial.C (n : Rat))) *
      Polynomial.C ((((n - i).factorial : Rat))⁻¹)) *
    Polynomial.C (MetaMathlibExt.partialBellPolynomial (n + 2 * i) i
      (fun j => if 2 ≤ j then (1 : Rat) else 0))) := by
  have hRdeg : (howardR n).natDegree ≤ n := howard_rhs_natDegree_le n
  have hQdeg : (howardQ n).natDegree ≤ n := howardQ_natDegree_le n
  have hInv : (PowerSeries.inv
      (PowerSeries.mk (fun k => (2 : Rat) / (((k + 2).factorial : Rat))))
      : PowerSeries Rat) = howardG⁻¹ := by
    rw [← howardG_mk_eq]
    exact howardG_inv_bridge
  have hGQ : G n = howardQ n := by
    apply howard_eq_of_deg_le_of_eval_eq n (G n) (howardQ n) hdeg hQdeg
    intro m hm
    have hQm : (howardQ n).eval ((m : ℕ) : Rat)
        = (n.factorial : Rat) * PowerSeries.coeff n (howardG⁻¹ ^ m) := by
      rw [howardQ_eval_nat n m hm, howardH_sub n m hm]
    have hPow : (howardG⁻¹ ^ m : PowerSeries Rat)
        = ((PowerSeries.inv
          (PowerSeries.mk (fun k => (2 : Rat) / (((k + 2).factorial : Rat))))) ^ m) := by
      rw [← hInv]
    rw [hQm, hPow, ← heval m hm]
  have hRQ : howardR n = howardQ n := by
    apply howard_eq_of_deg_le_of_eval_neg_eq n (howardR n) (howardQ n) hRdeg hQdeg
    intro j hj
    have hQj : (howardQ n).eval (-(j : Rat))
        = (n.factorial : Rat) * PowerSeries.coeff n (howardG ^ j) := by
      rw [howardQ_eval_neg, howardH_add]
    have hRj : (howardR n).eval (-(j : Rat))
        = (n.factorial : Rat) * PowerSeries.coeff n (howardG ^ j) :=
      howardR_neg_eq_coeff n j hj
    rw [hQj, hRj]
  exact hGQ.trans hRQ.symm

end

/-- Denominator of a Bell summand divides `N!`: if `∑ (i+1) * m i = N` then
`∏ (m i ! * (i+1)! ^ m i) ∣ N!`. Proof by induction on the number of block
sizes, peeling off the largest size and using `Nat.uniformBell_mul_eq`. -/
private theorem bell_denom_dvd (M : ℕ) : ∀ (N : ℕ) (m : Fin M → ℕ),
    (∑ i, (i.val + 1) * m i) = N →
    (∏ i, ((m i).factorial * (i.val + 1).factorial ^ m i)) ∣ N.factorial := by
  induction M with
  | zero =>
    intro N m hsum
    have hN : N = 0 := by simpa using hsum.symm
    subst hN
    simp
  | succ M ih =>
    intro N m hsum
    have hsum2 : (∑ i : Fin M, (i.castSucc.val + 1) * m i.castSucc)
        + (M + 1) * m (Fin.last M) = N := by
      have h := hsum
      rw [Fin.sum_univ_castSucc] at h
      have hvl : (Fin.last M).val + 1 = M + 1 := by rw [Fin.val_last]
      rw [hvl] at h
      exact h
    have hcast : (∑ i : Fin M, (i.castSucc.val + 1) * m i.castSucc)
        = ∑ i : Fin M, (i.val + 1) * m i.castSucc := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.val_castSucc]
    set N' : ℕ := ∑ i : Fin M, (i.val + 1) * m i.castSucc with hN'
    set t : ℕ := m (Fin.last M) with ht
    have hsum' : N' + (M + 1) * t = N := by rw [← hcast]; exact hsum2
    obtain ⟨Q, hQ⟩ := ih N' (fun i => m i.castSucc) rfl
    set T : ℕ := t * (M + 1) with hT
    have hcomm : (M + 1) * t = t * (M + 1) := mul_comm _ _
    have hNT : N' + T = N := by rw [hT]; omega
    have hU := Nat.uniformBell_mul_eq t (show M + 1 ≠ 0 by omega)
    have hTdvd : t.factorial * (M + 1).factorial ^ t ∣ T.factorial := by
      have hTeq : t * (M + 1) = T := rfl
      rw [← hTeq, ← hU]; ring_nf; exact Dvd.intro _ rfl
    have hprod : N'.factorial * T.factorial ∣ N.factorial := by
      conv_rhs => rw [← hNT]
      have h := Nat.factorial_mul_factorial_dvd_factorial
        (show N' ≤ N' + T by omega)
      rwa [Nat.add_sub_cancel_left] at h
    have hQdvd : (∏ i : Fin M, ((m i.castSucc).factorial
        * (i.val + 1).factorial ^ m i.castSucc)) ∣ N'.factorial := ⟨Q, hQ⟩
    have hmul := Nat.mul_dvd_mul hQdvd hTdvd
    have hgoal : (∏ i : Fin (M + 1),
        ((m i).factorial * (i.val + 1).factorial ^ m i))
        = (∏ i : Fin M, (((fun i => m i.castSucc) i).factorial
          * (i.val + 1).factorial ^ (fun i => m i.castSucc) i))
        * (t.factorial * (M + 1).factorial ^ t) := by
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc]
      rw [ht]
      have hvl : (Fin.last M).val + 1 = M + 1 := by rw [Fin.val_last]
      rw [hvl]
    rw [hgoal]
    calc (∏ i : Fin M, (((fun i => m i.castSucc) i).factorial
            * (i.val + 1).factorial ^ (fun i => m i.castSucc) i))
          * (t.factorial * (M + 1).factorial ^ t)
        ∣ N'.factorial * T.factorial := hmul
      _ ∣ N.factorial := hprod

private theorem prod_monomial {K : Type*} [CommSemiring K] (s : Finset ℕ) (a : ℕ → ℕ)
    (b : ℕ → K) :
    (∏ i ∈ s, PowerSeries.monomial (a i) (b i))
    = PowerSeries.monomial (∑ i ∈ s, a i) (∏ i ∈ s, b i) := by
  refine Finset.induction ?_ ?_ s
  · simp
  · intro x t hxt ih
    rw [Finset.prod_insert hxt, Finset.sum_insert hxt, Finset.prod_insert hxt, ih,
      PowerSeries.monomial_mul_monomial]
private theorem coeff_trunc_eq {K : Type*} [Field K] (N k : ℕ) (c : ℕ → K) :
    PowerSeries.coeff N ((PowerSeries.mk (fun m => if m = 0 then 0 else c m)) ^ k)
    = PowerSeries.coeff N
      ((∑ i ∈ Finset.range (N + 1),
        PowerSeries.monomial i (if i = 0 then 0 else c i)) ^ k) := by
  set d : ℕ → K := fun i => if i = 0 then 0 else c i with hd
  set S : PowerSeries K := PowerSeries.mk d with hS
  set T : PowerSeries K :=
    ∑ i ∈ Finset.range (N + 1), PowerSeries.monomial i (d i) with hT
  set R : PowerSeries K := S - T with hRdef
  have hST : T + R = S := by rw [hRdef]; abel
  have hTcoeff : ∀ m : ℕ, m < N + 1 →
      PowerSeries.coeff m T = d m := by
    intro m hm
    rw [hT, map_sum]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b hb hbm
      have hne : m ≠ b := Ne.symm hbm
      simp [PowerSeries.coeff_monomial, hne]
    · intro h
      exact absurd (Finset.mem_range.mpr hm) h
  have hR : PowerSeries.X ^ (N + 1) ∣ R := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    have h1 : PowerSeries.coeff m S = d m := by
      rw [hS]; exact PowerSeries.coeff_mk _ _
    have h2 : PowerSeries.coeff m T = d m := hTcoeff m hm
    have hsub : PowerSeries.coeff m R =
        PowerSeries.coeff m S - PowerSeries.coeff m T := Pi.sub_apply _ _ _
    rw [hsub, h1, h2, sub_self]
  have hterm0 : ∀ m ∈ Finset.range (k + 1), m ≠ k →
      PowerSeries.coeff N
        (T ^ m * R ^ (k - m) * ((k.choose m : ℕ) : PowerSeries K)) = 0 := by
    intro m hm hmk
    have hmlt : m < k + 1 := Finset.mem_range.mp hm
    have hkm : k - m ≠ 0 := by omega
    have hdvd : PowerSeries.X ^ (N + 1) ∣
        T ^ m * R ^ (k - m) * ((k.choose m : ℕ) : PowerSeries K) :=
      dvd_trans hR (dvd_trans
        (dvd_trans (dvd_pow_self R hkm) (dvd_mul_left _ _)) (dvd_mul_right _ _))
    obtain ⟨H, hH⟩ := hdvd
    rw [hH, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)]
  have hkterm : T ^ k * R ^ (k - k) * ((k.choose k : ℕ) : PowerSeries K)
      = T ^ k := by
    rw [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, mul_one]
  have h2 : k ∉ Finset.range (k + 1) →
      PowerSeries.coeff N
        (T ^ k * R ^ (k - k) * ((k.choose k : ℕ) : PowerSeries K)) = 0 := by
    intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) h
  have hbase : S ^ k = ∑ m ∈ Finset.range (k + 1),
      T ^ m * R ^ (k - m) * ((k.choose m : ℕ) : PowerSeries K) := by
    conv_lhs => rw [← hST]
    exact add_pow T R k
  rw [hbase, map_sum, Finset.sum_eq_single k hterm0 h2, hkterm]
private theorem coeff_trunc_expand {K : Type*} [Field K] (N k : ℕ) (c : ℕ → K) :
    PowerSeries.coeff N ((∑ i ∈ Finset.range (N + 1),
      PowerSeries.monomial i (if i = 0 then 0 else c i)) ^ k)
    = ∑ e ∈ (Finset.range (N + 1)).piAntidiag k,
      ((Nat.multinomial (Finset.range (N + 1)) e : ℕ) : K)
      * (if N = ∑ i ∈ Finset.range (N + 1), e i * i
        then ∏ i ∈ Finset.range (N + 1), (if i = 0 then 0 else c i) ^ e i
        else 0) := by
  have hterm : ∀ e : ℕ → ℕ, PowerSeries.coeff N
      (((((Nat.multinomial (Finset.range (N + 1)) e : ℕ))) : PowerSeries K)
        * ∏ i ∈ Finset.range (N + 1),
          (PowerSeries.monomial i (if i = 0 then 0 else c i)) ^ e i)
      = ((Nat.multinomial (Finset.range (N + 1)) e : ℕ) : K)
        * (if N = ∑ i ∈ Finset.range (N + 1), e i * i
          then ∏ i ∈ Finset.range (N + 1), (if i = 0 then 0 else c i) ^ e i
          else 0) := by
    intro e
    have hC : ((((Nat.multinomial (Finset.range (N + 1)) e : ℕ))) : PowerSeries K)
        = PowerSeries.C (((Nat.multinomial (Finset.range (N + 1)) e : ℕ)) : K) := by
      simp
    rw [hC, PowerSeries.coeff_C_mul]
    have hprod : (∏ i ∈ Finset.range (N + 1),
          (PowerSeries.monomial i (if i = 0 then 0 else c i)) ^ e i)
        = PowerSeries.monomial (∑ i ∈ Finset.range (N + 1), e i * i)
          (∏ i ∈ Finset.range (N + 1), (if i = 0 then 0 else c i) ^ e i) := by
      rw [← prod_monomial]
      apply Finset.prod_congr rfl
      intro i _
      rw [PowerSeries.monomial_pow]
    rw [hprod, PowerSeries.coeff_monomial]
  rw [Finset.sum_pow_eq_sum_piAntidiag, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact hterm e
private theorem piAntidiag_filter_sum {K : Type*} [Field K] (N k : ℕ) (c : ℕ → K) :
    (∑ e ∈ (Finset.range (N + 1)).piAntidiag k,
      ((Nat.multinomial (Finset.range (N + 1)) e : ℕ) : K)
      * (if N = ∑ i ∈ Finset.range (N + 1), e i * i
        then ∏ i ∈ Finset.range (N + 1), (if i = 0 then 0 else c i) ^ e i
        else 0))
    = ∑ e ∈ ((Finset.range (N + 1)).piAntidiag k).filter
        (fun e => e 0 = 0 ∧ ∑ i ∈ Finset.range (N + 1), e i * i = N),
      ((Nat.multinomial (Finset.range (N + 1)) e : ℕ) : K)
      * (∏ i ∈ Finset.range (N + 1), (if i = 0 then 0 else c i) ^ e i) := by
  have hcongr : (∑ e ∈ ((Finset.range (N + 1)).piAntidiag k).filter
        (fun e => e 0 = 0 ∧ ∑ i ∈ Finset.range (N + 1), e i * i = N),
      ((Nat.multinomial (Finset.range (N + 1)) e : ℕ) : K)
      * (∏ i ∈ Finset.range (N + 1), (if i = 0 then 0 else c i) ^ e i))
    = ∑ e ∈ ((Finset.range (N + 1)).piAntidiag k).filter
        (fun e => e 0 = 0 ∧ ∑ i ∈ Finset.range (N + 1), e i * i = N),
      ((Nat.multinomial (Finset.range (N + 1)) e : ℕ) : K)
      * (if N = ∑ i ∈ Finset.range (N + 1), e i * i
        then ∏ i ∈ Finset.range (N + 1), (if i = 0 then 0 else c i) ^ e i
        else 0) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_filter] at he
    rw [ite_eq_left he.2.2.symm]
  rw [hcongr]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hne
  have hcon : ¬ (e 0 = 0 ∧ ∑ i ∈ Finset.range (N + 1), e i * i = N) := by
    intro h
    exact hne (Finset.mem_filter.mpr ⟨he, h⟩)
  by_cases he0 : e 0 = 0
  · have hcond : ¬ (N = ∑ i ∈ Finset.range (N + 1), e i * i) := by
      intro h
      exact hcon ⟨he0, h.symm⟩
    rw [ite_eq_right hcond, mul_zero]
  · have hP : ∏ i ∈ Finset.range (N + 1), (if i = 0 then 0 else c i) ^ e i
        = 0 := by
      apply Finset.prod_eq_zero
        (Finset.mem_range.mpr (Nat.zero_lt_succ N))
      rw [ite_eq_left rfl]
      exact zero_pow he0
    rw [hP]
    split_ifs <;> exact mul_zero _

private def bellReindex (N : ℕ) (m : Fin (N + 1) → ℕ) : ℕ → ℕ
  | 0 => 0
  | Nat.succ i => if h : i < N then m ⟨i, by omega⟩ else 0
private def mExt (N : ℕ) (m : Fin (N + 1) → ℕ) : ℕ → ℕ :=
  fun i => if h : i < N + 1 then m ⟨i, h⟩ else 0
private theorem mExt_eq (N : ℕ) (m : Fin (N + 1) → ℕ) (i : Fin (N + 1)) :
    mExt N m (i.val) = m i := by
  unfold mExt
  rw [dite_eq_left i.isLt]
private theorem bellReindex_succ_eq_mExt (N : ℕ) (m : Fin (N + 1) → ℕ) (i : ℕ) (hi : i < N) :
    bellReindex N m (i + 1) = mExt N m i := by
  have h1 : i + 1 = Nat.succ i := rfl
  rw [h1]
  simp only [bellReindex, dite_eq_left hi]
  unfold mExt
  rw [dite_eq_left (by omega)]
private theorem bellReindex_eq_mExt_succ (N : ℕ) (m : Fin (N + 1) → ℕ) (i : ℕ) (hi : i < N) :
    bellReindex N m (i + 1) * (i + 1) = mExt N m i * (i + 1) := by
  rw [bellReindex_succ_eq_mExt N m i hi]
private theorem bell_last_eq_zero (N : ℕ) (m : Fin (N + 1) → ℕ)
    (hmN : ∑ i, (i.val + 1) * m i = N) :
    m ⟨N, Nat.lt_succ_self N⟩ = 0 := by
  by_contra hne
  have hpos : 0 < m ⟨N, Nat.lt_succ_self N⟩ := Nat.pos_of_ne_zero hne
  have hsingle := Finset.single_le_sum
    (s := Finset.univ (α := Fin (N + 1)))
    (f := fun i => (i.val + 1) * m i)
    (fun i _ => Nat.zero_le _) (Finset.mem_univ ⟨N, Nat.lt_succ_self N⟩)
  rw [hmN] at hsingle
  have hval : (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)).val = N := rfl
  rw [hval] at hsingle
  have hge : N + 1 ≤ (N + 1) * m ⟨N, Nat.lt_succ_self N⟩ :=
    Nat.le_mul_of_pos_right _ hpos
  omega
private theorem bellReindex_mem (N k : ℕ) (m : Fin (N + 1) → ℕ)
    (hmN : ∑ i, (i.val + 1) * m i = N)
    (hmk : ∑ i, m i = k) :
    bellReindex N m ∈ (Finset.range (N + 1)).piAntidiag k := by
  rw [Finset.mem_piAntidiag]
  refine ⟨?_, ?_⟩
  · -- sum = k
    have hlast := bell_last_eq_zero N m hmN
    have hFin : (∑ i : Fin (N + 1), m i)
        = ∑ i ∈ Finset.range (N + 1), mExt N m i := by
      have h := Fin.sum_univ_eq_sum_range (mExt N m) (N + 1)
      rw [← h]
      apply Finset.sum_congr rfl
      intro i _
      exact (mExt_eq N m i).symm
    rw [hmk] at hFin
    have hMlast : mExt N m N = 0 := by
      have h1 : mExt N m N = m ⟨N, Nat.lt_succ_self N⟩ := by
        unfold mExt
        rw [dite_eq_left (Nat.lt_succ_self N)]
      rw [h1, hlast]
    have hRe : (∑ i ∈ Finset.range (N + 1), bellReindex N m i)
        = ∑ i ∈ Finset.range (N + 1), mExt N m i := by
      rw [Finset.sum_range_succ' (bellReindex N m) N]
      rw [Finset.sum_range_succ (mExt N m) N, hMlast, add_zero]
      change (∑ k ∈ Finset.range N, bellReindex N m (k + 1)) + bellReindex N m 0
        = ∑ x ∈ Finset.range N, mExt N m x
      simp only [bellReindex, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      exact bellReindex_succ_eq_mExt N m i hiN
    rw [hRe, ← hFin]
  · -- support
    intro i hi
    by_contra hmem
    have hle : N + 1 ≤ i := not_lt.mp (fun hlt => hmem (Finset.mem_range.mpr hlt))
    have h0 : bellReindex N m i = 0 := by
      match i with
      | 0 => omega
      | Nat.succ i =>
        simp only [bellReindex, dite_eq_right (by omega : ¬ i < N)]
    rw [h0] at hi
    exact hi rfl
private theorem bellReindex_weighted (N : ℕ) (m : Fin (N + 1) → ℕ)
    (hmN : ∑ i, (i.val + 1) * m i = N) :
    ∑ i ∈ Finset.range (N + 1), bellReindex N m i * i = N := by
  have hlast := bell_last_eq_zero N m hmN
  have hFin : (∑ i : Fin (N + 1), (i.val + 1) * m i)
      = ∑ i ∈ Finset.range (N + 1), mExt N m i * (i + 1) := by
    have h := Fin.sum_univ_eq_sum_range (fun i => mExt N m i * (i + 1)) (N + 1)
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    rw [mExt_eq N m i, mul_comm]
  rw [hmN] at hFin
  have hMlast : mExt N m N * (N + 1) = 0 := by
    have h1 : mExt N m N = m ⟨N, Nat.lt_succ_self N⟩ := by
      unfold mExt
      rw [dite_eq_left (Nat.lt_succ_self N)]
    rw [h1, hlast, zero_mul]
  have hRe : (∑ i ∈ Finset.range (N + 1), bellReindex N m i * i)
      = ∑ i ∈ Finset.range (N + 1), mExt N m i * (i + 1) := by
    rw [Finset.sum_range_succ' (fun i => bellReindex N m i * i) N]
    rw [Finset.sum_range_succ (fun i => mExt N m i * (i + 1)) N, hMlast, add_zero]
    change (∑ k ∈ Finset.range N, bellReindex N m (k + 1) * (k + 1))
        + bellReindex N m 0 * 0
      = ∑ x ∈ Finset.range N, mExt N m x * (x + 1)
    simp only [bellReindex, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    exact bellReindex_eq_mExt_succ N m i hiN
  rw [hRe, ← hFin]

/-- Inverse reindexing: piAntidiag function to Bell multiplicity vector. -/
private def eToBell (N : ℕ) (e : ℕ → ℕ) : Fin (N + 1) → ℕ :=
  fun j => e (j.val + 1)

private theorem bellReindex_prod_factorial (N : ℕ) (m : Fin (N + 1) → ℕ)
    (hmN : ∑ i, (i.val + 1) * m i = N) :
    ∏ i ∈ Finset.range (N + 1), (bellReindex N m i).factorial
    = ∏ j : Fin (N + 1), (m j).factorial := by
  have hlast := bell_last_eq_zero N m hmN
  have hME : (∏ j : Fin (N + 1), (m j).factorial)
      = ∏ i : Fin (N + 1), ((mExt N m i.val).factorial) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [mExt_eq N m i]
  have hR := Fin.prod_univ_eq_prod_range (fun i => ((mExt N m i).factorial)) (N + 1)
  have h2 := Finset.prod_range_succ (fun i => ((mExt N m i).factorial)) N
  have hMlast : (mExt N m N).factorial = 1 := by
    have h1 : mExt N m N = m ⟨N, Nat.lt_succ_self N⟩ := by
      unfold mExt
      rw [dite_eq_left (Nat.lt_succ_self N)]
    rw [h1, hlast, Nat.factorial_zero]
  have hFin : (∏ j : Fin (N + 1), (m j).factorial)
      = (∏ i ∈ Finset.range N, ((mExt N m i).factorial)) * 1 := by
    rw [hME, hR, h2, hMlast]
  rw [hFin, mul_one]
  rw [Finset.prod_range_succ' (fun i => (bellReindex N m i).factorial) N]
  simp only [bellReindex, Nat.factorial_zero, mul_one]
  apply Finset.prod_congr rfl
  intro i hi
  have hiN : i < N := Finset.mem_range.mp hi
  rw [dite_eq_left hiN]
  unfold mExt
  rw [dite_eq_left (by omega : i < N + 1)]

private theorem bellReindex_prod_pow (N : ℕ) {K : Type*} [Field K]
    (m : Fin (N + 1) → ℕ) (c : ℕ → K)
    (hmN : ∑ i, (i.val + 1) * m i = N) :
    ∏ i ∈ Finset.range (N + 1), (if i = 0 then (0 : K) else c i) ^ bellReindex N m i
    = ∏ j : Fin (N + 1), (c (j.val + 1)) ^ m j := by
  have hlast := bell_last_eq_zero N m hmN
  have hME : (∏ j : Fin (N + 1), ((c (j.val + 1) : K) ^ m j))
      = ∏ i : Fin (N + 1), (((c (i.val + 1) : K)) ^ mExt N m i.val) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [mExt_eq N m i]
  have hR := Fin.prod_univ_eq_prod_range
    (fun i => (((c (i + 1) : K)) ^ mExt N m i)) (N + 1)
  have h2 := Finset.prod_range_succ (fun i => (((c (i + 1) : K)) ^ mExt N m i)) N
  have hMlast : (((c (N + 1) : K)) ^ mExt N m N) = 1 := by
    have h1 : mExt N m N = m ⟨N, Nat.lt_succ_self N⟩ := by
      unfold mExt
      rw [dite_eq_left (Nat.lt_succ_self N)]
    rw [h1, hlast, pow_zero]
  have hFin : (∏ j : Fin (N + 1), ((c (j.val + 1) : K) ^ m j))
      = (∏ i ∈ Finset.range N, (((c (i + 1) : K)) ^ mExt N m i)) * 1 := by
    rw [hME, hR, h2, hMlast]
  rw [hFin, mul_one]
  rw [Finset.prod_range_succ'
    (fun i => ((if i = 0 then (0 : K) else c i) ^ bellReindex N m i)) N]
  have h0 : (((if (0 : ℕ) = 0 then (0 : K) else c 0) ^ bellReindex N m 0)) = 1 := by
    simp [bellReindex]
  rw [h0, mul_one]
  apply Finset.prod_congr rfl
  intro i hi
  have hiN : i < N := Finset.mem_range.mp hi
  have hbell : bellReindex N m (i + 1) = mExt N m i :=
    bellReindex_succ_eq_mExt N m i hiN
  rw [hbell, ite_eq_right (by omega : i + 1 ≠ 0)]

private theorem eToBell_sum (N k : ℕ) (e : ℕ → ℕ)
    (hmem : e ∈ (Finset.range (N + 1)).piAntidiag k)
    (he0 : e 0 = 0) :
    ∑ j : Fin (N + 1), eToBell N e j = k := by
  have hsum : ∑ i ∈ Finset.range (N + 1), e i = k :=
    (Finset.mem_piAntidiag.mp hmem).1
  have hsup : ∀ i, e i ≠ 0 → i ∈ Finset.range (N + 1) :=
    (Finset.mem_piAntidiag.mp hmem).2
  have heN1 : e (N + 1) = 0 := by
    by_contra hne
    have h := hsup (N + 1) hne
    simp at h
  have hFin : (∑ j : Fin (N + 1), eToBell N e j)
      = ∑ i ∈ Finset.range (N + 1), e (i + 1) := by
    have h := Fin.sum_univ_eq_sum_range (fun i => e (i + 1)) (N + 1)
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [hFin]
  have hA := Finset.sum_range_succ (fun i => e i) (N + 1)
  have hB := Finset.sum_range_succ' (fun i => e i) (N + 1)
  omega

private theorem eToBell_weighted (N k : ℕ) (e : ℕ → ℕ)
    (hmem : e ∈ (Finset.range (N + 1)).piAntidiag k)
    (hweighted : ∑ i ∈ Finset.range (N + 1), e i * i = N) :
    ∑ j : Fin (N + 1), (j.val + 1) * eToBell N e j = N := by
  have hsup : ∀ i, e i ≠ 0 → i ∈ Finset.range (N + 1) :=
    (Finset.mem_piAntidiag.mp hmem).2
  have heN1 : e (N + 1) = 0 := by
    by_contra hne
    have h := hsup (N + 1) hne
    simp at h
  have hFin : (∑ j : Fin (N + 1), (j.val + 1) * eToBell N e j)
      = ∑ i ∈ Finset.range (N + 1), (i + 1) * e (i + 1) := by
    have h := Fin.sum_univ_eq_sum_range (fun i => (i + 1) * e (i + 1)) (N + 1)
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [hFin]
  have hA := Finset.sum_range_succ (fun i => e i * i) (N + 1)
  have hB := Finset.sum_range_succ' (fun i => e i * i) (N + 1)
  have hC0 : e 0 * 0 = 0 := Nat.mul_zero _
  have hCN1 : e (N + 1) * (N + 1) = 0 := by rw [heN1, zero_mul]
  have hEq : (∑ i ∈ Finset.range (N + 1), (i + 1) * e (i + 1))
      = ∑ i ∈ Finset.range (N + 1), e (i + 1) * (i + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  omega

private theorem eToBell_bellReindex (N : ℕ) (m : Fin (N + 1) → ℕ)
    (hmN : ∑ i, (i.val + 1) * m i = N) :
    eToBell N (bellReindex N m) = m := by
  have hlast := bell_last_eq_zero N m hmN
  funext j
  unfold eToBell
  by_cases hj : j.val < N
  · rw [bellReindex_succ_eq_mExt N m j.val hj]
    exact mExt_eq N m j
  · have hjN : j.val = N := by omega
    have hbell : bellReindex N m (j.val + 1) = 0 := by
      have h1 : j.val + 1 = Nat.succ j.val := rfl
      rw [h1]
      simp only [bellReindex, dite_eq_right (by omega : ¬ j.val < N)]
    rw [hbell]
    have hj_eq : j = ⟨N, Nat.lt_succ_self N⟩ := by
      apply Fin.ext
      simp [hjN]
    rw [hj_eq, hlast]

private theorem bellReindex_eToBell (N k : ℕ) (e : ℕ → ℕ)
    (hmem : e ∈ (Finset.range (N + 1)).piAntidiag k)
    (he0 : e 0 = 0) :
    bellReindex N (eToBell N e) = e := by
  have hsup : ∀ i, e i ≠ 0 → i ∈ Finset.range (N + 1) :=
    (Finset.mem_piAntidiag.mp hmem).2
  funext i
  match i with
  | 0 =>
    simp only [bellReindex]
    exact he0.symm
  | Nat.succ j =>
    by_cases hj : j < N
    · have h1 : Nat.succ j = j + 1 := rfl
      rw [h1, bellReindex_succ_eq_mExt N (eToBell N e) j hj]
      unfold mExt eToBell
      rw [dite_eq_left (by omega : j < N + 1)]
    · have hbell : bellReindex N (eToBell N e) (Nat.succ j) = 0 := by
        simp only [bellReindex, dite_eq_right (by omega : ¬ j < N)]
      rw [hbell]
      by_contra hne
      have h := hsup (Nat.succ j) (Ne.symm hne)
      simp at h
      omega

private theorem bell_term_eq (N k : ℕ) {K : Type*} [Field K] [CharZero K]
    (c : ℕ → K) (m : Fin (N + 1) → ℕ)
    (hmN : ∑ i, (i.val + 1) * m i = N)
    (hmk : ∑ i, m i = k) :
    (k.factorial : K) * ∏ j : Fin (N + 1), ((c (j.val + 1)) ^ m j / ((m j).factorial : K))
    = (((Nat.multinomial (Finset.range (N + 1)) (bellReindex N m) : ℕ)) : K)
      * ∏ i ∈ Finset.range (N + 1),
        (if i = 0 then (0 : K) else c i) ^ bellReindex N m i := by
  have hmem := bellReindex_mem N k m hmN hmk
  have hsum : ∑ i ∈ Finset.range (N + 1), bellReindex N m i = k :=
    (Finset.mem_piAntidiag.mp hmem).1
  have hspec := Nat.multinomial_spec (Finset.range (N + 1)) (bellReindex N m)
  rw [hsum] at hspec
  have hfact := bellReindex_prod_factorial N m hmN
  have hpow := bellReindex_prod_pow N m c hmN
  have hcast : (∏ j : Fin (N + 1), (((m j).factorial : ℕ) : K))
      * (((Nat.multinomial (Finset.range (N + 1)) (bellReindex N m) : ℕ)) : K)
      = ((k.factorial : ℕ) : K) := by
    have h := congrArg (fun n : ℕ => ((n : ℕ) : K)) hspec
    simp only [Nat.cast_mul] at h
    rw [hfact, Nat.cast_prod] at h
    exact h
  have hprod_ne : (∏ j : Fin (N + 1), (((m j).factorial : ℕ) : K)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hmulti : ((((Nat.multinomial (Finset.range (N + 1)) (bellReindex N m) : ℕ))) : K)
      = ((k.factorial : ℕ) : K) / (∏ j : Fin (N + 1), (((m j).factorial : ℕ) : K)) := by
    rw [eq_div_iff hprod_ne, mul_comm]
    exact hcast
  rw [hmulti, hpow]
  rw [div_mul_eq_mul_div, mul_div_assoc]
  congr 1
  rw [Finset.prod_div_distrib]

private theorem bell_mem_bound (N : ℕ) (m : Fin (N + 1) → ℕ)
    (hmN : ∑ i, (i.val + 1) * m i = N) (j : Fin (N + 1)) :
    m j < N + 1 := by
  have hle : (j.val + 1) * m j ≤ ∑ i, (i.val + 1) * m i := by
    have h := Finset.single_le_sum
      (s := Finset.univ (α := Fin (N + 1)))
      (f := fun i => (i.val + 1) * m i)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    exact h
  rw [hmN] at hle
  have h1 : 1 ≤ j.val + 1 := Nat.le_add_left _ _
  have h2 : m j ≤ (j.val + 1) * m j := Nat.le_mul_of_pos_left _ h1
  omega

private theorem bell_bridge_stepA (N k : ℕ) {K : Type*} [Field K] [CharZero K] (c : ℕ → K) :
    PowerSeries.coeff N ((PowerSeries.mk (fun m => if m = 0 then 0 else c m)) ^ k)
    = (k.factorial : K) * ∑ m ∈ (Fintype.piFinset fun _ : Fin (N + 1) => Finset.range
        (N + 1)).filter
        (fun m => (∑ i, (i.val + 1) * m i = N) ∧ ∑ i, m i = k),
      ∏ j : Fin (N + 1), ((c (j.val + 1)) ^ m j / ((m j).factorial : K)) := by
  rw [coeff_trunc_eq N k c, coeff_trunc_expand N k c, piAntidiag_filter_sum N k c]
  set S := ((Finset.range (N + 1)).piAntidiag k).filter
    (fun e => e 0 = 0 ∧ ∑ i ∈ Finset.range (N + 1), e i * i = N) with hS
  set T := (Fintype.piFinset fun _ : Fin (N + 1) => Finset.range (N + 1)).filter
    (fun m => (∑ i, (i.val + 1) * m i = N) ∧ ∑ i, m i = k) with hT
  have h_eq : (∑ m ∈ T, (k.factorial : K) *
        ∏ j : Fin (N + 1), ((c (j.val + 1)) ^ m j / ((m j).factorial : K)))
      = ∑ e ∈ S, (((Nat.multinomial (Finset.range (N + 1)) e : ℕ)) : K)
        * (∏ i ∈ Finset.range (N + 1), (if i = 0 then 0 else c i) ^ e i) := by
    apply Finset.sum_bij' (fun m _ => bellReindex N m) (fun e _ => eToBell N e)
    · intro m hm
      rw [hT] at hm
      rw [Finset.mem_filter] at hm
      obtain ⟨hmem_pi, hmN, hmk⟩ := hm
      have hmem := bellReindex_mem N k m hmN hmk
      have hw := bellReindex_weighted N m hmN
      rw [hS, Finset.mem_filter]
      exact ⟨hmem, rfl, hw⟩
    · intro e he
      rw [hS] at he
      rw [Finset.mem_filter] at he
      obtain ⟨hmem_pi, he0, hweighted⟩ := he
      have hsum := eToBell_sum N k e hmem_pi he0
      have hweight := eToBell_weighted N k e hmem_pi hweighted
      rw [hT, Finset.mem_filter]
      refine ⟨?_, hweight, hsum⟩
      rw [Fintype.mem_piFinset]
      intro i
      have hbound := bell_mem_bound N (eToBell N e) hweight i
      exact Finset.mem_range.mpr hbound
    · intro m hm
      rw [hT] at hm
      rw [Finset.mem_filter] at hm
      obtain ⟨hmem_pi, hmN, hmk⟩ := hm
      exact eToBell_bellReindex N m hmN
    · intro e he
      rw [hS] at he
      rw [Finset.mem_filter] at he
      obtain ⟨hmem_pi, he0, hweighted⟩ := he
      exact bellReindex_eToBell N k e hmem_pi he0
    · intro m hm
      rw [hT] at hm
      rw [Finset.mem_filter] at hm
      obtain ⟨hmem_pi, hmN, hmk⟩ := hm
      exact bell_term_eq N k c m hmN hmk
  rw [Finset.mul_sum]
  exact h_eq.symm

private theorem bell_bridge_stepB (N k : ℕ) {K : Type*} [Field K] [CharZero K] (c : ℕ → K) :
    partialBellPolynomial N k (fun j => ((j.factorial : ℕ) : K) * c j)
    = (N.factorial : K) * ∑ m ∈ (Fintype.piFinset fun _ : Fin (N + 1) => Finset.range
        (N + 1)).filter
        (fun m => (∑ i, (i.val + 1) * m i = N) ∧ ∑ i, m i = k),
      ∏ j : Fin (N + 1), ((c (j.val + 1)) ^ m j / ((m j).factorial : K)) := by
  unfold partialBellPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_filter] at hm
  obtain ⟨hmem_pi, hmN, hmk⟩ := hm
  set D : ℕ := ∏ i, ((m i).factorial * (i.val + 1).factorial ^ m i) with hD
  have hDvd : D ∣ N.factorial := bell_denom_dvd (N + 1) N m hmN
  have hDK_ne : ((D : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by
    intro h0
    have : D = 0 := h0
    rw [this] at hDvd
    have := Nat.factorial_ne_zero N
    omega)
  have hcast : ((((N.factorial / D : ℕ))) : K) = ((N.factorial : ℕ) : K) / ((D : ℕ) : K) := by
    exact Nat.cast_div hDvd hDK_ne
  have hA : ((D : ℕ) : K) = (∏ j : Fin (N + 1), (((m j).factorial : ℕ) : K))
      * (∏ j : Fin (N + 1), ((((j.val + 1).factorial : ℕ) : K) ^ m j)) := by
    rw [hD, Nat.cast_prod]
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [Finset.prod_mul_distrib]
  have hP : (∏ i, ((((i.val + 1).factorial : ℕ) : K) * c (i.val + 1)) ^ m i)
      = (∏ j : Fin (N + 1), ((((j.val + 1).factorial : ℕ) : K) ^ m j))
        * (∏ j : Fin (N + 1), ((c (j.val + 1)) ^ m j)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [mul_pow]
  have hBK_ne : (∏ j : Fin (N + 1), ((((j.val + 1).factorial : ℕ) : K) ^ m j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply pow_ne_zero
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hC : (∏ j : Fin (N + 1), ((c (j.val + 1)) ^ m j / ((m j).factorial : K)))
      = (∏ j : Fin (N + 1), ((c (j.val + 1)) ^ m j))
        / (∏ j : Fin (N + 1), (((m j).factorial : ℕ) : K)) := by
    rw [Finset.prod_div_distrib]
  rw [hcast, hA, hP, hC]
  field_simp

private theorem bell_bridge (N k : ℕ) {K : Type*} [Field K] [CharZero K] (c : ℕ → K) :
    PowerSeries.coeff N ((PowerSeries.mk (fun m => if m = 0 then 0 else c m)) ^ k)
    = ((k.factorial : ℕ) : K) / ((N.factorial : ℕ) : K)
      * partialBellPolynomial N k (fun j => ((j.factorial : ℕ) : K) * c j) := by
  rw [bell_bridge_stepA N k c, bell_bridge_stepB N k c]
  have hN : (((N.factorial : ℕ)) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

private theorem natDegree_C_mul_mul_le {R : Type*} [Semiring R]
    (a : R) (p q : Polynomial R) (m1 m2 : ℕ)
    (hp : p.natDegree ≤ m1) (hq : q.natDegree ≤ m2) :
    (Polynomial.C a * p * q).natDegree ≤ m1 + m2 := by
  calc (Polynomial.C a * p * q).natDegree
      ≤ (Polynomial.C a * p).natDegree + q.natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ p.natDegree + q.natDegree :=
        Nat.add_le_add_right (Polynomial.natDegree_C_mul_le _ _) _
    _ ≤ m1 + m2 := Nat.add_le_add hp hq

private theorem asc_mul_C_degree (i : ℕ) {K : Type*} [Field K] [CharZero K] (c : K) :
    ((ascPochhammer K i) * Polynomial.C c : Polynomial K).natDegree ≤ i := by
  calc ((ascPochhammer K i) * Polynomial.C c : Polynomial K).natDegree
      ≤ (ascPochhammer K i).natDegree := Polynomial.natDegree_mul_C_le _ _
    _ = i := ascPochhammer_natDegree K i

private theorem desc_comp_mul_C_mul_C_degree (n i : ℕ) {K : Type*} [Field K] [CharZero K]
    (c3 c4 : K) :
    ((((descPochhammer K (n - i)).comp (Polynomial.X + Polynomial.C (n : K)))
      * Polynomial.C c3 * Polynomial.C c4) : Polynomial K).natDegree ≤ n - i := by
  have h2 : ((descPochhammer K (n - i)).comp
      (Polynomial.X + Polynomial.C (n : K))).natDegree = n - i := by
    rw [Polynomial.natDegree_comp, descPochhammer_natDegree,
      Polynomial.natDegree_X_add_C]
    ring
  calc ((((descPochhammer K (n - i)).comp (Polynomial.X + Polynomial.C (n : K)))
      * Polynomial.C c3 * Polynomial.C c4) : Polynomial K).natDegree
      ≤ ((((descPochhammer K (n - i)).comp (Polynomial.X + Polynomial.C (n : K)))
        * Polynomial.C c3)).natDegree := Polynomial.natDegree_mul_C_le _ _
    _ ≤ ((descPochhammer K (n - i)).comp
        (Polynomial.X + Polynomial.C (n : K))).natDegree :=
        Polynomial.natDegree_mul_C_le _ _
    _ = n - i := h2

private theorem asc_at_neg (i j : ℕ) {K : Type*} [Field K] [CharZero K] :
    Polynomial.eval (-(j : K)) (ascPochhammer K i)
    = (-1 : K) ^ i * ((j.descFactorial i : ℕ) : K) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]

private theorem desc_comp_at_neg (n i j : ℕ) {K : Type*} [Field K] [CharZero K]
    (hj : j ≤ n) :
    Polynomial.eval (-(j : K))
      ((descPochhammer K (n - i)).comp (Polynomial.X + Polynomial.C (n : K)))
    = ((((n - j).descFactorial (n - i) : ℕ))) := by
  rw [Polynomial.eval_comp]
  have hXn : Polynomial.eval (-(j : K)) (Polynomial.X + Polynomial.C (n : K))
      = (((n - j : ℕ)) : K) := by
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      Nat.cast_sub hj]
    abel
  rw [hXn, descPochhammer_eval_eq_descFactorial]

private theorem coeff_ghat_mul_g (n k : ℕ) {K : Type*} [Field K]
    (g ghat : PowerSeries K)
    (hg1 : PowerSeries.constantCoeff g = 1) :
    PowerSeries.coeff n (ghat ^ n * g ^ k)
    = ∑ j ∈ Finset.range (n + 1),
      ((k.choose j : ℕ) : K) * PowerSeries.coeff n (ghat ^ n * (g - 1) ^ j) := by
  set u : PowerSeries K := g - 1 with hu
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    rw [hu, map_sub]
    simp [hg1]
  have hXu : PowerSeries.X ∣ u := PowerSeries.X_dvd_iff.mpr hu0
  have hug : u + 1 = g := by rw [hu]; abel
  have hterm : ∀ m : ℕ, PowerSeries.coeff n
      (ghat ^ n * (u ^ m * ((k.choose m : ℕ) : PowerSeries K)))
      = ((k.choose m : ℕ) : K) * PowerSeries.coeff n (ghat ^ n * u ^ m) := by
    intro m
    have hrw : ghat ^ n * (u ^ m * ((k.choose m : ℕ) : PowerSeries K))
        = ((k.choose m : ℕ) : PowerSeries K) * (ghat ^ n * u ^ m) := by ring
    rw [hrw, PowerSeries.coeff_natCast_mul]
  have hbase : PowerSeries.coeff n (ghat ^ n * g ^ k)
      = ∑ m ∈ Finset.range (k + 1),
        ((k.choose m : ℕ) : K) * PowerSeries.coeff n (ghat ^ n * u ^ m) := by
    have hgg : ghat ^ n * g ^ k
        = ∑ m ∈ Finset.range (k + 1),
          (ghat ^ n * (u ^ m * ((k.choose m : ℕ) : PowerSeries K))) := by
      conv_lhs => rw [← hug]
      rw [add_pow u 1 k, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      simp only [one_pow, mul_one]
    rw [hgg, map_sum]
    apply Finset.sum_congr rfl
    intro m _
    exact hterm m
  have hvan_n : ∀ m ∈ Finset.range (k + 1), m ∉ Finset.range (n + 1) →
      ((k.choose m : ℕ) : K) * PowerSeries.coeff n (ghat ^ n * u ^ m) = 0 := by
    intro m _ hmn
    have hmn' : n < m := by
      have : ¬ m < n + 1 := fun h => hmn (Finset.mem_range.mpr h)
      omega
    have hdvd : PowerSeries.X ^ m ∣ ghat ^ n * u ^ m := by
      have h1 : PowerSeries.X ^ m ∣ u ^ m := pow_dvd_pow_of_dvd hXu m
      have h2 : u ^ m ∣ ghat ^ n * u ^ m := dvd_mul_left _ _
      exact dvd_trans h1 h2
    obtain ⟨H, hH⟩ := hdvd
    have hcoeff : PowerSeries.coeff n (ghat ^ n * u ^ m) = 0 := by
      rw [hH, PowerSeries.coeff_X_pow_mul']
      exact ite_eq_right (by omega : ¬ m ≤ n)
    rw [hcoeff, mul_zero]
  have hvan_k : ∀ m ∈ Finset.range (n + 1), m ∉ Finset.range (k + 1) →
      ((k.choose m : ℕ) : K) * PowerSeries.coeff n (ghat ^ n * u ^ m) = 0 := by
    intro m _ hmk
    have hmk' : k < m := by
      have : ¬ m < k + 1 := fun h => hmk (Finset.mem_range.mpr h)
      omega
    have hchoose : ((k.choose m : ℕ) : K) = 0 := by
      rw [Nat.choose_eq_zero_of_lt hmk']
      simp
    rw [hchoose, zero_mul]
  by_cases hle : n ≤ k
  · have hsub : Finset.range (n + 1) ⊆ Finset.range (k + 1) := by
      rw [Finset.range_subset]
      intro x hx
      exact Finset.mem_range.mpr (by omega)
    rw [hbase]
    symm
    exact Finset.sum_subset hsub hvan_n
  · have hsub : Finset.range (k + 1) ⊆ Finset.range (n + 1) := by
      rw [Finset.range_subset]
      intro x hx
      have hlt : k < n := Nat.lt_of_not_ge hle
      exact Finset.mem_range.mpr (by omega)
    rw [hbase]
    exact Finset.sum_subset hsub hvan_k

/-- Auxiliary polynomial `Q` for interpolation: `n! * Σ d_j * desc_j(X+n)/j!`. -/
private noncomputable def howardQGen (n : ℕ) {K : Type*} [Field K] (d : ℕ → K) : Polynomial K :=
  Polynomial.C (n.factorial : K) * ∑ j ∈ Finset.range (n + 1),
    Polynomial.C (d j) * (((descPochhammer K j).comp
      (Polynomial.X + Polynomial.C (n : K))) * Polynomial.C (((j.factorial : K))⁻¹))

private theorem howardQ_degree (n : ℕ) {K : Type*} [Field K] [CharZero K] (d : ℕ → K) :
    (howardQGen n d).natDegree ≤ n := by
  unfold howardQGen
  have hsum : (∑ j ∈ Finset.range (n + 1),
      Polynomial.C (d j) * (((descPochhammer K j).comp
        (Polynomial.X + Polynomial.C (n : K))) * Polynomial.C (((j.factorial : K))⁻¹))
      : Polynomial K).natDegree ≤ n := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hdesc : ((descPochhammer K j).comp
        (Polynomial.X + Polynomial.C (n : K))).natDegree = j := by
      rw [Polynomial.natDegree_comp, descPochhammer_natDegree,
        Polynomial.natDegree_X_add_C]
      ring
    have hterm : (Polynomial.C (d j) * (((descPochhammer K j).comp
        (Polynomial.X + Polynomial.C (n : K))) * Polynomial.C (((j.factorial : K))⁻¹))
        : Polynomial K).natDegree ≤ j := by
      calc (Polynomial.C (d j) * (((descPochhammer K j).comp
          (Polynomial.X + Polynomial.C (n : K))) * Polynomial.C (((j.factorial : K))⁻¹))
          : Polynomial K).natDegree
          ≤ (((descPochhammer K j).comp
            (Polynomial.X + Polynomial.C (n : K))) * Polynomial.C
                (((j.factorial : K))⁻¹)).natDegree :=
            Polynomial.natDegree_C_mul_le _ _
        _ ≤ ((descPochhammer K j).comp
            (Polynomial.X + Polynomial.C (n : K))).natDegree :=
            Polynomial.natDegree_mul_C_le _ _
        _ = j := hdesc
    omega
  calc (Polynomial.C (n.factorial : K) * ∑ j ∈ Finset.range (n + 1),
      Polynomial.C (d j) * (((descPochhammer K j).comp
        (Polynomial.X + Polynomial.C (n : K))) * Polynomial.C (((j.factorial : K))⁻¹))
      : Polynomial K).natDegree
      ≤ (∑ j ∈ Finset.range (n + 1),
        Polynomial.C (d j) * (((descPochhammer K j).comp
          (Polynomial.X + Polynomial.C (n : K))) * Polynomial.C (((j.factorial : K))⁻¹))
        : Polynomial K).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ n := hsum

private theorem howardQ_eval (n k : ℕ) {K : Type*} [Field K] [CharZero K] (d : ℕ → K) :
    Polynomial.eval ((k : K) - (n : K)) (howardQGen n d)
    = (n.factorial : K) * ∑ j ∈ Finset.range (n + 1),
      (d j) * ((k.choose j : ℕ) : K) := by
  unfold howardQGen
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_C]
  have hX : Polynomial.eval ((k : K) - (n : K))
      (Polynomial.X + Polynomial.C (n : K)) = (k : K) := by
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    abel
  have hdesc : Polynomial.eval ((k : K) - (n : K))
      ((descPochhammer K j).comp (Polynomial.X + Polynomial.C (n : K)))
      = (((k.choose j : ℕ)) : K) * ((j.factorial : ℕ) : K) := by
    rw [Polynomial.eval_comp, hX, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  rw [hdesc]
  have hfj : (((j.factorial : ℕ)) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

private theorem howard_S_eq (r : ℕ) {K : Type*} [Field K] [CharZero K]
    (a : ℕ → K) (hr : 1 ≤ r) (har : a r ≠ 0) :
    PowerSeries.mk (fun m => if m = 0 then (0 : K) else
        (if r ≤ m then a m / ((m.factorial : ℕ) : K) else 0))
    = PowerSeries.C ((a r) / ((r.factorial : ℕ) : K)) *
      (PowerSeries.X ^ r * PowerSeries.mk (fun k => ((r.factorial : ℕ) : K) * a (r + k) /
        (a r * (((r + k).factorial : ℕ) : K)))) := by
  apply PowerSeries.ext_iff.mpr
  intro n
  rw [PowerSeries.coeff_mk]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hrn : r ≤ n
  · have hn0 : n ≠ 0 := by omega
    have hnr : r + (n - r) = n := Nat.add_sub_cancel' hrn
    have hcoeff : PowerSeries.coeff (n - r)
          (PowerSeries.mk (fun k => ((r.factorial : ℕ) : K) * a (r + k) /
            (a r * (((r + k).factorial : ℕ) : K))))
          = ((r.factorial : ℕ) : K) * a n / (a r * (((n.factorial : ℕ)) : K)) := by
      rw [PowerSeries.coeff_mk, hnr]
    rw [ite_eq_left hrn, ite_eq_right hn0, ite_eq_left hrn, hcoeff]
    have hrF : (((r.factorial : ℕ)) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hnF : (((n.factorial : ℕ)) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  · have hRHS : ((a r) / ((r.factorial : ℕ) : K)) *
          (if r ≤ n then PowerSeries.coeff (n - r)
            (PowerSeries.mk (fun k => ((r.factorial : ℕ) : K) * a (r + k) /
              (a r * (((r + k).factorial : ℕ) : K)))) else 0) = 0 := by
      rw [ite_eq_right hrn, mul_zero]
    have hLHS : (if n = 0 then (0 : K) else
        (if r ≤ n then a n / (((n.factorial : ℕ)) : K) else 0)) = 0 := by
      by_cases hn0 : n = 0
      · rw [ite_eq_left hn0]
      · rw [ite_eq_right hn0, ite_eq_right hrn]
    rw [hLHS, hRHS]

private theorem howard_factorial_mul_c (r j : ℕ) {K : Type*} [Field K] [CharZero K]
    (a : ℕ → K) :
    (((j.factorial : ℕ)) : K) * (if r ≤ j then a j / (((j.factorial : ℕ)) : K) else 0)
    = (if r ≤ j then a j else 0) := by
  by_cases h : r ≤ j
  · rw [ite_eq_left h, ite_eq_left h]
    have hj : ((((j.factorial : ℕ))) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

private theorem howard_coeff_S (r n j : ℕ) {K : Type*} [Field K] [CharZero K]
    (a : ℕ → K) (hr : 1 ≤ r) (har : a r ≠ 0) :
    PowerSeries.coeff (n + r * j)
      ((PowerSeries.mk (fun m => if m = 0 then (0 : K)
        else (if r ≤ m then a m / (((m.factorial : ℕ)) : K) else 0))) ^ j)
    = (((a r) / (((r.factorial : ℕ)) : K)) ^ j)
      * PowerSeries.coeff n
        ((PowerSeries.mk (fun k => ((r.factorial : ℕ) : K) * a (r + k) /
          (a r * (((r + k).factorial : ℕ) : K)))) ^ j) := by
  have hCpow : (PowerSeries.C ((a r) / (((r.factorial : ℕ)) : K)) : PowerSeries K) ^ j
      = PowerSeries.C ((((a r) / (((r.factorial : ℕ)) : K)) ^ j)) := by
    rw [← map_pow]
  have hXpow : (PowerSeries.X ^ r : PowerSeries K) ^ j = PowerSeries.X ^ (r * j) := by
    rw [← pow_mul]
  have hpow : (PowerSeries.mk (fun m => if m = 0 then (0 : K)
        else (if r ≤ m then a m / (((m.factorial : ℕ)) : K) else 0))) ^ j
      = PowerSeries.C ((((a r) / (((r.factorial : ℕ)) : K)) ^ j)) *
        (PowerSeries.X ^ (r * j) *
          (PowerSeries.mk (fun k => ((r.factorial : ℕ) : K) * a (r + k) /
            (a r * (((r + k).factorial : ℕ) : K)))) ^ j) := by
    conv_lhs => rw [howard_S_eq r a hr har]
    rw [mul_pow, mul_pow, hXpow, hCpow]
  rw [hpow, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  rw [ite_eq_left (Nat.le_add_left _ _)]
  have hsub : (n + r * j) - (r * j) = n := Nat.add_sub_cancel n (r * j)
  rw [hsub]

private theorem howard_Bell_eq (r n j : ℕ) {K : Type*} [Field K] [CharZero K]
    (a : ℕ → K) (hr : 1 ≤ r) (har : a r ≠ 0) :
    partialBellPolynomial (n + r * j) j (fun t => if r ≤ t then a t else 0)
    = ((((n + r * j).factorial : ℕ)) : K) / ((((j.factorial : ℕ))) : K)
      * (((((a r) / (((r.factorial : ℕ)) : K)) ^ j))
        * PowerSeries.coeff n
          ((PowerSeries.mk (fun k => ((r.factorial : ℕ) : K) * a (r + k) /
            (a r * (((r + k).factorial : ℕ) : K)))) ^ j)) := by
  have hbridge := bell_bridge (n + r * j) j
    (fun m => if r ≤ m then a m / (((m.factorial : ℕ)) : K) else 0)
  have hcoeffS := howard_coeff_S r n j a hr har
  have hfun : (fun t => (((t.factorial : ℕ)) : K) *
        (if r ≤ t then a t / (((t.factorial : ℕ)) : K) else 0))
      = (fun t => if r ≤ t then a t else 0) := by
    funext t
    exact howard_factorial_mul_c r t a
  rw [hfun] at hbridge
  rw [hcoeffS] at hbridge
  have hj : ((((j.factorial : ℕ))) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hN : ((((n + r * j).factorial : ℕ)) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hcancel : ((((n + r * j).factorial : ℕ)) : K) / ((((j.factorial : ℕ))) : K)
      * (((((j.factorial : ℕ))) : K) / ((((n + r * j).factorial : ℕ)) : K)) = 1 := by
    field_simp
  calc partialBellPolynomial (n + r * j) j (fun t => if r ≤ t then a t else 0)
      = 1 * partialBellPolynomial (n + r * j) j (fun t => if r ≤ t then a t else 0) := by
        rw [one_mul]
    _ = (((((n + r * j).factorial : ℕ)) : K) / ((((j.factorial : ℕ))) : K)
          * (((((j.factorial : ℕ))) : K) / ((((n + r * j).factorial : ℕ)) : K)))
        * partialBellPolynomial (n + r * j) j (fun t => if r ≤ t then a t else 0) := by
        rw [hcancel]
    _ = ((((n + r * j).factorial : ℕ)) : K) / ((((j.factorial : ℕ))) : K)
        * ((((((j.factorial : ℕ))) : K) / ((((n + r * j).factorial : ℕ)) : K))
          * partialBellPolynomial (n + r * j) j (fun t => if r ≤ t then a t else 0)) := by
        ring
    _ = ((((n + r * j).factorial : ℕ)) : K) / ((((j.factorial : ℕ))) : K)
        * (((((a r) / (((r.factorial : ℕ)) : K)) ^ j))
          * PowerSeries.coeff n
            ((PowerSeries.mk (fun k => ((r.factorial : ℕ) : K) * a (r + k) /
              (a r * (((r + k).factorial : ℕ) : K)))) ^ j)) := by
        congr 1
        exact hbridge.symm

private theorem howard_g_coeff_one (r : ℕ) {K : Type*} [Field K] [CharZero K]
    (a : ℕ → K) (har : a r ≠ 0) :
    PowerSeries.constantCoeff
      (PowerSeries.mk (fun k => (r.factorial : K) * a (r + k) /
        (a r * ((r + k).factorial : K)))) = 1 := by
  rw [PowerSeries.constantCoeff_mk]
  simp only [Nat.add_zero]
  have hrF : (((r.factorial : ℕ)) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

private theorem natDegree_C_mul4_le {R : Type*} [Semiring R]
    (a : R) (p q r : Polynomial R) (m1 m2 m3 : ℕ)
    (hp : p.natDegree ≤ m1) (hq : q.natDegree ≤ m2) (hr : r.natDegree ≤ m3) :
    (Polynomial.C a * p * q * r).natDegree ≤ m1 + m2 + m3 := by
  calc (Polynomial.C a * p * q * r).natDegree
      ≤ (Polynomial.C a * p * q).natDegree + r.natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ (m1 + m2) + m3 := Nat.add_le_add
        (natDegree_C_mul_mul_le a p q m1 m2 hp hq) hr

/-- **Howard's formula for potential polynomials.** Let $K$ be a field of characteristic zero,
let $r \ge 1$ and $n$ be natural numbers, and let $a_0, a_1, a_2, \dots$ be a sequence in $K$
with $a_r \ne 0$. Let $g$ be the formal power series
$$g(x) = \sum_{k \ge 0} \frac{r!\, a_{r+k}}{a_r\, (r+k)!}\, x^k,$$
let $g^{-1}$ be its inverse in $K[[x]]$, and write $[x^n]\, f$ for the coefficient of $x^n$ in a
power series $f$. Let $P \in K[X]$ be a polynomial of degree at most $n$ such that
$P(m) = n!\, [x^n]\, (g^{-1})^m$ for every natural number $m \le n$. Then
$$P(X) = \sum_{i=0}^{n} (-1)^i \left(\frac{r!}{a_r}\right)^i \frac{n!\, i!}{(n+ri)!} \cdot
\frac{X(X+1)\cdots(X+i-1)}{i!} \cdot \frac{(X+n)(X+n-1)\cdots(X+i+1)}{(n-i)!} \cdot
B_{n+ri,\,i}(\tilde a),$$
where empty products equal $1$, $B_{n+ri,\,i}$ is the partial Bell polynomial, and $\tilde a$
is the sequence with $\tilde a_j = a_j$ for $j \ge r$ and $\tilde a_j = 0$ for $j < r$.

Source: G. Nemes, Journal of Integer Sequences 13 (2010).
Source URL: https://cs.uwaterloo.ca/journals/JIS/VOL13/Nemes/nemes2.tex
Generic span: lines 120-133; specialization span: lines 166-173.
File SHA256: f3556d7fdb4d3f9366c3505d2cd20564f431d71a337e9f3a4fc7c24431df2daf
Span SHA256 (generic): c3e6c35fd19388416b9e1105e7b027a70c3956f58c8d204c44e88a0936273a04
Span SHA256 (specialization): bcc9e205ea075840eda33c04ff69e3f762b50e16bdc4627ed06ac9351fd4348c
Statement IDs: jis_f8773fd39faf6ec979df6672 and jis_rank35_proof_specialization_lines_166_173
Grounded concept ID: jis_grounded_097dd40d7498e5b441a12749
Exact-rational probe: passed 75 comparisons across r=1,2,3, n=0,...,4, natural z=0,...,n+2; finite
evidence only.

Proves `Wanted` entry `howard_potentialPolynomial_eq_partialBell`.
-/
theorem howard_potentialPolynomial_eq_partialBell
  {K : Type*} [Field K] [CharZero K]
  (r n : ℕ) (hr : 1 ≤ r) (a : ℕ → K) (har : a r ≠ 0)
  (P : Polynomial K)
  (hdeg : P.natDegree ≤ n)
  (heval : ∀ m : ℕ, m ≤ n →
    P.eval (↑m : K) = (n.factorial : K) *
      PowerSeries.coeff n
        ((PowerSeries.inv (PowerSeries.mk (fun k => (r.factorial : K) * a (r + k) /
          (a r * ((r + k).factorial : K))))) ^ m)) :
  P = Finset.sum (Finset.range (n + 1)) (fun i =>
    Polynomial.C (((-1 : K) ^ i) * (((r.factorial : K) / a r) ^ i) *
      (((n.factorial : K) * (i.factorial : K)) / (((n + r * i).factorial : K)))) *
    ((ascPochhammer K i) * Polynomial.C (((i.factorial : K))⁻¹)) *
    (((descPochhammer K (n - i)).comp (Polynomial.X + Polynomial.C (n : K))) *
      Polynomial.C ((((n - i).factorial : K))⁻¹)) *
    Polynomial.C (MetaMathlibExt.partialBellPolynomial (n + r * i) i
      (fun j => if r ≤ j then a j else 0))) := by
  set g : PowerSeries K := PowerSeries.mk (fun k => (r.factorial : K) * a (r + k) /
    (a r * ((r + k).factorial : K))) with hgdef
  have hg1 : PowerSeries.constantCoeff g = 1 := howard_g_coeff_one r a har
  set ghat : PowerSeries K := PowerSeries.inv g with hghatdef
  have hg0 : PowerSeries.constantCoeff g ≠ 0 := by rw [hg1]; exact one_ne_zero
  have hgg1 : ghat * g = 1 := PowerSeries.inv_mul_cancel _ hg0
  have hgg2 : g * ghat = 1 := PowerSeries.mul_inv_cancel _ hg0
  set R : Polynomial K := Finset.sum (Finset.range (n + 1)) (fun i =>
    Polynomial.C (((-1 : K) ^ i) * (((r.factorial : K) / a r) ^ i) *
      (((n.factorial : K) * (i.factorial : K)) / (((n + r * i).factorial : K)))) *
    ((ascPochhammer K i) * Polynomial.C (((i.factorial : K))⁻¹)) *
    (((descPochhammer K (n - i)).comp (Polynomial.X + Polynomial.C (n : K))) *
      Polynomial.C ((((n - i).factorial : K))⁻¹)) *
    Polynomial.C (MetaMathlibExt.partialBellPolynomial (n + r * i) i
      (fun j => if r ≤ j then a j else 0))) with hRdef
  have hRdeg : R.natDegree ≤ n := by
      rw [hRdef]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      have hiN : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hA : ((ascPochhammer K i) * Polynomial.C (((i.factorial : K))⁻¹) : Polynomial
          K).natDegree ≤ i :=
        asc_mul_C_degree i _
      have hD : ((((descPochhammer K (n - i)).comp (Polynomial.X + Polynomial.C (n : K))) *
          Polynomial.C ((((n - i).factorial : K))⁻¹) : Polynomial K)).natDegree ≤ n - i := by
        calc ((((descPochhammer K (n - i)).comp (Polynomial.X + Polynomial.C (n : K))) *
            Polynomial.C ((((n - i).factorial : K))⁻¹) : Polynomial K)).natDegree
            ≤ ((descPochhammer K (n - i)).comp
              (Polynomial.X + Polynomial.C (n : K))).natDegree :=
              Polynomial.natDegree_mul_C_le _ _
          _ = n - i := by
              rw [Polynomial.natDegree_comp, descPochhammer_natDegree,
                Polynomial.natDegree_X_add_C]
              ring
      have hE : (Polynomial.C (MetaMathlibExt.partialBellPolynomial (n + r * i) i
          (fun j => if r ≤ j then a j else 0)) : Polynomial K).natDegree ≤ 0 := by
        rw [Polynomial.natDegree_C]
      have hle := natDegree_C_mul4_le
        (((-1 : K) ^ i) * (((r.factorial : K) / a r) ^ i) *
          (((n.factorial : K) * (i.factorial : K)) / (((n + r * i).factorial : K))))
        _ _ _ i (n - i) 0 hA hD hE
      have heq : i + (n - i) + 0 = n := by omega
      rw [heq] at hle
      exact hle
  have hRneg : ∀ j : ℕ, j ≤ n →
        Polynomial.eval (-(j : K)) R
        = (n.factorial : K) * PowerSeries.coeff n (g ^ j) := by
      intro j hj
      rw [hRdef, Polynomial.eval_finsetSum]
      have hmem : j ∈ Finset.range (n + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
      refine (Finset.sum_eq_single j ?hvan ?hmem0).trans ?hcompute
      · intro i hi hne
        by_cases hij : j < i
        · have hdesc0 : (((j.descFactorial i : ℕ)) : K) = 0 := by
            have hNat : j.descFactorial i = 0 :=
              Nat.descFactorial_eq_zero_iff_lt.mpr hij
            rw [hNat, Nat.cast_zero]
          have hasc0 : Polynomial.eval (-(j : K)) (ascPochhammer K i) = 0 := by
            rw [asc_at_neg, hdesc0, mul_zero]
          simp only [Polynomial.eval_mul, Polynomial.eval_C, hasc0, mul_zero, zero_mul]
        · have hiN : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          have hlt : n - j < n - i := by omega
          have hNat : (n - j).descFactorial (n - i) = 0 :=
            Nat.descFactorial_eq_zero_iff_lt.mpr hlt
          have hdesc0 : Polynomial.eval (-(j : K))
              ((descPochhammer K (n - i)).comp (Polynomial.X + Polynomial.C (n : K))) = 0 := by
            rw [desc_comp_at_neg n i j hj, hNat, Nat.cast_zero]
          simp only [Polynomial.eval_mul, Polynomial.eval_C, hdesc0, mul_zero, zero_mul]
      · intro hcon
        exact absurd hmem hcon
      · have hascJ : Polynomial.eval (-(j : K)) (ascPochhammer K j)
            = (-1 : K) ^ j * ((j.factorial : K)) := by
          rw [asc_at_neg, Nat.descFactorial_self]
        have hdescJ : Polynomial.eval (-(j : K))
            ((descPochhammer K (n - j)).comp (Polynomial.X + Polynomial.C (n : K)))
            = (((n - j).factorial : K)) := by
          rw [desc_comp_at_neg n j j hj, Nat.descFactorial_self]
        have hjF : ((j.factorial : K)) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have hnjF : (((n - j).factorial : K)) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have hNF : (((n + r * j).factorial : K)) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have hnF : ((n.factorial : K)) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have hrF : ((r.factorial : K)) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have hneg : ((-1 : K) ^ j) * ((-1 : K) ^ j) = 1 := by
          rw [← pow_add]
          exact Even.neg_one_pow ⟨j, rfl⟩
        have hneg2 : (((-1 : K) ^ j)) ^ 2 = 1 := by
          rw [pow_two]
          exact hneg
        have hneg3 : (-1 : K) ^ (j + j) = 1 :=
          Even.neg_one_pow ⟨j, rfl⟩
        simp only [Polynomial.eval_mul, Polynomial.eval_C]
        rw [hascJ, hdescJ]
        rw [hgdef]
        rw [howard_Bell_eq r n j a hr har]
        field_simp
        simp only [hneg2]
        rw [one_mul]
        have hAB : (((r.factorial : K) / a r) ^ j) * (((a r) / ((r.factorial : K))) ^ j) = 1 := by
          rw [← mul_pow, div_mul_div_comm, mul_comm (a r) ((r.factorial : K)), div_self
              (mul_ne_zero hrF har), one_pow]
        rw [hAB, one_mul]
  set u : PowerSeries K := g - 1 with hudef
  set d : ℕ → K := fun j => PowerSeries.coeff n (ghat ^ n * u ^ j) with hddef
  set Q : Polynomial K := howardQGen n d with hQdef
  have hQdeg : Q.natDegree ≤ n := by
    rw [hQdef]
    exact howardQ_degree n d
  have hQeval : ∀ k : ℕ, Polynomial.eval ((k : K) - (n : K)) Q
      = (n.factorial : K) * PowerSeries.coeff n (ghat ^ n * g ^ k) := by
    intro k
    rw [hQdef, howardQ_eval n k d, coeff_ghat_mul_g n k g ghat hg1]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  set Qt : Polynomial K := Q.comp (-Polynomial.X) with hQtdef
  have hQtdeg : Qt.natDegree ≤ n := by
    have hneg : (-Polynomial.X : Polynomial K).natDegree = 1 := by
      rw [Polynomial.natDegree_neg, Polynomial.natDegree_X]
    rw [hQtdef, Polynomial.natDegree_comp, hneg, mul_one]
    exact hQdeg
  have hpow1 : ∀ m : ℕ, m ≤ n → ghat ^ n * g ^ (n - m) = ghat ^ m := by
    intro m hm
    have hn : n = (n - m) + m := (Nat.sub_add_cancel hm).symm
    have e1 : ghat ^ n * g ^ (n - m) = ghat ^ m * ((ghat * g) ^ (n - m)) := by
      nth_rewrite 1 [hn]
      rw [pow_add, mul_pow]
      ring
    rw [e1, hgg1, one_pow, mul_one]
  have hPeq : ∀ m : ℕ, m ≤ n →
      Polynomial.eval (m : K) P = Polynomial.eval (m : K) Qt := by
    intro m hm
    have hevX : Polynomial.eval (m : K) (-Polynomial.X) = -((m : K)) := by
      rw [Polynomial.eval_neg, Polynomial.eval_X]
    have hQm : Polynomial.eval (m : K) Qt
        = (n.factorial : K) * PowerSeries.coeff n (ghat ^ m) := by
      rw [hQtdef, Polynomial.eval_comp, hevX]
      have hpt : (-((m : K))) = ((((n - m : ℕ)) : K) - (n : K)) := by
        rw [Nat.cast_sub hm]
        ring
      rw [hpt, hQeval (n - m), hpow1 m hm]
    rw [hQm]
    exact heval m hm
  have hpow2 : ∀ j : ℕ, ghat ^ n * g ^ (n + j) = g ^ j := by
    intro j
    have e2 : ghat ^ n * g ^ (n + j) = g ^ j * ((ghat * g) ^ n) := by
      rw [pow_add, mul_pow]
      ring
    rw [e2, hgg1, one_pow, mul_one]
  have hReq : ∀ j : ℕ, j ≤ n →
      Polynomial.eval (-(j : K)) R = Polynomial.eval (-(j : K)) Qt := by
    intro j hj
    have hevX : Polynomial.eval (-(j : K)) (-Polynomial.X) = ((j : K)) := by
      rw [Polynomial.eval_neg, Polynomial.eval_X, neg_neg]
    have hQj : Polynomial.eval (-(j : K)) Qt
        = (n.factorial : K) * PowerSeries.coeff n (g ^ j) := by
      rw [hQtdef, Polynomial.eval_comp, hevX]
      have hpt2 : ((j : K)) = ((((n + j : ℕ)) : K) - (n : K)) := by
        rw [Nat.cast_add]
        abel
      rw [hpt2, hQeval (n + j), hpow2 j]
    rw [hQj]
    exact hRneg j hj
  have hPQt : P = Qt := by
    classical
    set S1 : Finset K := Finset.image (fun m : ℕ => ((m : ℕ) : K)) (Finset.range (n + 1)) with
        hS1def
    have hinj1 : Function.Injective (fun m : ℕ => ((m : ℕ) : K)) := Nat.cast_injective
    have hcard1 : S1.card = n + 1 := by
      rw [hS1def, Finset.card_image_of_injective _ hinj1, Finset.card_range]
    apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq S1
    · rw [hcard1]
      have hdegPQ : (P - Qt).natDegree ≤ n := by
        calc (P - Qt).natDegree ≤ max P.natDegree Qt.natDegree := Polynomial.natDegree_sub_le _ _
          _ ≤ n := max_le hdeg hQtdeg
      calc (P - Qt).degree ≤ (((P - Qt).natDegree : ℕ) : WithBot ℕ) :=
            Polynomial.degree_le_of_natDegree_le (le_refl _)
        _ ≤ (((n : ℕ)) : WithBot ℕ) := WithBot.coe_le_coe.mpr hdegPQ
        _ < (((n + 1 : ℕ)) : WithBot ℕ) := WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n)
    · intro x hx
      rw [hS1def] at hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      have hmN : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      exact hPeq m hmN
  have hRQt : R = Qt := by
    classical
    set S2 : Finset K := Finset.image (fun j : ℕ => (-(((j : ℕ)) : K))) (Finset.range (n + 1)) with
        hS2def
    have hinj2 : Function.Injective (fun j : ℕ => (-(((j : ℕ)) : K))) := by
      intro a b hab
      simp only at hab
      have h1 : (((a : ℕ)) : K) = (((b : ℕ)) : K) := neg_inj.mp hab
      exact Nat.cast_injective h1
    have hcard2 : S2.card = n + 1 := by
      rw [hS2def, Finset.card_image_of_injective _ hinj2, Finset.card_range]
    apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq S2
    · rw [hcard2]
      have hdegRQ : (R - Qt).natDegree ≤ n := by
        calc (R - Qt).natDegree ≤ max R.natDegree Qt.natDegree := Polynomial.natDegree_sub_le _ _
          _ ≤ n := max_le hRdeg hQtdeg
      calc (R - Qt).degree ≤ (((R - Qt).natDegree : ℕ) : WithBot ℕ) :=
            Polynomial.degree_le_of_natDegree_le (le_refl _)
        _ ≤ (((n : ℕ)) : WithBot ℕ) := WithBot.coe_le_coe.mpr hdegRQ
        _ < (((n + 1 : ℕ)) : WithBot ℕ) := WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n)
    · intro x hx
      rw [hS2def] at hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      have hmN : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      exact hReq m hmN
  rw [hPQt, hRQt]

end MetaMathlibExt
