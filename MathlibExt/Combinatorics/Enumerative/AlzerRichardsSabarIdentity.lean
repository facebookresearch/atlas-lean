/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.LinearAlgebra.Lagrange

/-!
# Sabar's identity for complex arguments

Subtracting the falling factorial from a power gives the polynomial of degree below
the exponent that interpolates the power at consecutive natural numbers. Writing its
interpolation weights as generalized binomial coefficients gives Sabar's identity.
-/

namespace MetaMathlibExt

open Finset Polynomial

namespace pow_sub_descPochhammer_eq_sum_choose

private noncomputable def binomPoly (k : ℕ) : ℂ[X] :=
  C (k.factorial : ℂ)⁻¹ * descPochhammer ℂ k

private lemma eval_binomPoly (k : ℕ) (z : ℂ) : (binomPoly k).eval z = Ring.choose z k := by
  rw [binomPoly, eval_mul, eval_C, Ring.choose_eq_smul, smul_eq_mul,
    descPochhammer_eval_eq_ascPochhammer, descPochhammer_smeval_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval]

private lemma natDegree_binomPoly_le (k : ℕ) : (binomPoly k).natDegree ≤ k := by
  simpa [binomPoly] using natDegree_C_mul_le (k.factorial : ℂ)⁻¹ (descPochhammer ℂ k)

private noncomputable def summand (p k : ℕ) : ℂ[X] :=
  C ((-1 : ℂ) ^ (p - k - 1) * (k : ℂ) ^ p) *
    (binomPoly k * (binomPoly (p - k - 1)).comp (X - C ((k : ℂ) + 1)))

private lemma eval_summand (p k : ℕ) (z : ℂ) :
    (summand p k).eval z = (-1 : ℂ) ^ (p - k - 1) * (k : ℂ) ^ p * Ring.choose z k *
      Ring.choose (z - k - 1) (p - k - 1) := by
  simp [summand, eval_comp, eval_binomPoly, sub_add_eq_sub_sub, mul_assoc]

private lemma natDegree_summand_le {p k : ℕ} (hk : k < p) :
    (summand p k).natDegree ≤ p - 1 := by
  apply (natDegree_C_mul_le ..).trans
  apply natDegree_mul_le.trans
  have hcomp : ((binomPoly (p - k - 1)).comp (X - C ((k : ℂ) + 1))).natDegree ≤ p - k - 1 := by
    apply natDegree_comp_le.trans
    rw [natDegree_X_sub_C, mul_one]
    exact natDegree_binomPoly_le _
  exact (add_le_add (natDegree_binomPoly_le k) hcomp).trans (by omega)

-- At the node j, only the kth summand with k = j contributes.
private lemma sum_eval_node {p j : ℕ} (hj : j < p) :
    ∑ k ∈ range p, (summand p k).eval (j : ℂ) = (j : ℂ) ^ p := by
  rw [sum_eq_single_of_mem j (mem_range.mpr hj)]
  · have hneg (n : ℕ) : Ring.choose (-1 : ℂ) n = (-1) ^ n := by
      simpa [Units.smul_def, zsmul_eq_mul, Int.coe_negOnePow_natCast] using
        Ring.choose_neg' (1 : ℂ) n
    simp only [eval_summand, Ring.choose_natCast, Nat.choose_self, Nat.cast_one, mul_one,
      sub_self, zero_sub, hneg]
    rw [mul_right_comm, ← mul_pow]
    simp
  · intro k _ hkj
    rcases lt_or_gt_of_ne hkj with h | h
    · have hcast : (j : ℂ) - k - 1 = (↑(j - (k + 1)) : ℂ) := by
        rw [Nat.cast_sub h, Nat.cast_succ, sub_add_eq_sub_sub]
      simp [eval_summand, hcast, Ring.choose_natCast, Nat.choose_eq_zero_of_lt
        (show j - (k + 1) < p - k - 1 by omega)]
    · simp [eval_summand, Ring.choose_natCast, Nat.choose_eq_zero_of_lt h]

end pow_sub_descPochhammer_eq_sum_choose

open pow_sub_descPochhammer_eq_sum_choose in
/-- **Sabar's identity for complex arguments.** For a complex number $w$ and a natural number $j$
write $\binom{w}{j} = w(w-1)\cdots(w-j+1)/j!$. For every natural number $p \ge 1$ and every
complex number $z$,
$$
z^p - z(z-1)\cdots(z-p+1) =
\sum_{k=0}^{p-1} (-1)^{p-k-1} k^p \binom{z}{k} \binom{z-k-1}{p-k-1}.
$$

Sabar proved this formula for natural numbers $z = n \ge p$; here it is extended to complex $z$.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 8, Equation (9). -/
public theorem pow_sub_descPochhammer_eq_sum_choose {p : ℕ} (hp : 1 ≤ p) (z : ℂ) :
    z ^ p - (descPochhammer ℂ p).eval z =
      ∑ k ∈ range p, (-1 : ℂ) ^ (p - k - 1) * (k : ℂ) ^ p * Ring.choose z k *
        Ring.choose (z - k - 1) (p - k - 1) := by
  have hpoly : X ^ p - descPochhammer ℂ p = ∑ k ∈ range p, summand p k := by
    apply eq_of_degrees_lt_of_eval_index_eq (v := (Nat.cast : ℕ → ℂ)) (range p)
      Nat.cast_injective.injOn
    · rw [card_range]
      apply degree_le_natDegree.trans_lt
      exact WithBot.coe_lt_coe.mpr <| IsMonicOfDegree.natDegree_sub_lt (by omega : p ≠ 0)
        (isMonicOfDegree_X_pow ℂ p) ⟨descPochhammer_natDegree ℂ p, monic_descPochhammer ℂ p⟩
    · rw [card_range]
      apply degree_le_natDegree.trans_lt
      apply WithBot.coe_lt_coe.mpr
      exact (natDegree_sum_le_of_forall_le _ _ fun k hk =>
        natDegree_summand_le (mem_range.mp hk)).trans_lt (by omega : p - 1 < p)
    · intro j hj
      have hj' := mem_range.mp hj
      simp [eval_finsetSum, descPochhammer_eval_natCast_of_lt (R := ℂ) hj', sum_eval_node hj']
  simpa only [eval_sub, eval_pow, eval_X, eval_finsetSum, eval_summand] using
    congrArg (eval z) hpoly

end MetaMathlibExt
