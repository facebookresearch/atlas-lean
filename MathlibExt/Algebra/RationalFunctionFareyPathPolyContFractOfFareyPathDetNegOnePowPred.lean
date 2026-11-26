/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.ContinuedFractions.RationalFunctionFareyPath
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.LinearCombination

/-!
# Farey paths of polynomials with alternating determinants starting at 1

We prove `MetaMathlibExt.polyContFract_of_farey_path_det_neg_one_pow_pred`, the convergent
formula for Farey paths with increasing denominator degrees and adjacent determinants
$(-1)^{i-1}$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Corollary 1.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

variable {F : Type*} [Field F]

/-- **Farey paths of polynomials with alternating determinants starting at 1.** Let $F$ be a
field, let $n \in \mathbb{N}$, and let $u_i, v_i \in F[X]$ for $i \ge 0$. Suppose that $v_0 = 1$
and that for $1 \le i \le n$ we have $\deg v_{i-1} < \deg v_i$ and
$u_i v_{i-1} - u_{i-1} v_i = (-1)^{i-1}$. Let $a_0, a_1, \ldots \in F[X]$ satisfy $a_0 = u_0$,
$a_1 = v_1$ and $a_i = (-1)^i (u_i v_{i-2} - u_{i-2} v_i)$ for $2 \le i \le n$. Then $a_i$ is
nonconstant for $1 \le i \le n$, and for every $i \le n$ the numerator $A_i$ and denominator
$B_i$ of the $i$th convergent of the continued fraction $[a_0; a_1, \ldots, a_n]$ over $F(X)$
are $A_i = u_i$ and $B_i = v_i$.

The paper presents the corollaries for $\mathbb{F}_2$ and $\mathbb{F}_3$; the statement holds
verbatim over any field.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Corollary 1. -/
public theorem polyContFract_of_farey_path_det_neg_one_pow_pred
    (u v : ℕ → F[X]) (n : ℕ) (hv0 : v 0 = 1)
    (hdeg : ∀ i, 1 ≤ i → i ≤ n → (v (i - 1)).degree < (v i).degree)
    (hdet : ∀ i, 1 ≤ i → i ≤ n → u i * v (i - 1) - u (i - 1) * v i = C ((-1) ^ (i - 1)))
    (a : ℕ → F[X]) (ha0 : a 0 = u 0) (ha1 : a 1 = v 1)
    (ha : ∀ i, 2 ≤ i → i ≤ n → a i = C ((-1) ^ i) * (u i * v (i - 2) - u (i - 2) * v i)) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) ∧
      ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (u i) ∧
        (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (v i) := by
  let cross (i : ℕ) : F[X] := u (i + 2) * v i - u i * v (i + 2)
  have hquot (i : ℕ) (hi : i + 2 ≤ n) : a (i + 2) = C ((-1) ^ (i + 2)) * cross i :=
    ha (i + 2) (by omega) hi
  -- Adjacent determinants of opposite signs express the next pair through the preceding two.
  have hstep (i : ℕ) (hi : i + 2 ≤ n) :
      cross i * u (i + 1) = C ((-1 : F) ^ i) * (u (i + 2) - u i) ∧
      cross i * v (i + 1) = C ((-1 : F) ^ i) * (v (i + 2) - v i) := by
    have hprev : u (i + 1) * v i - u i * v (i + 1) = C ((-1 : F) ^ i) :=
      hdet (i + 1) (by omega) (by omega)
    have hpow : (-1 : F) ^ (i + 1) = -(-1 : F) ^ i := by rw [pow_succ]; ring
    have hcurr : u (i + 2) * v (i + 1) - u (i + 1) * v (i + 2) = C ((-1 : F) ^ (i + 1)) :=
      hdet (i + 2) (by omega) hi
    rw [hpow, map_neg] at hcurr
    dsimp only [cross]
    constructor
    · linear_combination u (i + 2) * hprev + u i * hcurr
    · linear_combination v (i + 2) * hprev + v i * hcurr
  have hneg2 (i : ℕ) : (-1 : F) ^ (i + 2) = (-1 : F) ^ i := by simp [pow_add, pow_two]
  have hsq (i : ℕ) : C ((-1 : F) ^ i) * C ((-1 : F) ^ i) = 1 := by
    rw [← map_mul]
    have h1 : (-1 : F) ^ i * (-1 : F) ^ i = 1 := by
      rw [← pow_add, show i + i = 2 * i by ring, pow_mul]
      simp only [pow_two, neg_mul_neg, mul_one, one_pow]
    rw [h1, map_one]
  have hrec (i : ℕ) (hi : i + 2 ≤ n) {p q r : F[X]}
      (h : cross i * q = C ((-1 : F) ^ i) * (r - p)) :
      a (i + 2) * q + p = r := by
    rw [hquot i hi, hneg2 i]
    linear_combination C ((-1 : F) ^ i) * h + (r - p) * hsq i
  refine ⟨?_, ?_⟩
  · intro i hi hin
    obtain _ | _ | i := i
    · omega
    · simpa [natDegree_pos_iff_degree_pos, hv0, ha1] using hdeg 1 hi hin
    have hprev : (v i).degree < (v (i + 1)).degree := hdeg (i + 1) (by omega) (by omega)
    have hcurr : (v (i + 1)).degree < (v (i + 2)).degree := hdeg (i + 2) hi hin
    have hprod : (cross i * v (i + 1)).natDegree = (v (i + 2)).natDegree := by
      rw [(hstep i hin).2, natDegree_C_mul (by simp), sub_eq_add_neg,
        natDegree_add_eq_left_of_degree_lt (by rw [degree_neg]; exact hprev.trans hcurr)]
    have hlt := natDegree_lt_natDegree (ne_zero_of_degree_gt hprev) hcurr
    have hle : (cross i * v (i + 1)).natDegree ≤ (cross i).natDegree + (v (i + 1)).natDegree :=
      natDegree_mul_le
    rw [hquot i hin, natDegree_C_mul (by simp)]
    omega
  · intro i
    induction i using Nat.twoStepInduction with
    | zero => simp [polyContFract_h, ha0, hv0]
    | one =>
      intro hi
      have hu1 : u 1 = v 1 * u 0 + 1 := by
        have h : u 1 * v 0 - u 0 * v 1 = 1 := by
          simpa using hdet 1 le_rfl hi
        rw [hv0, mul_one] at h
        linear_combination h
      have hn : 0 < n := by omega
      simp [polyContFract_nums_one a hn, polyContFract_dens_one a hn, ha0, ha1, hu1]
    | more i ih₀ ih₁ =>
      intro hi
      obtain ⟨hu₀, hv₀⟩ := ih₀ (by omega)
      obtain ⟨hu₁, hv₁⟩ := ih₁ (by omega)
      have hs : (polyContFract a n).s.get? (i + 1) =
          some ⟨1, algebraMap F[X] (RatFunc F) (a (i + 2))⟩ := by
        simp [polyContFract_s_get?, show i + 1 < n by omega]
      obtain ⟨hu, hv⟩ := hstep i hi
      constructor
      · rw [GenContFract.nums_recurrence hs hu₀ hu₁]
        simpa only [map_add, map_mul, one_mul] using
          congrArg (algebraMap F[X] (RatFunc F)) (hrec i hi hu)
      · rw [GenContFract.dens_recurrence hs hv₀ hv₁]
        simpa only [map_add, map_mul, one_mul] using
          congrArg (algebraMap F[X] (RatFunc F)) (hrec i hi hv)

end

end MetaMathlibExt
