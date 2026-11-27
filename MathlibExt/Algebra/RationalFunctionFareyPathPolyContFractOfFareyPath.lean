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
# Continued fraction along a Farey path of polynomials

We prove `MetaMathlibExt.polyContFract_of_farey_path`. Let `u v : ℕ → F[X]` and
`c : ℕ → F` with `v 0 = 1` and, for `1 ≤ i ≤ n`, `c i ≠ 0`, `degree (v (i - 1)) < degree (v i)`
and `u i * v (i - 1) - u (i - 1) * v i = C (c i)`, so adjacent determinants are nonzero
constants. Let `a : ℕ → F[X]` satisfy the prescribed formulas for `a 0`, `a 1`, `a 2` and for
`a i` with `3 ≤ i ≤ n`. Then `a i` is nonconstant for `1 ≤ i ≤ n` (`a 0 = u 0` may be
constant), and for every `i ≤ n` the `i`th numerator and denominator of `polyContFract a n`
are the images in `RatFunc F` of `C (t i) * u i` and `C (t i) * v i`, where `t i` is the sign
(`1` if `i % 4` is `0` or `1`, else `-1`) times `∏ j ∈ Icc 1 i, c j ^ (-1) ^ (i - j + 1)`;
hence the `i`th convergent is `u i / v i`. The proof uses a private auxiliary alternating
product of the `c j`.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 6.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

variable {F : Type*} [Field F]

/-- The alternating product `∏ j ∈ Icc 1 i, c j ^ (-1) ^ (i - j + 1)`. -/
private def fareyProd (c : ℕ → F) (i : ℕ) : F :=
  ∏ j ∈ Finset.Icc 1 i, c j ^ ((-1 : ℤ) ^ (i - j + 1))

/-- `(-1 : ℤ) ^ (k + 1) = -(-1) ^ k`. -/
private theorem neg_one_zpow_succ (k : ℕ) : (-1 : ℤ) ^ (k + 1) = -((-1 : ℤ) ^ k) := by
  rw [pow_succ]
  ring

/-- `(-1 : ℤ) ^ (k + 2) = (-1) ^ k`. -/
private theorem neg_one_zpow_add_two (k : ℕ) : (-1 : ℤ) ^ (k + 2) = (-1 : ℤ) ^ k := by
  rw [pow_add]
  norm_num

/-- `fareyProd c 0 = 1`. -/
private theorem fareyProd_zero (c : ℕ → F) : fareyProd c 0 = 1 := by
  simp [fareyProd]

/-- `fareyProd c (i + 1) = (c (i + 1))⁻¹ * (fareyProd c i)⁻¹`. -/
private theorem fareyProd_succ (c : ℕ → F) (i : ℕ) :
    fareyProd c (i + 1) = (c (i + 1))⁻¹ * (fareyProd c i)⁻¹ := by
  unfold fareyProd
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ i + 1)]
  have hexp : ∀ j ∈ Finset.Icc 1 i, ((-1 : ℤ) ^ (i + 1 - j + 1)) = -(((-1 : ℤ) ^ (i - j + 1))) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hsub : i + 1 - j + 1 = (i - j + 1) + 1 := by omega
    rw [hsub, neg_one_zpow_succ]
  have hterm : ∀ j ∈ Finset.Icc 1 i,
      c j ^ ((-1 : ℤ) ^ (i + 1 - j + 1)) = (c j ^ ((-1 : ℤ) ^ (i - j + 1)))⁻¹ := by
    intro j hj
    rw [hexp j hj, zpow_neg]
  rw [Finset.prod_congr rfl hterm, Finset.prod_inv_distrib]
  have hlast : ((-1 : ℤ) ^ (i + 1 - (i + 1) + 1)) = -1 := by
    simp
  rw [hlast]
  simp [zpow_neg, mul_comm]

/-- `fareyProd c (i + 2) = (c (i + 2))⁻¹ * c (i + 1) * fareyProd c i`. -/
private theorem fareyProd_two_step (c : ℕ → F) (i : ℕ) :
    fareyProd c (i + 2) = (c (i + 2))⁻¹ * c (i + 1) * fareyProd c i := by
  rw [fareyProd_succ, fareyProd_succ, mul_inv_rev, inv_inv, inv_inv,
    mul_comm (fareyProd c i), ← mul_assoc]

/-- `fareyProd c i ≠ 0` for `i ≤ n` when `c j ≠ 0` for `1 ≤ j ≤ n`. -/
private theorem fareyProd_ne_zero (c : ℕ → F) (n : ℕ)
    (hc : ∀ i, 1 ≤ i → i ≤ n → c i ≠ 0) (i : ℕ) (hi : i ≤ n) :
    fareyProd c i ≠ 0 := by
  unfold fareyProd
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  simp only [Finset.mem_Icc] at hj
  exact zpow_ne_zero _ (hc j hj.1 (by omega))

/-- For `k ≤ n` and `c j ≠ 0` for `1 ≤ j ≤ n`,
`∏ j ∈ Icc 1 k, c j ^ (2 * (-1) ^ (k + 2 - j + 1)) = fareyProd c k ^ 2`. -/
private theorem fareyProd_sq (c : ℕ → F) (n : ℕ)
    (hc : ∀ i, 1 ≤ i → i ≤ n → c i ≠ 0) (k : ℕ) (hk : k ≤ n) :
    (∏ j ∈ Finset.Icc 1 k, c j ^ (2 * (-1 : ℤ) ^ (k + 2 - j + 1))) =
      (fareyProd c k) ^ 2 := by
  unfold fareyProd
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have hsub : k + 2 - j + 1 = (k - j + 1) + 2 := by omega
  rw [hsub, neg_one_zpow_add_two]
  have hcj : c j ≠ 0 := hc j hj.1 (by omega)
  have hexp : 2 * (-1 : ℤ) ^ (k - j + 1) =
      (-1 : ℤ) ^ (k - j + 1) + (-1 : ℤ) ^ (k - j + 1) := by
    ring
  rw [hexp, zpow_add₀ hcj, pow_two]

/-- **Continued fraction along a Farey path of polynomials.** Let $F$ be a field, let
$n \in \mathbb N$, let $u_i, v_i \in F[X]$ for $i \ge 0$, and let $c_i \in F$ for $i \ge 1$.
Suppose that $v_0 = 1$ and that for $1 \le i \le n$ we have $c_i \ne 0$,
$\deg v_{i-1} < \deg v_i$ and $u_i v_{i-1} - u_{i-1} v_i = c_i$. Let $a_0, a_1, \ldots \in F[X]$
satisfy $a_0 = u_0$, $a_1 = c_1^{-1} v_1$, $a_2 = -c_2^{-1} c_1 (u_2 v_0 - u_0 v_2)$ and, for
$3 \le i \le n$,
$$a_i = (-1)^{i+1}c_i^{-1}c_{i-1}(u_i v_{i-2} - u_{i-2} v_i)\prod_{j=1}^{i-2} c_j^{2(-1)^{i-j+1}}.$$
Then $a_i$ is nonconstant for $1 \le i \le n$. Moreover, for every $i \le n$ let
$t_i = \varepsilon_i \prod_{j=1}^{i} c_j^{(-1)^{i-j+1}}$, where $\varepsilon_i = 1$ if
$i \equiv 0, 1 \pmod 4$ and $\varepsilon_i = -1$ if $i \equiv 2, 3 \pmod 4$. Then the numerator
$A_i$ and the denominator $B_i$ of the $i$th convergent of the continued fraction
$[a_0; a_1, \ldots, a_n]$ over $F(X)$ are $A_i = t_i u_i$ and $B_i = t_i v_i$, and this
convergent equals $u_i / v_i$.

The paper's coprimality hypothesis $(u_i, v_i) = 1$ is omitted: it follows from the determinant
condition.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 6. -/
public theorem polyContFract_of_farey_path (u v : ℕ → F[X]) (c : ℕ → F) (n : ℕ)
    (hv0 : v 0 = 1) (hc : ∀ i, 1 ≤ i → i ≤ n → c i ≠ 0)
    (hdeg : ∀ i, 1 ≤ i → i ≤ n → (v (i - 1)).degree < (v i).degree)
    (hdet : ∀ i, 1 ≤ i → i ≤ n → u i * v (i - 1) - u (i - 1) * v i = C (c i))
    (a : ℕ → F[X]) (ha0 : a 0 = u 0) (ha1 : a 1 = C (c 1)⁻¹ * v 1)
    (ha2 : a 2 = -C ((c 2)⁻¹ * c 1) * (u 2 * v 0 - u 0 * v 2))
    (ha : ∀ i, 3 ≤ i → i ≤ n →
      a i = C ((-1) ^ (i + 1) * (c i)⁻¹ * c (i - 1) *
        ∏ j ∈ Finset.Icc 1 (i - 2), c j ^ (2 * (-1 : ℤ) ^ (i - j + 1))) *
        (u i * v (i - 2) - u (i - 2) * v i)) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) ∧
      ∀ i ≤ n, ∃ t : F,
        t = (if i % 4 = 0 ∨ i % 4 = 1 then 1 else -1) *
          ∏ j ∈ Finset.Icc 1 i, c j ^ ((-1 : ℤ) ^ (i - j + 1)) ∧
        (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (C t * u i) ∧
        (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (C t * v i) ∧
        (polyContFract a n).convs i =
          algebraMap F[X] (RatFunc F) (u i) / algebraMap F[X] (RatFunc F) (v i) := by
  let sign (i : ℕ) : F := if i % 4 = 0 ∨ i % 4 = 1 then 1 else -1
  let cross (i : ℕ) : F[X] := u (i + 2) * v i - u i * v (i + 2)
  have hquot (i : ℕ) (hi : i + 2 ≤ n) :
      a (i + 2) = C ((-1) ^ (i + 3) * (c (i + 2))⁻¹ * c (i + 1) * (fareyProd c i) ^ 2) *
        cross i := by
    by_cases hi0 : i = 0
    · subst hi0
      rw [ha2]
      have hpow : (-1 : F) ^ (0 + 3) = -1 := by norm_num
      have hP : fareyProd c 0 = 1 := fareyProd_zero c
      have harg : (-1 : F) ^ (0 + 3) * (c (0 + 2))⁻¹ * c (0 + 1) * (fareyProd c 0) ^ 2
          = -((c 2)⁻¹ * c 1) := by
        rw [hP, hpow]
        ring
      rw [harg, map_neg]
    · have hi3 : 3 ≤ i + 2 := by omega
      have h := ha (i + 2) hi3 hi
      have hsub1 : i + 2 - 1 = i + 1 := by omega
      have hsub2 : i + 2 - 2 = i := by omega
      rw [hsub1, hsub2] at h
      have hQ := fareyProd_sq c n hc i (by omega)
      rw [hQ] at h
      have hexp : i + 2 + 1 = i + 3 := by omega
      rw [hexp] at h
      exact h
  have hstep (i : ℕ) (hi : i + 2 ≤ n) :
      C (c (i + 1)) * u (i + 2) + C (c (i + 2)) * u i = cross i * u (i + 1) ∧
      C (c (i + 1)) * v (i + 2) + C (c (i + 2)) * v i = cross i * v (i + 1) := by
    have hprev : u (i + 1) * v i - u i * v (i + 1) = C (c (i + 1)) :=
      hdet (i + 1) (by omega) (by omega)
    have hcurr : u (i + 2) * v (i + 1) - u (i + 1) * v (i + 2) = C (c (i + 2)) :=
      hdet (i + 2) (by omega) hi
    dsimp only [cross]
    constructor
    · linear_combination -u (i + 2) * hprev - u i * hcurr
    · linear_combination -v (i + 2) * hprev - v i * hcurr
  have hsign (i : ℕ) :
      sign (i + 2) = (-1) ^ (i + 3) * sign (i + 1) ∧ sign i = -sign (i + 2) := by
    simp only [sign, neg_one_pow_eq_ite, Nat.even_iff]
    constructor <;> split_ifs <;> (try simp only [one_mul, neg_one_mul, neg_neg]) <;> omega
  have hfield1 (i : ℕ) (hi : i + 2 ≤ n) :
      ((-1 : F) ^ (i + 3) * (c (i + 2))⁻¹ * c (i + 1) * (fareyProd c i) ^ 2) *
        (sign (i + 1) * fareyProd c (i + 1)) * c (i + 1) =
        sign (i + 2) * fareyProd c (i + 2) := by
    have hc1 : c (i + 1) ≠ 0 := hc (i + 1) (by omega) (by omega)
    have hc2 : c (i + 2) ≠ 0 := hc (i + 2) (by omega) hi
    have hPi : fareyProd c i ≠ 0 := fareyProd_ne_zero c n hc i (by omega)
    have hP1 := fareyProd_succ c i
    have hP2 := fareyProd_two_step c i
    have hs1 := (hsign i).1
    rw [hP1, hP2, hs1]
    field_simp
  have hfield2 (i : ℕ) (hi : i + 2 ≤ n) :
      ((-1 : F) ^ (i + 3) * (c (i + 2))⁻¹ * c (i + 1) * (fareyProd c i) ^ 2) *
        (sign (i + 1) * fareyProd c (i + 1)) * c (i + 2) + sign i * fareyProd c i = 0 := by
    have hc1 : c (i + 1) ≠ 0 := hc (i + 1) (by omega) (by omega)
    have hc2 : c (i + 2) ≠ 0 := hc (i + 2) (by omega) hi
    have hPi : fareyProd c i ≠ 0 := fareyProd_ne_zero c n hc i (by omega)
    have hP1 := fareyProd_succ c i
    have hs1 := (hsign i).1
    have hs2 := (hsign i).2
    rw [hP1, hs2, hs1]
    field_simp
    ring
  have hrec (i : ℕ) (hi : i + 2 ≤ n) {p q r : F[X]}
      (h : C (c (i + 1)) * r + C (c (i + 2)) * p = cross i * q) :
      a (i + 2) * (C (sign (i + 1) * fareyProd c (i + 1)) * q) +
        C (sign i * fareyProd c i) * p =
        C (sign (i + 2) * fareyProd c (i + 2)) * r := by
    have hF1 := hfield1 i hi
    have hF2 := hfield2 i hi
    have hC1 : C (((-1 : F) ^ (i + 3) * (c (i + 2))⁻¹ * c (i + 1) * (fareyProd c i) ^ 2) *
        (sign (i + 1) * fareyProd c (i + 1)) * c (i + 1)) =
        C (sign (i + 2) * fareyProd c (i + 2)) := by rw [hF1]
    have hC2 : C (((-1 : F) ^ (i + 3) * (c (i + 2))⁻¹ * c (i + 1) * (fareyProd c i) ^ 2) *
        (sign (i + 1) * fareyProd c (i + 1)) * c (i + 2)) + C (sign i * fareyProd c i) = 0 := by
      have : C (((-1 : F) ^ (i + 3) * (c (i + 2))⁻¹ * c (i + 1) * (fareyProd c i) ^ 2) *
          (sign (i + 1) * fareyProd c (i + 1)) * c (i + 2) + sign i * fareyProd c i) =
          C (0 : F) := by rw [hF2]
      simpa [C_add] using this
    calc
      a (i + 2) * (C (sign (i + 1) * fareyProd c (i + 1)) * q) +
          C (sign i * fareyProd c i) * p
          = C (((-1 : F) ^ (i + 3) * (c (i + 2))⁻¹ * c (i + 1) * (fareyProd c i) ^ 2) *
            (sign (i + 1) * fareyProd c (i + 1))) * (cross i * q) +
            C (sign i * fareyProd c i) * p := by
            rw [hquot i hi]
            simp [C_mul]
            ring
      _ = C (((-1 : F) ^ (i + 3) * (c (i + 2))⁻¹ * c (i + 1) * (fareyProd c i) ^ 2) *
            (sign (i + 1) * fareyProd c (i + 1))) *
            (C (c (i + 1)) * r + C (c (i + 2)) * p) +
            C (sign i * fareyProd c i) * p := by rw [← h]
      _ = C (((-1 : F) ^ (i + 3) * (c (i + 2))⁻¹ * c (i + 1) * (fareyProd c i) ^ 2) *
            (sign (i + 1) * fareyProd c (i + 1)) * c (i + 1)) * r +
            (C (((-1 : F) ^ (i + 3) * (c (i + 2))⁻¹ * c (i + 1) * (fareyProd c i) ^ 2) *
              (sign (i + 1) * fareyProd c (i + 1)) * c (i + 2)) +
              C (sign i * fareyProd c i)) * p := by
            simp [C_mul]
            ring
      _ = C (sign (i + 2) * fareyProd c (i + 2)) * r := by
            rw [hC1, hC2]
            simp
  have hsign_ne (i : ℕ) : sign i ≠ 0 := by
    simp only [sign]
    split_ifs
    · exact one_ne_zero
    · exact neg_ne_zero.mpr one_ne_zero
  have ht_ne (i : ℕ) (hi : i ≤ n) : sign i * fareyProd c i ≠ 0 :=
    mul_ne_zero (hsign_ne i) (fareyProd_ne_zero c n hc i hi)
  have hconvs (i : ℕ) (t : F) (ht : t ≠ 0)
      (hn : (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (C t * u i))
      (hd : (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (C t * v i)) :
      (polyContFract a n).convs i =
        algebraMap F[X] (RatFunc F) (u i) / algebraMap F[X] (RatFunc F) (v i) := by
    have hCt : (C t : F[X]) ≠ 0 := C_ne_zero.mpr ht
    have hAlg : algebraMap F[X] (RatFunc F) (C t) ≠ 0 :=
      mt (FaithfulSMul.algebraMap_eq_zero_iff _ _).mp hCt
    have hconvs_eq : (polyContFract a n).convs i =
        (polyContFract a n).nums i / (polyContFract a n).dens i := rfl
    rw [hconvs_eq, hn, hd, map_mul, map_mul]
    exact mul_div_mul_left _ _ hAlg
  refine ⟨?_, ?_⟩
  · intro i hi hin
    obtain _ | _ | i := i
    · omega
    · have hc1 : c 1 ≠ 0 := hc 1 hi hin
      have hcinv : (c 1)⁻¹ ≠ 0 := inv_ne_zero hc1
      simpa [natDegree_pos_iff_degree_pos, hv0, ha1, natDegree_C_mul hcinv] using hdeg 1 hi hin
    · have hc1 : c (i + 1) ≠ 0 := hc (i + 1) (by omega) (by omega)
      have hc2 : c (i + 2) ≠ 0 := hc (i + 2) (by omega) hin
      have hPi : fareyProd c i ≠ 0 := fareyProd_ne_zero c n hc i (by omega)
      have hs : (-1 : F) ^ (i + 3) * (c (i + 2))⁻¹ * c (i + 1) * (fareyProd c i) ^ 2 ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
        · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
        · exact inv_ne_zero hc2
        · exact hc1
        · exact pow_ne_zero _ hPi
      have hprev : (v i).degree < (v (i + 1)).degree := hdeg (i + 1) (by omega) (by omega)
      have hcurr : (v (i + 1)).degree < (v (i + 2)).degree := hdeg (i + 2) (by omega) hin
      have hdeg_lt : (C (c (i + 2)) * v i).degree < (C (c (i + 1)) * v (i + 2)).degree := by
        rw [degree_C_mul hc2, degree_C_mul hc1]
        exact hprev.trans hcurr
      have hprod : (cross i * v (i + 1)).natDegree = (v (i + 2)).natDegree := by
        rw [← (hstep i hin).2]
        rw [natDegree_add_eq_left_of_degree_lt hdeg_lt, natDegree_C_mul hc1]
      have hlt := natDegree_lt_natDegree (ne_zero_of_degree_gt hprev) hcurr
      have hle : (cross i * v (i + 1)).natDegree ≤
          (cross i).natDegree + (v (i + 1)).natDegree :=
        natDegree_mul_le
      have hcross : 0 < (cross i).natDegree := by omega
      rw [hquot i hin, natDegree_C_mul hs]
      exact hcross
  · intro i
    induction i using Nat.twoStepInduction with
    | zero =>
      intro _
      have hP0 : fareyProd c 0 = 1 := fareyProd_zero c
      have hsign0 : sign 0 = 1 := by simp [sign]
      refine ⟨sign 0 * fareyProd c 0, by simp [sign, fareyProd], ?_, ?_, ?_⟩
      · simp [polyContFract_h, ha0, hsign0, hP0]
      · simp [hv0, hsign0, hP0]
      · apply hconvs 0 (sign 0 * fareyProd c 0) (ht_ne 0 (Nat.zero_le n))
        · simp [polyContFract_h, ha0, hsign0, hP0]
        · simp [hv0, hsign0, hP0]
    | one =>
      intro hi1
      have hc1 : c 1 ≠ 0 := hc 1 le_rfl hi1
      have hP1 : fareyProd c 1 = (c 1)⁻¹ := by
        have h := fareyProd_succ c 0
        rw [fareyProd_zero] at h
        simpa using h
      have hsign1 : sign 1 = 1 := by simp [sign]
      have ht1 : sign 1 * fareyProd c 1 = (c 1)⁻¹ := by rw [hsign1, hP1, one_mul]
      have h : u 1 * v 0 - u 0 * v 1 = C (c 1) := hdet 1 le_rfl hi1
      rw [hv0, mul_one] at h
      have hu1 : u 1 = u 0 * v 1 + C (c 1) := by linear_combination h
      have hC : C ((c 1)⁻¹ : F) * C (c 1) = 1 := by rw [← C_mul, inv_mul_cancel₀ hc1, C_1]
      have hpoly : C ((c 1)⁻¹) * v 1 * u 0 + 1 = C ((c 1)⁻¹) * u 1 := by
        calc C ((c 1)⁻¹) * v 1 * u 0 + 1
            = C ((c 1)⁻¹) * (u 0 * v 1 + C (c 1)) := by rw [mul_add, hC]; ring
          _ = C ((c 1)⁻¹) * u 1 := by rw [hu1]
      have hn0 : 0 < n := by omega
      refine ⟨sign 1 * fareyProd c 1, by simp [sign, fareyProd], ?_, ?_, ?_⟩
      · rw [polyContFract_nums_one a hn0, ha0, ha1, ht1, hpoly]
      · rw [polyContFract_dens_one a hn0, ha1, ht1]
      · apply hconvs 1 (sign 1 * fareyProd c 1) (ht_ne 1 hi1)
        · rw [polyContFract_nums_one a hn0, ha0, ha1, ht1, hpoly]
        · rw [polyContFract_dens_one a hn0, ha1, ht1]
    | more k ih0 ih1 =>
      intro hi2
      obtain ⟨t0, ht0_eq, hu0, hv0', _⟩ := ih0 (by omega)
      obtain ⟨t1, ht1_eq, hu1, hv1, _⟩ := ih1 (by omega)
      have hs : (polyContFract a n).s.get? (k + 1) =
          some ⟨1, algebraMap F[X] (RatFunc F) (a (k + 2))⟩ := by
        simp [polyContFract_s_get?, show k + 1 < n by omega]
      obtain ⟨hstep_u, hstep_v⟩ := hstep k hi2
      have ht0 : t0 = sign k * fareyProd c k := by
        rw [ht0_eq]
        simp [sign, fareyProd]
      have ht1 : t1 = sign (k + 1) * fareyProd c (k + 1) := by
        rw [ht1_eq]
        simp [sign, fareyProd]
      rw [ht0] at hu0 hv0'
      rw [ht1] at hu1 hv1
      refine ⟨sign (k + 2) * fareyProd c (k + 2), by simp [sign, fareyProd], ?_, ?_, ?_⟩
      · rw [GenContFract.nums_recurrence hs hu0 hu1]
        simpa only [map_add, map_mul, one_mul] using
          congrArg (algebraMap F[X] (RatFunc F)) (hrec k hi2 hstep_u)
      · rw [GenContFract.dens_recurrence hs hv0' hv1]
        simpa only [map_add, map_mul, one_mul] using
          congrArg (algebraMap F[X] (RatFunc F)) (hrec k hi2 hstep_v)
      · apply hconvs (k + 2) (sign (k + 2) * fareyProd c (k + 2)) (ht_ne (k + 2) hi2)
        · rw [GenContFract.nums_recurrence hs hu0 hu1]
          simpa only [map_add, map_mul, one_mul] using
            congrArg (algebraMap F[X] (RatFunc F)) (hrec k hi2 hstep_u)
        · rw [GenContFract.dens_recurrence hs hv0' hv1]
          simpa only [map_add, map_mul, one_mul] using
            congrArg (algebraMap F[X] (RatFunc F)) (hrec k hi2 hstep_v)

end

end MetaMathlibExt
