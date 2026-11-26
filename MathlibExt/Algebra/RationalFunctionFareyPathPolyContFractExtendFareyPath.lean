/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.ContinuedFractions.RationalFunctionFareyPath
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic.LinearCombination

/-!
# Extending a Farey path extends the continued fraction

We prove `MetaMathlibExt.polyContFract_extend_farey_path`: a polynomial adjacent to the last
convergent with larger denominator degree extends the continued fraction by one nonconstant
partial quotient, with the new convergent equal to the adjacent fraction.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 5.
-/

namespace MetaMathlibExt

open Polynomial

private theorem base_zero {F : Type*} [Field F] (a : ℕ → F[X]) (n : ℕ) (A B : ℕ → F[X])
    (hA : ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (A i))
    (hB : ∀ i ≤ n, (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (B i)) :
    A 0 = a 0 ∧ B 0 = 1 := by
  have hinj := RatFunc.algebraMap_injective F
  have hA0 := hA 0 (Nat.zero_le n)
  have hB0 := hB 0 (Nat.zero_le n)
  rw [polyContFract_nums_zero] at hA0
  rw [polyContFract_dens_zero] at hB0
  constructor
  · exact hinj hA0.symm
  · have h : algebraMap F[X] (RatFunc F) (B 0) = algebraMap F[X] (RatFunc F) 1 := by
      simpa using hB0.symm
    exact hinj h

private theorem base_one {F : Type*} [Field F] (a : ℕ → F[X]) {n : ℕ} (hn : 1 ≤ n) (A B : ℕ → F[X])
    (hA : ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (A i))
    (hB : ∀ i ≤ n, (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (B i)) :
    A 1 = a 1 * a 0 + 1 ∧ B 1 = a 1 := by
  have hinj := RatFunc.algebraMap_injective F
  have hA1 := hA 1 hn
  have hB1 := hB 1 hn
  rw [polyContFract_nums_one a (by omega : 0 < n)] at hA1
  rw [polyContFract_dens_one a (by omega : 0 < n)] at hB1
  exact ⟨hinj hA1.symm, hinj hB1.symm⟩

private theorem poly_rec {F : Type*} [Field F] (a : ℕ → F[X]) (n : ℕ) (A B : ℕ → F[X])
    (hA : ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (A i))
    (hB : ∀ i ≤ n, (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (B i))
    (i : ℕ) (hi : i + 2 ≤ n) :
    A (i + 2) = a (i + 2) * A (i + 1) + A i ∧
      B (i + 2) = a (i + 2) * B (i + 1) + B i := by
  have hinj := RatFunc.algebraMap_injective F
  have hs : (polyContFract a n).s.get? (i + 1) =
      some ⟨1, algebraMap F[X] (RatFunc F) (a (i + 2))⟩ := by
    simp [polyContFract_s_get?, show i + 1 < n by omega]
  have hAi := hA i (by omega)
  have hAi1 := hA (i + 1) (by omega)
  have hAi2 := hA (i + 2) hi
  have hBi := hB i (by omega)
  have hBi1 := hB (i + 1) (by omega)
  have hBi2 := hB (i + 2) hi
  have hnums := GenContFract.nums_recurrence (n := i) hs hAi hAi1
  have hdens := GenContFract.dens_recurrence (n := i) hs hBi hBi1
  rw [hAi2] at hnums
  rw [hBi2] at hdens
  constructor
  · have h : algebraMap F[X] (RatFunc F) (A (i + 2)) =
        algebraMap F[X] (RatFunc F) (a (i + 2) * A (i + 1) + A i) := by
      simpa only [map_add, map_mul, one_mul] using hnums
    exact hinj h
  · have h : algebraMap F[X] (RatFunc F) (B (i + 2)) =
        algebraMap F[X] (RatFunc F) (a (i + 2) * B (i + 1) + B i) := by
      simpa only [map_add, map_mul, one_mul] using hdens
    exact hinj h

-- Denominators are nonzero with strictly increasing degrees.
private theorem B_ne_deg {F : Type*} [Field F] (a : ℕ → F[X]) {n : ℕ}
    (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree)
    (A B : ℕ → F[X])
    (hA : ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (A i))
    (hB : ∀ i ≤ n, (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (B i))
    (i : ℕ) (hi : i ≤ n) : B i ≠ 0 ∧ (1 ≤ i → (B (i - 1)).degree < (B i).degree) := by
  induction i using Nat.twoStepInduction with
  | zero =>
    obtain ⟨-, hB0⟩ := base_zero a n A B hA hB
    refine ⟨by rw [hB0]; exact one_ne_zero, fun h => absurd h (by omega)⟩
  | one =>
    have hn : 1 ≤ n := hi
    obtain ⟨-, hB0⟩ := base_zero a n A B hA hB
    obtain ⟨-, hB1⟩ := base_one a hn A B hA hB
    have ha1 : 0 < (a 1).natDegree := ha 1 le_rfl hn
    have hne : B 1 ≠ 0 := by
      rw [hB1]
      intro hcon
      rw [hcon, natDegree_zero] at ha1
      exact lt_irrefl 0 ha1
    refine ⟨hne, fun _ => ?_⟩
    rw [hB0, hB1]
    have hpos : (0 : WithBot ℕ) < (a 1).degree := natDegree_pos_iff_degree_pos.mp ha1
    simpa [degree_one] using hpos
  | more i ih0 ih1 =>
    have hi2 : i + 2 ≤ n := hi
    obtain ⟨hBi_ne, -⟩ := ih0 (by omega)
    obtain ⟨hBi1_ne, hdeg1⟩ := ih1 (by omega)
    have hlt : (B i).degree < (B (i + 1)).degree := hdeg1 (by omega)
    obtain ⟨-, hrec⟩ := poly_rec a n A B hA hB i hi2
    have ha2 : 0 < (a (i + 2)).natDegree := ha (i + 2) (by omega) hi2
    have hapos : (0 : WithBot ℕ) < (a (i + 2)).degree :=
      natDegree_pos_iff_degree_pos.mp ha2
    have hBne_bot : (B (i + 1)).degree ≠ ⊥ := degree_eq_bot.not.mpr hBi1_ne
    have hmul : (B (i + 1)).degree < ((a (i + 2)) * B (i + 1)).degree := by
      rw [degree_mul]
      have h := WithBot.add_lt_add_right hBne_bot hapos
      simpa [zero_add] using h
    have hsum : ((B i).degree < ((a (i + 2)) * B (i + 1)).degree) :=
      hlt.trans hmul
    have hdeg_eq : (a (i + 2) * B (i + 1) + B i).degree =
        ((a (i + 2)) * B (i + 1)).degree :=
      degree_add_eq_left_of_degree_lt hsum
    have hB2_ne : B (i + 2) ≠ 0 := by
      rw [hrec]
      intro hcon
      rw [hcon, degree_zero] at hdeg_eq
      rw [← hdeg_eq] at hmul
      exact not_lt_bot hmul
    refine ⟨hB2_ne, fun _ => ?_⟩
    have hsub : i + 2 - 1 = i + 1 := by omega
    rw [hsub, hrec, hdeg_eq]
    exact hmul

-- Consecutive convergents have unit determinant.
private theorem det_unit {F : Type*} [Field F] (a : ℕ → F[X]) {n : ℕ}
    (A B : ℕ → F[X])
    (hA : ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (A i))
    (hB : ∀ i ≤ n, (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (B i))
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    IsUnit (A i * B (i - 1) - A (i - 1) * B i) := by
  have base : ∀ h : 1 ≤ n, IsUnit (A 1 * B (1 - 1) - A (1 - 1) * B 1) := by
    intro h
    obtain ⟨hA0, hB0⟩ := base_zero a n A B hA hB
    obtain ⟨hA1, hB1⟩ := base_one a h A B hA hB
    have hdet : A 1 * B (1 - 1) - A (1 - 1) * B 1 = 1 := by
      simp only [Nat.sub_self] at *
      rw [hA1, hB1, hA0, hB0]
      ring
    rw [hdet]
    exact isUnit_one
  have step : ∀ m : ℕ, ∀ hmn : 1 ≤ m,
      (m ≤ n → IsUnit (A m * B (m - 1) - A (m - 1) * B m)) →
      (m + 1 ≤ n → IsUnit (A (m + 1) * B (m + 1 - 1) - A (m + 1 - 1) * B (m + 1))) := by
    intro m hmn ih hmn1
    have hm_le : m ≤ n := by omega
    have ihu := ih hm_le
    have hsub : m + 1 - 1 = m := by omega
    rw [hsub]
    -- recurrence with (m-1)+2 = m+1
    have hm2 : m - 1 + 2 = m + 1 := by omega
    have hrec := poly_rec a n A B hA hB (m - 1) (by omega)
    rw [hm2] at hrec
    obtain ⟨hArec, hBrec⟩ := hrec
    have hsub2 : m - 1 + 1 = m := by omega
    rw [hsub2] at hArec hBrec
    -- D(m+1) = -D(m)
    have hdet : A (m + 1) * B m - A m * B (m + 1) =
        -(A m * B (m - 1) - A (m - 1) * B m) := by
      rw [hArec, hBrec]
      ring
    rw [hdet]
    exact ihu.neg
  have h := Nat.le_induction
    (motive := fun j _ => j ≤ n → IsUnit (A j * B (j - 1) - A (j - 1) * B j))
    (fun hle => base hle) (fun m hmn ih hle => step m hmn ih hle) i hi1 hin
  exact h

-- A unit linear combination gives coprimality.
private theorem coprime_of_adj {F : Type*} [Field F] (u v P Q : F[X]) (h : IsUnit (u * Q - v * P)) :
    IsCoprime u v := by
  obtain ⟨w, hw⟩ := h.exists_left_inv
  refine ⟨w * Q, w * (-P), ?_⟩
  have hring : (w * Q) * u + (w * (-P)) * v = w * (u * Q - v * P) := by ring
  rw [hring, hw]

private theorem ext_s_get_eq {F : Type*} [Field F] (a : ℕ → F[X]) (n : ℕ) (b : F[X])
    (i : ℕ) (hi : i < n) :
    (polyContFract (Function.update a (n + 1) b) (n + 1)).s.get? i =
      (polyContFract a n).s.get? i := by
  have h1 : i < n + 1 := by omega
  have h2 : Function.update a (n + 1) b (i + 1) = a (i + 1) := by
    apply Function.update_of_ne (show i + 1 ≠ n + 1 by omega)
  simp [polyContFract_s_get?, hi, h1, h2]

private theorem ext_nums_dens_eq {F : Type*} [Field F] (a : ℕ → F[X]) (n : ℕ) (b : F[X])
    (i : ℕ) (hi : i ≤ n) :
    (polyContFract (Function.update a (n + 1) b) (n + 1)).nums i =
      (polyContFract a n).nums i ∧
    (polyContFract (Function.update a (n + 1) b) (n + 1)).dens i =
      (polyContFract a n).dens i := by
  induction i using Nat.twoStepInduction with
  | zero =>
    have h0 : Function.update a (n + 1) b 0 = a 0 :=
      Function.update_of_ne (show 0 ≠ n + 1 by omega) b a
    constructor
    · rw [polyContFract_nums_zero, polyContFract_nums_zero, h0]
    · rw [polyContFract_dens_zero, polyContFract_dens_zero]
  | one =>
    have hn1 : 1 ≤ n := hi
    have h0 : Function.update a (n + 1) b 0 = a 0 :=
      Function.update_of_ne (show 0 ≠ n + 1 by omega) b a
    have h1 : Function.update a (n + 1) b 1 = a 1 :=
      Function.update_of_ne (show 1 ≠ n + 1 by omega) b a
    constructor
    · rw [polyContFract_nums_one _ (by omega : 0 < n + 1),
        polyContFract_nums_one _ (by omega : 0 < n), h0, h1]
    · rw [polyContFract_dens_one _ (by omega : 0 < n + 1),
        polyContFract_dens_one _ (by omega : 0 < n), h1]
  | more i ih0 ih1 =>
    have hi2 : i + 2 ≤ n := hi
    obtain ⟨ihn0, ihd0⟩ := ih0 (by omega)
    obtain ⟨ihn1, ihd1⟩ := ih1 (by omega)
    have hs_orig : (polyContFract a n).s.get? (i + 1) =
        some ⟨1, algebraMap F[X] (RatFunc F) (a (i + 2))⟩ := by
      have h : i + 1 < n := by omega
      simp [polyContFract_s_get?, h]
    have hs_ext : (polyContFract (Function.update a (n + 1) b) (n + 1)).s.get? (i + 1) =
        some ⟨1, algebraMap F[X] (RatFunc F) (a (i + 2))⟩ := by
      rw [ext_s_get_eq a n b (i + 1) (by omega), hs_orig]
    have hnums_ext := GenContFract.nums_recurrence (n := i) hs_ext rfl rfl
    have hnums_orig := GenContFract.nums_recurrence (n := i) hs_orig rfl rfl
    have hdens_ext := GenContFract.dens_recurrence (n := i) hs_ext rfl rfl
    have hdens_orig := GenContFract.dens_recurrence (n := i) hs_orig rfl rfl
    rw [ihn0, ihn1] at hnums_ext
    rw [ihd0, ihd1] at hdens_ext
    exact ⟨hnums_ext.trans hnums_orig.symm, hdens_ext.trans hdens_orig.symm⟩

/-- **Extending a Farey path extends the continued fraction.** Let $F$ be a field, let $n \ge 1$,
and let $a_0, a_1, \dots, a_n \in F[X]$ with $a_i$ nonconstant for $1 \le i \le n$. Let
$A_0, \dots, A_n, B_0, \dots, B_n \in F[X]$ be such that, for every $i \le n$, $A_i$ and $B_i$ are
the numerator and the denominator of the $i$th convergent of the continued fraction
$[a_0, a_1, \dots, a_n]$ over $F(X)$. Let $u, v \in F[X]$ be such that $u B_n - v A_n$ is a unit
of $F[X]$ (a nonzero constant) and $\deg B_n < \deg v$. Then there is a nonconstant polynomial
$b \in F[X]$ such that, in $F(X)$,
$$b = \frac{v A_{n-1} - u B_{n-1}}{u B_n - v A_n},$$
and the $(n+1)$st convergent of the continued fraction $[a_0, a_1, \dots, a_n, b]$ equals $u/v$.

Compared with the paper: the case $n = 0$, which needs $A_{-1} = 1$ and $B_{-1} = 0$, is excluded;
the paper's degree condition on the reduced denominator of $A_n / B_n$ is stated with $B_n$ itself
(the two agree, since $A_n / B_n$ is already in lowest terms); and the hypothesis that $u$ and $v$
are coprime is omitted, since adjacency implies it.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 5. -/
public theorem polyContFract_extend_farey_path {F : Type*} [Field F] (a : ℕ → F[X]) {n : ℕ}
    (hn : 1 ≤ n) (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree)
    (A B : ℕ → F[X])
    (hA : ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (A i))
    (hB : ∀ i ≤ n, (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (B i))
    (u v : F[X]) (hadj : IsUnit (u * B n - v * A n))
    (hdeg : (B n).degree < v.degree) :
    ∃ b : F[X], 0 < b.natDegree ∧
      algebraMap F[X] (RatFunc F) b =
        algebraMap F[X] (RatFunc F) (v * A (n - 1) - u * B (n - 1)) /
          algebraMap F[X] (RatFunc F) (u * B n - v * A n) ∧
      (polyContFract (Function.update a (n + 1) b) (n + 1)).convs (n + 1) =
        algebraMap F[X] (RatFunc F) u / algebraMap F[X] (RatFunc F) v := by
  have hinj := RatFunc.algebraMap_injective F
  obtain ⟨hBn_ne, hmono_fn⟩ := B_ne_deg a ha A B hA hB n le_rfl
  have hmono : (B (n - 1)).degree < (B n).degree := hmono_fn hn
  have hdet_n : IsUnit (A n * B (n - 1) - A (n - 1) * B n) :=
    det_unit a A B hA hB n hn le_rfl
  have hv_ne : v ≠ 0 := ne_zero_of_degree_gt (lt_of_le_of_lt bot_le hdeg)
  obtain ⟨w, hw⟩ := hadj.exists_left_inv
  -- b*d = e where d = u*B n - v*A n, e = v*A(n-1) - u*B(n-1)
  have hb_mul : ((v * A (n - 1) - u * B (n - 1)) * w) * (u * B n - v * A n) =
      v * A (n - 1) - u * B (n - 1) := by
    rw [mul_assoc, hw, mul_one]
  have heq : v * (((v * A (n - 1) - u * B (n - 1)) * w) * A n + A (n - 1)) =
      u * (((v * A (n - 1) - u * B (n - 1)) * w) * B n + B (n - 1)) := by
    linear_combination -hb_mul
  have hcop_uv : IsCoprime u v := coprime_of_adj u v (A n) (B n) hadj
  have hadj' : IsUnit (((((v * A (n - 1) - u * B (n - 1)) * w) * A n + A (n - 1)) * B n -
      (((v * A (n - 1) - u * B (n - 1)) * w) * B n + B (n - 1)) * A n)) := by
    have hring : ((((v * A (n - 1) - u * B (n - 1)) * w) * A n + A (n - 1)) * B n -
        (((v * A (n - 1) - u * B (n - 1)) * w) * B n + B (n - 1)) * A n) =
        -(A n * B (n - 1) - A (n - 1) * B n) := by ring
    rw [hring]
    exact hdet_n.neg
  have hcop_AB : IsCoprime (((v * A (n - 1) - u * B (n - 1)) * w) * A n + A (n - 1))
      (((v * A (n - 1) - u * B (n - 1)) * w) * B n + B (n - 1)) :=
    coprime_of_adj _ _ (A n) (B n) hadj'
  have hdvd1 : v ∣ ((v * A (n - 1) - u * B (n - 1)) * w) * B n + B (n - 1) := by
    have h1 : v ∣ u * (((v * A (n - 1) - u * B (n - 1)) * w) * B n + B (n - 1)) :=
      ⟨((v * A (n - 1) - u * B (n - 1)) * w) * A n + A (n - 1), heq.symm⟩
    exact hcop_uv.symm.dvd_of_dvd_mul_left h1
  have hdvd2 : (((v * A (n - 1) - u * B (n - 1)) * w) * B n + B (n - 1)) ∣ v := by
    have h2 : (((v * A (n - 1) - u * B (n - 1)) * w) * B n + B (n - 1)) ∣
        (((v * A (n - 1) - u * B (n - 1)) * w) * A n + A (n - 1)) * v := by
      refine ⟨u, ?_⟩
      rw [mul_comm (((v * A (n - 1) - u * B (n - 1)) * w) * A n + A (n - 1)) v, heq,
        mul_comm u (((v * A (n - 1) - u * B (n - 1)) * w) * B n + B (n - 1))]
    exact hcop_AB.symm.dvd_of_dvd_mul_left h2
  have hB'_ne : ((v * A (n - 1) - u * B (n - 1)) * w) * B n + B (n - 1) ≠ 0 := by
    intro hcon
    rw [hcon] at hdvd2
    obtain ⟨k, hk⟩ := hdvd2
    have hv0 : v = 0 := by simpa using hk
    exact hv_ne hv0
  have hdeg_eq : (((v * A (n - 1) - u * B (n - 1)) * w) * B n + B (n - 1)).degree =
      v.degree := by
    apply le_antisymm
    · exact degree_le_of_dvd hdvd2 hv_ne
    · exact degree_le_of_dvd hdvd1 hB'_ne
  refine ⟨(v * A (n - 1) - u * B (n - 1)) * w, ?_, ?_, ?_⟩
  · -- b is nonconstant by degree comparison
    by_contra hcon
    have hb0 : (((v * A (n - 1) - u * B (n - 1)) * w)).natDegree = 0 := by omega
    by_cases hb : (v * A (n - 1) - u * B (n - 1)) * w = 0
    · rw [hb] at hdeg_eq
      simp only [zero_mul, zero_add] at hdeg_eq
      have hlt : (B (n - 1)).degree < v.degree := hmono.trans hdeg
      rw [hdeg_eq] at hlt
      exact lt_irrefl _ hlt
    · have hbdeg : (((v * A (n - 1) - u * B (n - 1)) * w)).degree = 0 := by
        rw [degree_eq_natDegree hb, hb0, Nat.cast_zero]
      have hmul_deg : (((v * A (n - 1) - u * B (n - 1)) * w) * B n).degree =
          (B n).degree := by
        rw [degree_mul, hbdeg, zero_add]
      have hsum : (B (n - 1)).degree <
          (((v * A (n - 1) - u * B (n - 1)) * w) * B n).degree := by
        rw [hmul_deg]
        exact hmono
      have hB'_deg : ((((v * A (n - 1) - u * B (n - 1)) * w) * B n +
          B (n - 1))).degree = (B n).degree := by
        rw [degree_add_eq_left_of_degree_lt hsum, hmul_deg]
      rw [hB'_deg] at hdeg_eq
      rw [hdeg_eq] at hdeg
      exact lt_irrefl _ hdeg
  · -- b equals the required fraction in F(X)
    have hd_ne : u * B n - v * A n ≠ 0 := hadj.ne_zero
    have halg_d_ne : algebraMap F[X] (RatFunc F) (u * B n - v * A n) ≠ 0 := by
      intro hcon
      have h0 : algebraMap F[X] (RatFunc F) (u * B n - v * A n) =
          algebraMap F[X] (RatFunc F) 0 := by
        simpa using hcon
      exact hd_ne (hinj h0)
    have hmul : algebraMap F[X] (RatFunc F) ((v * A (n - 1) - u * B (n - 1)) * w) *
        algebraMap F[X] (RatFunc F) (u * B n - v * A n) =
        algebraMap F[X] (RatFunc F) (v * A (n - 1) - u * B (n - 1)) := by
      have h := congrArg (algebraMap F[X] (RatFunc F)) hb_mul
      simpa [map_mul] using h
    exact (eq_div_iff halg_d_ne).mpr hmul
  · -- the extended convergent equals u/v
    have hext_n1 := ext_nums_dens_eq a n ((v * A (n - 1) - u * B (n - 1)) * w)
      (n - 1) (by omega)
    have hext_n := ext_nums_dens_eq a n ((v * A (n - 1) - u * B (n - 1)) * w) n le_rfl
    have hA_n1 := hA (n - 1) (by omega)
    have hA_n := hA n le_rfl
    have hB_n1 := hB (n - 1) (by omega)
    have hB_n := hB n le_rfl
    have hext_n1_num : (polyContFract
        (Function.update a (n + 1) ((v * A (n - 1) - u * B (n - 1)) * w)) (n + 1)).nums
        (n - 1) = algebraMap F[X] (RatFunc F) (A (n - 1)) :=
      hext_n1.1.trans hA_n1
    have hext_n_num : (polyContFract
        (Function.update a (n + 1) ((v * A (n - 1) - u * B (n - 1)) * w)) (n + 1)).nums
        n = algebraMap F[X] (RatFunc F) (A n) :=
      hext_n.1.trans hA_n
    have hext_n1_den : (polyContFract
        (Function.update a (n + 1) ((v * A (n - 1) - u * B (n - 1)) * w)) (n + 1)).dens
        (n - 1) = algebraMap F[X] (RatFunc F) (B (n - 1)) :=
      hext_n1.2.trans hB_n1
    have hext_n_den : (polyContFract
        (Function.update a (n + 1) ((v * A (n - 1) - u * B (n - 1)) * w)) (n + 1)).dens
        n = algebraMap F[X] (RatFunc F) (B n) :=
      hext_n.2.trans hB_n
    have hs_n : (polyContFract
        (Function.update a (n + 1) ((v * A (n - 1) - u * B (n - 1)) * w)) (n + 1)).s.get?
        n = some ⟨1, algebraMap F[X] (RatFunc F)
        ((v * A (n - 1) - u * B (n - 1)) * w)⟩ := by
      have h1 : n < n + 1 := by omega
      simp [polyContFract_s_get?, h1]
    have hsub1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hsub2 : n - 1 + 2 = n + 1 := by omega
    have hs' : (polyContFract
        (Function.update a (n + 1) ((v * A (n - 1) - u * B (n - 1)) * w)) (n + 1)).s.get?
        (n - 1 + 1) = some ⟨1, algebraMap F[X] (RatFunc F)
        ((v * A (n - 1) - u * B (n - 1)) * w)⟩ := by
      rw [hsub1]
      exact hs_n
    have hext_n_num' : (polyContFract
        (Function.update a (n + 1) ((v * A (n - 1) - u * B (n - 1)) * w)) (n + 1)).nums
        (n - 1 + 1) = algebraMap F[X] (RatFunc F) (A n) := by
      rw [hsub1]
      exact hext_n_num
    have hext_n_den' : (polyContFract
        (Function.update a (n + 1) ((v * A (n - 1) - u * B (n - 1)) * w)) (n + 1)).dens
        (n - 1 + 1) = algebraMap F[X] (RatFunc F) (B n) := by
      rw [hsub1]
      exact hext_n_den
    have hnums := GenContFract.nums_recurrence (n := n - 1) hs' hext_n1_num hext_n_num'
    have hdens := GenContFract.dens_recurrence (n := n - 1) hs' hext_n1_den hext_n_den'
    rw [hsub2] at hnums hdens
    have hnums' : (polyContFract
        (Function.update a (n + 1) ((v * A (n - 1) - u * B (n - 1)) * w)) (n + 1)).nums
        (n + 1) = algebraMap F[X] (RatFunc F)
        (((v * A (n - 1) - u * B (n - 1)) * w) * A n + A (n - 1)) := by
      simpa only [map_add, map_mul, one_mul] using hnums
    have hdens' : (polyContFract
        (Function.update a (n + 1) ((v * A (n - 1) - u * B (n - 1)) * w)) (n + 1)).dens
        (n + 1) = algebraMap F[X] (RatFunc F)
        (((v * A (n - 1) - u * B (n - 1)) * w) * B n + B (n - 1)) := by
      simpa only [map_add, map_mul, one_mul] using hdens
    have halg_v_ne : algebraMap F[X] (RatFunc F) v ≠ 0 := by
      intro hcon
      have h0 : algebraMap F[X] (RatFunc F) v = algebraMap F[X] (RatFunc F) 0 := by
        simpa using hcon
      exact hv_ne (hinj h0)
    have halg_B'_ne : algebraMap F[X] (RatFunc F)
        (((v * A (n - 1) - u * B (n - 1)) * w) * B n + B (n - 1)) ≠ 0 := by
      intro hcon
      have h0 : algebraMap F[X] (RatFunc F)
          (((v * A (n - 1) - u * B (n - 1)) * w) * B n + B (n - 1)) =
          algebraMap F[X] (RatFunc F) 0 := by
        simpa using hcon
      exact hB'_ne (hinj h0)
    rw [GenContFract.conv_eq_num_div_den, hnums', hdens']
    rw [div_eq_div_iff halg_B'_ne halg_v_ne]
    have hmap := congrArg (algebraMap F[X] (RatFunc F)) heq
    simp only [map_mul] at hmap
    linear_combination hmap

end MetaMathlibExt
