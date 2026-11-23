/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import MathlibExt.NumberTheory.PrimeCounting.WeightedLargeSieve
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

open scoped BigOperators

namespace MathlibExt.NumberTheory.PrimeCounting

private theorem btFareySpacing (a b r s z : ℕ) (hr : 0 < r) (hs : 0 < s)
    (har : a < r) (hbs : b < s) (hsz : s ≤ z)
    (hne : a * s ≠ b * r) :
    1 / ((r : ℝ) * z) ≤
      ‖((((a : ℝ) / r - (b : ℝ) / s) : ℝ) : AddCircle (1 : ℝ))‖ := by
  let d : ℝ := (a : ℝ) / r - (b : ℝ) / s
  let k : ℤ := round d
  let m : ℤ := (a : ℤ) * s - (b : ℤ) * r - k * (r * s)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hadiv : 0 ≤ (a : ℝ) / r ∧ (a : ℝ) / r < 1 := by
    constructor
    · positivity
    · rw [div_lt_one hrR]
      exact_mod_cast har
  have hbdiv : 0 ≤ (b : ℝ) / s ∧ (b : ℝ) / s < 1 := by
    constructor
    · positivity
    · rw [div_lt_one hsR]
      exact_mod_cast hbs
  have hd : -1 < d ∧ d < 1 := by
    simp only [d]
    constructor <;> linarith [hadiv.1, hadiv.2, hbdiv.1, hbdiv.2]
  have hm0 : m ≠ 0 := by
    intro hm
    have hmR : ((m : ℤ) : ℝ) = 0 := by rw [hm]; norm_num
    have hdk : d = (k : ℝ) := by
      simp only [m] at hmR
      push_cast at hmR
      simp only [d]
      field_simp at hmR ⊢
      nlinarith
    have hkLower : (-1 : ℤ) < k := by
      exact_mod_cast (hd.1.trans_eq hdk)
    have hkUpper : k < (1 : ℤ) := by
      exact_mod_cast (hdk.symm.trans_lt hd.2)
    have hk0 : k = 0 := by omega
    have hd0 : d = 0 := by rw [hdk, hk0]; norm_num
    have hcrossR : (a : ℝ) * s = (b : ℝ) * r := by
      simp only [d] at hd0
      field_simp at hd0
      linarith
    apply hne
    exact_mod_cast hcrossR
  have hmOne : (1 : ℝ) ≤ |(m : ℝ)| := by
    exact_mod_cast Int.one_le_abs hm0
  have hrepr : d - (k : ℝ) = (m : ℝ) / ((r : ℝ) * s) := by
    simp only [d, m]
    push_cast
    field_simp
  rw [show (((a : ℝ) / r - (b : ℝ) / s) : ℝ) = d by rfl]
  rw [AddCircle.norm_eq]
  simp only [inv_one, one_mul]
  have hk : round d = k := by rfl
  rw [hk]
  simp only [mul_one]
  rw [hrepr, abs_div, abs_of_pos (mul_pos hrR hsR)]
  calc
    1 / ((r : ℝ) * z) ≤ 1 / ((r : ℝ) * s) := by
      apply one_div_le_one_div_of_le (mul_pos hrR hsR)
      gcongr
    _ ≤ |(m : ℝ)| / ((r : ℝ) * s) := by
      exact div_le_div_of_nonneg_right hmOne (mul_pos hrR hsR).le

private def btFareyIndex (z : ℕ) :=
  {p : Fin (z + 1) × Fin (z + 1) //
    0 < p.2.1 ∧ p.1.1 < p.2.1 ∧ Nat.Coprime p.1.1 p.2.1}

private noncomputable instance (z : ℕ) : Fintype (btFareyIndex z) := by
  classical
  unfold btFareyIndex
  infer_instance

private noncomputable def btFareyPoint {z : ℕ} (p : btFareyIndex z) : ℝ :=
  (p.1.1.1 : ℝ) / p.1.2.1

private noncomputable def btFareyDelta {z : ℕ} (p : btFareyIndex z) : ℝ :=
  1 / ((p.1.2.1 : ℝ) * z)

private theorem btFareyCross_ne {z : ℕ} {p q : btFareyIndex z} (hpq : p ≠ q) :
    p.1.1.1 * q.1.2.1 ≠ q.1.1.1 * p.1.2.1 := by
  intro hcross
  have hrDivS : p.1.2.1 ∣ q.1.2.1 := by
    apply p.2.2.2.symm.dvd_of_dvd_mul_left
    exact ⟨q.1.1.1, hcross.trans (mul_comm _ _)⟩
  have hsDivR : q.1.2.1 ∣ p.1.2.1 := by
    apply q.2.2.2.symm.dvd_of_dvd_mul_left
    exact ⟨p.1.1.1, hcross.symm.trans (mul_comm _ _)⟩
  have hrs : p.1.2.1 = q.1.2.1 := Nat.dvd_antisymm hrDivS hsDivR
  have hab : p.1.1.1 = q.1.1.1 := by
    apply Nat.eq_of_mul_eq_mul_right p.2.1
    simpa only [hrs] using hcross
  apply hpq
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext hab
  · exact Fin.ext hrs

private theorem btFareyDelta_pos {z : ℕ} (hz : 0 < z) (p : btFareyIndex z) :
    0 < btFareyDelta p := by
  unfold btFareyDelta
  apply one_div_pos.mpr
  exact mul_pos (by exact_mod_cast p.2.1) (by exact_mod_cast hz)

private theorem btFarey_separated {z : ℕ} (p q : btFareyIndex z) (hpq : p ≠ q) :
    btFareyDelta p ≤
      ‖((btFareyPoint p - btFareyPoint q : ℝ) : AddCircle (1 : ℝ))‖ := by
  apply btFareySpacing p.1.1.1 q.1.1.1 p.1.2.1 q.1.2.1 z
  · exact p.2.1
  · exact q.2.1
  · exact p.2.2.1
  · exact q.2.2.1
  · omega
  · exact btFareyCross_ne hpq

private theorem btFareyLargeSieve (N z : ℕ) (hz : 0 < z) (a : ℕ → ℂ) :
    ∑ p : btFareyIndex z,
        ((N : ℝ) + 3 * (p.1.2.1 : ℝ) * z / 2)⁻¹ *
          ‖∑ n ∈ Finset.range N,
            a n * Complex.exp ((((2 * Real.pi *
              (n * btFareyPoint p) : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
      ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  have h := weightedLargeSieve N btFareyPoint btFareyDelta a
    (btFareyDelta_pos hz) btFarey_separated
  convert h using 1
  apply Finset.sum_congr rfl
  intro p _
  congr 2
  unfold btFareyDelta
  have hp : (0 : ℝ) < p.1.2.1 := by exact_mod_cast p.2.1
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  field_simp

private noncomputable def btFareyFourier {z : ℕ}
    (S : Finset ℕ) (p : btFareyIndex z) : ℂ :=
  ∑ n ∈ S, Complex.exp ((((2 * Real.pi *
    (n * btFareyPoint p) : ℝ) : ℝ) : ℂ) * Complex.I)

private noncomputable def btSieveDensity (N z : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 z,
    ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
      (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)

private theorem btIndicatorFourier {N z : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.range N) (p : btFareyIndex z) :
    ∑ n ∈ Finset.range N,
        (if n ∈ S then (1 : ℂ) else 0) *
          Complex.exp ((((2 * Real.pi *
            (n * btFareyPoint p) : ℝ) : ℝ) : ℂ) * Complex.I) =
      btFareyFourier S p := by
  rw [btFareyFourier]
  calc
    ∑ n ∈ Finset.range N,
        (if n ∈ S then (1 : ℂ) else 0) *
          Complex.exp ((((2 * Real.pi *
            (n * btFareyPoint p) : ℝ) : ℝ) : ℂ) * Complex.I) =
        ∑ n ∈ S, (if n ∈ S then (1 : ℂ) else 0) *
          Complex.exp ((((2 * Real.pi *
            (n * btFareyPoint p) : ℝ) : ℝ) : ℂ) * Complex.I) := by
      symm
      apply Finset.sum_subset hS
      intro n _ hn
      simp [hn]
    _ = _ := by simp

private theorem btIndicatorNormSum {N : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.range N) :
    ∑ n ∈ Finset.range N, ‖if n ∈ S then (1 : ℂ) else 0‖ ^ 2 = S.card := by
  calc
    ∑ n ∈ Finset.range N, ‖if n ∈ S then (1 : ℂ) else 0‖ ^ 2 =
        ∑ n ∈ S, ‖if n ∈ S then (1 : ℂ) else 0‖ ^ 2 := by
      symm
      apply Finset.sum_subset hS
      intro n _ hn
      simp [hn]
    _ = ∑ _n ∈ S, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [hn]
    _ = S.card := by simp

private theorem btSieveWeight_nonneg (N z r : ℕ) :
    0 ≤ ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ := by positivity

private theorem btFareyDen_mem {z : ℕ} (p : btFareyIndex z) :
    p.1.2.1 ∈ Finset.Icc 1 z := by
  simp only [Finset.mem_Icc]
  constructor
  · exact p.2.1
  · exact Nat.lt_succ_iff.mp p.1.2.isLt

private theorem btArithmeticLargeSieve (N z : ℕ) (hz : 0 < z) (S : Finset ℕ)
    (hS : S ⊆ Finset.range N)
    (hlocal : ∀ r ∈ Finset.Icc 1 z,
      (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r) * S.card ^ 2 ≤
        ∑ p : btFareyIndex z,
          if p.1.2.1 = r then ‖btFareyFourier S p‖ ^ 2 else 0) :
    btSieveDensity N z * S.card ^ 2 ≤ S.card := by
  let w : ℕ → ℝ := fun r ↦ ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹
  have hsummed : btSieveDensity N z * S.card ^ 2 ≤
      ∑ r ∈ Finset.Icc 1 z, w r *
        ∑ p : btFareyIndex z,
          if p.1.2.1 = r then ‖btFareyFourier S p‖ ^ 2 else 0 := by
    rw [btSieveDensity, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro r hr
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hlocal r hr) (btSieveWeight_nonneg N z r)
  have hcollapse :
      (∑ r ∈ Finset.Icc 1 z, w r *
        ∑ p : btFareyIndex z,
          if p.1.2.1 = r then ‖btFareyFourier S p‖ ^ 2 else 0) =
        ∑ p : btFareyIndex z, w p.1.2.1 * ‖btFareyFourier S p‖ ^ 2 := by
    calc
      (∑ r ∈ Finset.Icc 1 z, w r *
          ∑ p : btFareyIndex z,
            if p.1.2.1 = r then ‖btFareyFourier S p‖ ^ 2 else 0) =
          ∑ r ∈ Finset.Icc 1 z, ∑ p : btFareyIndex z,
            w r * (if p.1.2.1 = r then ‖btFareyFourier S p‖ ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
      _ = ∑ p : btFareyIndex z, ∑ r ∈ Finset.Icc 1 z,
          w r * (if p.1.2.1 = r then ‖btFareyFourier S p‖ ^ 2 else 0) :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p _
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq]
        simp only [btFareyDen_mem p, ite_true]
  rw [hcollapse] at hsummed
  have hlarge := btFareyLargeSieve N z hz
    (fun n ↦ if n ∈ S then (1 : ℂ) else 0)
  simp_rw [btIndicatorFourier S hS] at hlarge
  rw [btIndicatorNormSum S hS] at hlarge
  exact hsummed.trans hlarge

private theorem btCompleteRootSum (k : ℕ) (hk : 0 < k) :
    ∑ b ∈ Finset.range k,
        Complex.exp ((((2 * Real.pi * ((b : ℝ) / k) : ℝ) : ℂ) * Complex.I)) =
      if k = 1 then 1 else 0 := by
  cases k with
  | zero => omega
  | succ k =>
      by_cases hk0 : k = 0
      · subst k
        norm_num
      · have hk1 : k.succ ≠ 1 := by omega
        rw [ite_eq_right hk1, ← Fin.sum_univ_eq_sum_range]
        let _ : NeZero k.succ := ⟨by omega⟩
        let _ : Fact (1 < k.succ) := ⟨by omega⟩
        have hchar (j : ZMod k.succ) :
            ZMod.stdAddChar j =
              Complex.exp ((((2 * Real.pi *
                ((j.val : ℝ) / k.succ) : ℝ) : ℂ) * Complex.I)) := by
          rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
          push_cast
          congr 1
          ring
        have hzero : (∑ j : ZMod k.succ, ZMod.stdAddChar j) = 0 := by
          have hone : (1 : ZMod k.succ) ≠ 0 := one_ne_zero
          have hshift :
              (∑ j : ZMod k.succ, ZMod.stdAddChar (1 * j)) = 0 :=
            AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar k.succ hone)
          simpa only [one_mul] using hshift
        calc
          (∑ b : Fin k.succ,
              Complex.exp ((((2 * Real.pi *
                ((b : ℝ) / (k.succ : ℝ)) : ℝ) : ℂ) * Complex.I))) =
              ∑ b : Fin k.succ, ZMod.stdAddChar (ZMod.finEquiv k.succ b) := by
                apply Finset.sum_congr rfl
                intro b _
                rw [hchar]
                rfl
          _ = ∑ j : ZMod k.succ, ZMod.stdAddChar j := by
            exact Fintype.sum_equiv (ZMod.finEquiv k.succ).toEquiv _ _
              (fun _ ↦ rfl)
          _ = 0 := hzero

private noncomputable def btRoot (k b : ℕ) : ℂ :=
  Complex.exp ((((2 * Real.pi * ((b : ℝ) / k) : ℝ) : ℂ) * Complex.I))

private theorem btRoot_add (k b c : ℕ) :
    btRoot k (b + c) = btRoot k b * btRoot k c := by
  unfold btRoot
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem btRoot_norm (k b : ℕ) : ‖btRoot k b‖ = 1 := by
  unfold btRoot
  convert Complex.norm_exp_ofReal_mul_I (2 * Real.pi * ((b : ℝ) / k)) using 1

private theorem btCompleteRootSum_mul (k n : ℕ) (hk : 0 < k)
    (hn : Nat.Coprime n k) :
    ∑ b ∈ Finset.range k, btRoot k (b * n) = if k = 1 then 1 else 0 := by
  cases k with
  | zero => omega
  | succ k =>
      by_cases hk0 : k = 0
      · subst k
        simp [btRoot]
      · have hk1 : k.succ ≠ 1 := by omega
        rw [ite_eq_right hk1, ← Fin.sum_univ_eq_sum_range]
        let _ : NeZero k.succ := ⟨by omega⟩
        have hnz : (n : ZMod k.succ) ≠ 0 := by
          intro hzero
          have hdiv : k.succ ∣ n :=
            (ZMod.natCast_eq_zero_iff n k.succ).mp hzero
          exact hk1 (hn.symm.eq_one_of_dvd hdiv)
        have hzero :
            (∑ j : ZMod k.succ, ZMod.stdAddChar ((n : ZMod k.succ) * j)) = 0 :=
          AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar k.succ hnz)
        calc
          (∑ b : Fin k.succ, btRoot k.succ (b * n)) =
              ∑ b : Fin k.succ,
                ZMod.stdAddChar ((n : ZMod k.succ) * ZMod.finEquiv k.succ b) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [← ZMod.natCast_zmod_val (ZMod.finEquiv k.succ b)]
            change btRoot k.succ (b.val * n) =
              ZMod.stdAddChar ((n : ZMod k.succ) * (b.val : ZMod k.succ))
            rw [← Nat.cast_mul]
            rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
            unfold btRoot
            push_cast
            congr 1
            ring
          _ = ∑ j : ZMod k.succ,
              ZMod.stdAddChar ((n : ZMod k.succ) * j) := by
            exact Fintype.sum_equiv (ZMod.finEquiv k.succ).toEquiv _ _
              (fun _ ↦ rfl)
          _ = 0 := hzero

private theorem btRoot_mul_div (r d a : ℕ) (hr : 0 < r) (hd : 0 < d)
    (hdr : d ∣ r) (hda : d ∣ a) :
    btRoot r a = btRoot (r / d) (a / d) := by
  have hrdiv : 0 < r / d := Nat.div_pos (Nat.le_of_dvd hr hdr) hd
  have haeq : d * (a / d) = a := Nat.mul_div_cancel' hda
  have hreq : d * (r / d) = r := Nat.mul_div_cancel' hdr
  have hfrac : (a : ℝ) / r =
      ((a / d : ℕ) : ℝ) / ((r / d : ℕ) : ℝ) := by
    calc
      (a : ℝ) / r = ((d * (a / d) : ℕ) : ℝ) /
          ((d * (r / d) : ℕ) : ℝ) := by rw [haeq, hreq]
      _ = ((a / d : ℕ) : ℝ) / ((r / d : ℕ) : ℝ) := by
        push_cast
        field_simp
  unfold btRoot
  congr 3
  rw [hfrac]

private theorem btRootMultiplesSum (r d : ℕ) (hr : 0 < r) (hd : 0 < d)
    (hdr : d ∣ r) :
    ∑ a ∈ Finset.range r, (if d ∣ a then btRoot r a else 0) =
      ∑ b ∈ Finset.range (r / d), btRoot (r / d) b := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ ↦ a / d) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    exact Finset.mem_range.mpr ((Nat.div_lt_div_right hd.ne' hdr).mpr ha.1)
  · intro a ha b hb hab
    simp only [Finset.mem_filter] at ha hb
    rw [← Nat.mul_div_cancel' ha.2, ← Nat.mul_div_cancel' hb.2, hab]
  · intro b hb
    simp only [Finset.mem_range] at hb
    refine ⟨d * b, ?_, Nat.mul_div_cancel_left b hd⟩
    simp only [Finset.mem_filter, Finset.mem_range, Nat.dvd_mul_right]
    constructor
    · rw [← Nat.mul_div_cancel' hdr]
      exact (Nat.mul_lt_mul_left hd).mpr hb
    · simp
  · intro a ha
    simp only [Finset.mem_filter] at ha
    exact btRoot_mul_div r d a hr hd hdr ha.2

private theorem btRootMultiplesSum_mul (r d n : ℕ) (hr : 0 < r) (hd : 0 < d)
    (hdr : d ∣ r) :
    ∑ a ∈ Finset.range r, (if d ∣ a then btRoot r (a * n) else 0) =
      ∑ b ∈ Finset.range (r / d), btRoot (r / d) (b * n) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ ↦ a / d) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    exact Finset.mem_range.mpr ((Nat.div_lt_div_right hd.ne' hdr).mpr ha.1)
  · intro a ha b hb hab
    simp only [Finset.mem_filter] at ha hb
    rw [← Nat.mul_div_cancel' ha.2, ← Nat.mul_div_cancel' hb.2, hab]
  · intro b hb
    simp only [Finset.mem_range] at hb
    refine ⟨d * b, ?_, Nat.mul_div_cancel_left b hd⟩
    simp only [Finset.mem_filter, Finset.mem_range, Nat.dvd_mul_right]
    constructor
    · rw [← Nat.mul_div_cancel' hdr]
      exact (Nat.mul_lt_mul_left hd).mpr hb
    · simp
  · intro a ha
    simp only [Finset.mem_filter] at ha
    have hdan : d ∣ a * n := ha.2.trans (Nat.dvd_mul_right a n)
    rw [btRoot_mul_div r d (a * n) hr hd hdr hdan]
    congr 2
    rw [mul_comm a n, Nat.mul_div_assoc n ha.2, mul_comm]

private theorem btSumMoebiusDivisorsLocal (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ ↦ f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

private theorem btDivisorsGcdLocal (r a : ℕ) (hr : r ≠ 0) :
    (Nat.gcd r a).divisors = r.divisors.filter (fun d ↦ d ∣ a) := by
  have hg : Nat.gcd r a ≠ 0 :=
    (Nat.gcd_pos_of_pos_left a (Nat.pos_of_ne_zero hr)).ne'
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · rintro ⟨hd, -⟩
    exact ⟨⟨(Nat.dvd_gcd_iff.mp hd).1, hr⟩, (Nat.dvd_gcd_iff.mp hd).2⟩
  · rintro ⟨⟨hdr, -⟩, hda⟩
    exact ⟨Nat.dvd_gcd hdr hda, hg⟩

private theorem btMobiusCoprimeIndicatorLocal (r a : ℕ) (hr : r ≠ 0) :
    (∑ d ∈ r.divisors,
      if d ∣ a then ArithmeticFunction.moebius d else 0) =
      if Nat.Coprime r a then 1 else 0 := by
  rw [← Finset.sum_filter, ← btDivisorsGcdLocal r a hr]
  rw [btSumMoebiusDivisorsLocal]

private theorem btRamanujanUnitSum (r n : ℕ) (hr : 0 < r)
    (hn : Nat.Coprime n r) :
    ∑ a ∈ Finset.range r,
      (if Nat.Coprime a r then btRoot r (a * n) else 0) =
      ArithmeticFunction.moebius r := by
  have hind (a : ℕ) :
      ((if Nat.Coprime a r then (1 : ℤ) else 0) : ℤ) =
        ∑ d ∈ r.divisors,
          if d ∣ a then ArithmeticFunction.moebius d else 0 := by
    simpa only [Nat.coprime_comm] using
      (btMobiusCoprimeIndicatorLocal r a hr.ne').symm
  calc
    (∑ a ∈ Finset.range r,
        (if Nat.Coprime a r then btRoot r (a * n) else 0)) =
        ∑ a ∈ Finset.range r,
          (((if Nat.Coprime a r then (1 : ℤ) else 0) : ℤ) : ℂ) *
            btRoot r (a * n) := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp_all
    _ = ∑ a ∈ Finset.range r,
        ((∑ d ∈ r.divisors,
          if d ∣ a then ArithmeticFunction.moebius d else 0 : ℤ) : ℂ) *
            btRoot r (a * n) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hind]
    _ = ∑ d ∈ r.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          ∑ a ∈ Finset.range r,
            (if d ∣ a then btRoot r (a * n) else 0) := by
      push_cast
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro a _
      by_cases hda : d ∣ a <;> simp [hda]
    _ = ∑ d ∈ r.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          (if r / d = 1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hdmem
      have hdr := (Nat.mem_divisors.mp hdmem).1
      have hd : 0 < d := Nat.pos_of_ne_zero
        (ne_zero_of_dvd_ne_zero hr.ne' hdr)
      rw [btRootMultiplesSum_mul r d n hr hd hdr]
      have hdiv : r / d ∣ r := ⟨d, (Nat.div_mul_cancel hdr).symm⟩
      rw [btCompleteRootSum_mul (r / d) n
        (Nat.div_pos (Nat.le_of_dvd hr hdr) hd) (hn.of_dvd_right hdiv)]
    _ = ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
        (if r / r = 1 then 1 else 0) := by
      apply Finset.sum_eq_single r
      · intro d hdmem hdrNe
        have hdr := (Nat.mem_divisors.mp hdmem).1
        have hmul := Nat.mul_div_cancel' hdr
        have hne : r / d ≠ 1 := by
          intro hone
          apply hdrNe
          simpa [hone] using hmul
        simp [hne]
      · intro hrmem
        exact (hrmem (Nat.mem_divisors.mpr ⟨dvd_rfl, hr.ne'⟩)).elim
    _ = ArithmeticFunction.moebius r := by
      rw [Nat.div_self hr]
      simp

private theorem btLocalFourierLower (r c : ℕ) (S : Finset ℕ) (hr : 0 < r)
    (hcop : ∀ n ∈ S, Nat.Coprime (n + c) r) :
    (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r) * S.card ^ 2 ≤
      ∑ a ∈ (Finset.range r).filter (fun a ↦ Nat.Coprime a r),
        ‖∑ n ∈ S, btRoot r (a * n)‖ ^ 2 := by
  let A := (Finset.range r).filter (fun a ↦ Nat.Coprime a r)
  let F : ℕ → ℂ := fun a ↦ ∑ n ∈ S, btRoot r (a * (n + c))
  have hinner (n : ℕ) (hnS : n ∈ S) :
      ∑ a ∈ A, btRoot r (a * (n + c)) = ArithmeticFunction.moebius r := by
    have hn := hcop n hnS
    simpa only [A, ← Finset.sum_filter] using btRamanujanUnitSum r (n + c) hr hn
  have hsum : ∑ a ∈ A, F a =
      (S.card : ℂ) * ArithmeticFunction.moebius r := by
    calc
      ∑ a ∈ A, F a =
          ∑ a ∈ A, ∑ n ∈ S, btRoot r (a * (n + c)) := rfl
      _ = ∑ n ∈ S, ∑ a ∈ A, btRoot r (a * (n + c)) := by
        rw [Finset.sum_comm]
      _ = ∑ _n ∈ S, ((ArithmeticFunction.moebius r : ℤ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hnS
        exact hinner n hnS
      _ = (S.card : ℂ) * ArithmeticFunction.moebius r := by simp
  have hFnorm (a : ℕ) : ‖F a‖ = ‖∑ n ∈ S, btRoot r (a * n)‖ := by
    have hfactor : F a =
        (∑ n ∈ S, btRoot r (a * n)) * btRoot r (a * c) := by
      simp only [F, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      rw [← btRoot_add]
      congr 2
      ring
    rw [hfactor, norm_mul, btRoot_norm, mul_one]
  have hcard : A.card = Nat.totient r := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext a
    simp only [A, Finset.mem_filter, Nat.coprime_comm]
  have htri : ‖∑ a ∈ A, F a‖ ≤ ∑ a ∈ A, ‖F a‖ := norm_sum_le A F
  have hsq : ‖∑ a ∈ A, F a‖ ^ 2 ≤
      (Nat.totient r : ℝ) * ∑ a ∈ A, ‖F a‖ ^ 2 := by
    calc
      ‖∑ a ∈ A, F a‖ ^ 2 ≤ (∑ a ∈ A, ‖F a‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ (A.card : ℝ) * ∑ a ∈ A, ‖F a‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ = (Nat.totient r : ℝ) * ∑ a ∈ A, ‖F a‖ ^ 2 := by rw [hcard]
  have hphi : (0 : ℝ) < Nat.totient r := by
    exact_mod_cast Nat.totient_pos.mpr hr
  rcases ArithmeticFunction.moebius_eq_or r with hmu | hmu | hmu
  · rw [hmu]
    norm_num
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  · rw [hmu] at hsum ⊢
    norm_num at hsum ⊢
    rw [hsum] at hsq
    norm_num at hsq
    rw [inv_mul_le_iff₀ hphi]
    simpa only [A, hFnorm] using hsq
  · rw [hmu] at hsum ⊢
    norm_num at hsum ⊢
    rw [hsum] at hsq
    norm_num at hsq
    rw [inv_mul_le_iff₀ hphi]
    simpa only [A, hFnorm] using hsq

private theorem btFareyFourier_eq_root {z : ℕ} (S : Finset ℕ)
    (p : btFareyIndex z) :
    btFareyFourier S p =
      ∑ n ∈ S, btRoot p.1.2.1 (p.1.1.1 * n) := by
  unfold btFareyFourier btFareyPoint btRoot
  apply Finset.sum_congr rfl
  intro n _
  congr 3
  have hp : (0 : ℝ) < p.1.2.1 := by exact_mod_cast p.2.1
  push_cast
  field_simp

private def btFareyMk {z : ℕ} (a r : ℕ) (hr : 0 < r) (har : a < r)
    (hrz : r ≤ z) (hcop : Nat.Coprime a r) : btFareyIndex z :=
  ⟨(⟨a, by omega⟩, ⟨r, by omega⟩), hr, har, hcop⟩

@[simp] private theorem btFareyMk_num {z a r : ℕ} {hr : 0 < r} {har : a < r}
    {hrz : r ≤ z} {hcop : Nat.Coprime a r} :
    (btFareyMk a r hr har hrz hcop).1.1.1 = a := rfl

@[simp] private theorem btFareyMk_den {z a r : ℕ} {hr : 0 < r} {har : a < r}
    {hrz : r ≤ z} {hcop : Nat.Coprime a r} :
    (btFareyMk a r hr har hrz hcop).1.2.1 = r := rfl

private theorem btFareyFiberFourierLower (z r c : ℕ) (S : Finset ℕ)
    (hrz : r ∈ Finset.Icc 1 z) (hcop : ∀ n ∈ S, Nat.Coprime (n + c) r) :
    (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r) * S.card ^ 2 ≤
      ∑ p : btFareyIndex z,
        if p.1.2.1 = r then ‖btFareyFourier S p‖ ^ 2 else 0 := by
  have hrz' := Finset.mem_Icc.mp hrz
  have hr : 0 < r := by omega
  have hbase := btLocalFourierLower r c S hr hcop
  apply hbase.trans_eq
  rw [← Finset.sum_filter]
  let A := (Finset.range r).filter (fun a ↦ Nat.Coprime a r)
  change (∑ a ∈ A, ‖∑ n ∈ S, btRoot r (a * n)‖ ^ 2) =
    ∑ p ∈ Finset.univ.filter (fun p : btFareyIndex z ↦ p.1.2.1 = r),
      ‖btFareyFourier S p‖ ^ 2
  refine Finset.sum_bij (fun a ha ↦
    btFareyMk a r hr (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      hrz'.2 (Finset.mem_filter.mp ha).2) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp
  · intro a₁ ha₁ a₂ ha₂ heq
    have hnum := congrArg (fun p : btFareyIndex z ↦ p.1.1.1) heq
    exact hnum
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨p.1.1.1, ?_, ?_⟩
    · simp only [A, Finset.mem_filter, Finset.mem_range]
      exact ⟨hp.symm ▸ p.2.2.1, hp.symm ▸ p.2.2.2⟩
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact Fin.ext hp.symm
  · intro a ha
    symm
    rw [btFareyFourier_eq_root]
    simp

private theorem btProgressionCoprimeShift (q a r z : ℕ) (S : Finset ℕ)
    (hr : 0 < r) (hqr : Nat.Coprime q r)
    (hprime : ∀ n ∈ S, (q * n + a).Prime)
    (hlarge : ∀ n ∈ S, z < q * n + a) (hrz : r ≤ z) :
    ∃ c : ℕ, ∀ n ∈ S, Nat.Coprime (n + c) r := by
  let c := (q⁻¹ : ZMod r).val * a
  refine ⟨c, ?_⟩
  intro n hnS
  have hcmod : q * c ≡ a [MOD r] := by
    apply (ZMod.natCast_eq_natCast_iff (q * c) a r).mp
    change ((q * ((q⁻¹ : ZMod r).val * a) : ℕ) : ZMod r) = (a : ZMod r)
    push_cast
    rw [← mul_assoc, show (q : ZMod r) * (q⁻¹ : ZMod r).val = 1 by
      exact ZMod.mul_val_inv hqr, one_mul]
  have hmod : q * (n + c) ≡ q * n + a [MOD r] := by
    rw [mul_add]
    exact hcmod.add_left (q * n)
  apply Nat.coprime_of_dvd
  intro p hp hpn hpr
  have hpz : p ≤ z := (Nat.le_of_dvd hr hpr).trans hrz
  have hpLeft : p ∣ q * (n + c) := dvd_mul_of_dvd_right hpn q
  have hpRight : p ∣ q * n + a := (hmod.dvd_iff hpr).mp hpLeft
  have hpeq : p = q * n + a :=
    (Nat.prime_dvd_prime_iff_eq hp (hprime n hnS)).mp hpRight
  have hbig := hlarge n hnS
  omega

private noncomputable def btRestrictedSieveDensity (N z q : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r q),
    ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
      (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)

private theorem btArithmeticLargeSieveOn (N z : ℕ) (hz : 0 < z)
    (D : Finset ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range N)
    (hlocal : ∀ r ∈ D,
      (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r) * S.card ^ 2 ≤
        ∑ p : btFareyIndex z,
          if p.1.2.1 = r then ‖btFareyFourier S p‖ ^ 2 else 0) :
    (∑ r ∈ D, ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
      (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)) *
        S.card ^ 2 ≤ S.card := by
  let w : ℕ → ℝ := fun r ↦ ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹
  have hsummed :
      (∑ r ∈ D, w r *
        (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)) *
          S.card ^ 2 ≤
        ∑ r ∈ D, w r * ∑ p : btFareyIndex z,
          if p.1.2.1 = r then ‖btFareyFourier S p‖ ^ 2 else 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro r hr
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hlocal r hr) (btSieveWeight_nonneg N z r)
  have hcollapse :
      (∑ r ∈ D, w r * ∑ p : btFareyIndex z,
        if p.1.2.1 = r then ‖btFareyFourier S p‖ ^ 2 else 0) =
      ∑ p : btFareyIndex z,
        if p.1.2.1 ∈ D then w p.1.2.1 * ‖btFareyFourier S p‖ ^ 2 else 0 := by
    calc
      (∑ r ∈ D, w r * ∑ p : btFareyIndex z,
          if p.1.2.1 = r then ‖btFareyFourier S p‖ ^ 2 else 0) =
          ∑ r ∈ D, ∑ p : btFareyIndex z,
            w r * (if p.1.2.1 = r then ‖btFareyFourier S p‖ ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
      _ = ∑ p : btFareyIndex z, ∑ r ∈ D,
          w r * (if p.1.2.1 = r then ‖btFareyFourier S p‖ ^ 2 else 0) :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : p.1.2.1 ∈ D
        · rw [ite_eq_left hp]
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq, hp, ite_true]
        · rw [ite_eq_right hp]
          apply Finset.sum_eq_zero
          intro r hr
          have hne : p.1.2.1 ≠ r := by
            intro heq
            exact hp (heq ▸ hr)
          simp [hne]
  rw [hcollapse] at hsummed
  have hsub :
      (∑ p : btFareyIndex z,
        if p.1.2.1 ∈ D then w p.1.2.1 * ‖btFareyFourier S p‖ ^ 2 else 0) ≤
      ∑ p : btFareyIndex z, w p.1.2.1 * ‖btFareyFourier S p‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro p _
    split_ifs
    · exact le_rfl
    · positivity
  have hlarge := btFareyLargeSieve N z hz
    (fun n ↦ if n ∈ S then (1 : ℂ) else 0)
  simp_rw [btIndicatorFourier S hS] at hlarge
  rw [btIndicatorNormSum S hS] at hlarge
  exact hsummed.trans (hsub.trans hlarge)

private theorem btProgressionLargeSieve (N z q a : ℕ) (hz : 0 < z)
    (S : Finset ℕ) (hS : S ⊆ Finset.range N)
    (hprime : ∀ n ∈ S, (q * n + a).Prime)
    (hlarge : ∀ n ∈ S, z < q * n + a) :
    btRestrictedSieveDensity N z q * S.card ^ 2 ≤ S.card := by
  let D := (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r q)
  have hlocal : ∀ r ∈ D,
      (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r) * S.card ^ 2 ≤
        ∑ p : btFareyIndex z,
          if p.1.2.1 = r then ‖btFareyFourier S p‖ ^ 2 else 0 := by
    intro r hrD
    have hrData := Finset.mem_filter.mp hrD
    have hr := (Finset.mem_Icc.mp hrData.1).1
    obtain ⟨c, hc⟩ := btProgressionCoprimeShift q a r z S (by omega)
      hrData.2.symm hprime hlarge (Finset.mem_Icc.mp hrData.1).2
    exact btFareyFiberFourierLower z r c S hrData.1 hc
  simpa only [btRestrictedSieveDensity, D] using
    btArithmeticLargeSieveOn N z hz D S hS hlocal

private noncomputable def btSquarefreeDivisorSum (q : ℕ) : ℝ :=
  ∑ d ∈ q.divisors.filter Squarefree, (Nat.totient d : ℝ)⁻¹

private theorem btSieveDensity_eq_squarefree (N z : ℕ) :
    btSieveDensity N z =
      ∑ r ∈ (Finset.Icc 1 z).filter Squarefree,
        ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ * (Nat.totient r : ℝ)⁻¹ := by
  rw [btSieveDensity]
  calc
    (∑ r ∈ Finset.Icc 1 z,
        ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
          (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)) =
        ∑ r ∈ Finset.Icc 1 z, if Squarefree r then
          ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ * (Nat.totient r : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hsq : Squarefree r
      · rw [ite_eq_left hsq]
        have hmu := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
        have hmuReal : (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2) = 1 := by
          have hcast := congrArg (fun n : ℤ ↦ (n : ℝ)) hmu
          norm_num at hcast
          rcases hcast with hcast | hcast
          · rw [hcast]
            norm_num
          · rw [hcast]
            norm_num
        rw [hmuReal]
        simp only [one_div]
      · rw [ite_eq_right hsq,
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
        norm_num
    _ = _ := by rw [Finset.sum_filter]

private theorem btRestrictedSieveDensity_eq_squarefree (N z q : ℕ) :
    btRestrictedSieveDensity N z q =
      ∑ r ∈ (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r q ∧ Squarefree r),
        ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ * (Nat.totient r : ℝ)⁻¹ := by
  rw [btRestrictedSieveDensity]
  calc
    (∑ r ∈ (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r q),
        ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
          (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)) =
        ∑ r ∈ (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r q),
          if Squarefree r then
            ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
              (Nat.totient r : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hsq : Squarefree r
      · rw [ite_eq_left hsq]
        have hmu := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
        have hmuReal : (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2) = 1 := by
          have hcast := congrArg (fun n : ℤ ↦ (n : ℝ)) hmu
          norm_num at hcast
          rcases hcast with hcast | hcast
          · rw [hcast]
            norm_num
          · rw [hcast]
            norm_num
        rw [hmuReal]
        simp only [one_div]
      · rw [ite_eq_right hsq,
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
        norm_num
    _ = ∑ r ∈ ((Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r q)).filter Squarefree,
          ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ * (Nat.totient r : ℝ)⁻¹ := by
      exact (Finset.sum_filter (s :=
        (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r q))
        (fun r : ℕ ↦ Squarefree r) (fun r : ℕ ↦
        ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ * (Nat.totient r : ℝ)⁻¹)).symm
    _ = _ := by
      apply Finset.sum_congr
      · ext r
        simp only [Finset.mem_filter, Finset.mem_Icc]
        tauto
      · intro r _
        rfl

private theorem btSieveDensity_le_divisor_mul_restricted (N z q : ℕ) (hq : 0 < q) :
    btSieveDensity N z ≤ btSquarefreeDivisorSum q * btRestrictedSieveDensity N z q := by
  rw [btSieveDensity_eq_squarefree, btRestrictedSieveDensity_eq_squarefree]
  unfold btSquarefreeDivisorSum
  let A := (Finset.Icc 1 z).filter Squarefree
  let D := q.divisors.filter Squarefree
  let R := (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r q ∧ Squarefree r)
  let e : ℕ → ℕ × ℕ := fun n ↦ (n.gcd q, n / n.gcd q)
  let f : ℕ → ℝ := fun n ↦
    ((N : ℝ) + 3 * (n : ℝ) * z / 2)⁻¹ * (Nat.totient n : ℝ)⁻¹
  let g : ℕ × ℕ → ℝ := fun p ↦
    (Nat.totient p.1 : ℝ)⁻¹ *
      (((N : ℝ) + 3 * (p.2 : ℝ) * z / 2)⁻¹ * (Nat.totient p.2 : ℝ)⁻¹)
  have he : Set.InjOn e (A : Set ℕ) := by
    intro m hm n hn hmn
    have hprod := congrArg (fun p : ℕ × ℕ ↦ p.1 * p.2) hmn
    simpa only [e, Nat.mul_div_cancel' (Nat.gcd_dvd_left m q),
      Nat.mul_div_cancel' (Nat.gcd_dvd_left n q)] using hprod
  have he_mem : Finset.image e A ⊆ D ×ˢ R := by
    rw [Finset.image_subset_iff]
    intro n hnA
    have hnData := Finset.mem_filter.mp hnA
    have hnRange := Finset.mem_Icc.mp hnData.1
    have hnpos : 0 < n := by omega
    have hgcdpos : 0 < n.gcd q := Nat.gcd_pos_of_pos_left q hnpos
    have hdivpos : 0 < n / n.gcd q :=
      Nat.div_pos (Nat.gcd_le_left q hnpos) hgcdpos
    have hdivle : n / n.gcd q ≤ n := Nat.div_le_self n (n.gcd q)
    simp only [Finset.mem_product, D, R, e, Finset.mem_filter, Nat.mem_divisors,
      Finset.mem_Icc]
    exact ⟨⟨⟨Nat.gcd_dvd_right n q, hq.ne'⟩,
      hnData.2.squarefree_of_dvd (Nat.gcd_dvd_left n q)⟩,
      ⟨⟨by omega, hdivle.trans hnRange.2⟩,
        Nat.coprime_div_gcd_of_squarefree hnData.2 hq.ne',
        hnData.2.squarefree_of_dvd ⟨n.gcd q, by
          rw [mul_comm, Nat.mul_div_cancel' (Nat.gcd_dvd_left n q)]⟩⟩⟩
  have hterm : ∀ n ∈ A, f n ≤ g (e n) := by
    intro n hnA
    have hnData := Finset.mem_filter.mp hnA
    have hnRange := Finset.mem_Icc.mp hnData.1
    have hnpos : 0 < n := by omega
    have hzpos : 0 < z := hnpos.trans_le hnRange.2
    have hgcdpos : 0 < n.gcd q := Nat.gcd_pos_of_pos_left q hnpos
    have hdivpos : 0 < n / n.gcd q :=
      Nat.div_pos (Nat.gcd_le_left q hnpos) hgcdpos
    have hprod : n.gcd q * (n / n.gcd q) = n :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left n q)
    have hcop : Nat.Coprime (n.gcd q) (n / n.gcd q) := by
      apply Nat.coprime_of_squarefree_mul
      rw [hprod]
      exact hnData.2
    have hw :
        ((N : ℝ) + 3 * (n : ℝ) * z / 2)⁻¹ ≤
          ((N : ℝ) + 3 * ((n / n.gcd q : ℕ) : ℝ) * z / 2)⁻¹ := by
      apply inv_anti₀
      · positivity
      · gcongr
        exact Nat.div_le_self n (n.gcd q)
    have hphi :
        (Nat.totient n : ℝ)⁻¹ =
          (Nat.totient (n.gcd q) : ℝ)⁻¹ *
            (Nat.totient (n / n.gcd q) : ℝ)⁻¹ := by
      calc
        (Nat.totient n : ℝ)⁻¹ =
            (Nat.totient (n.gcd q * (n / n.gcd q)) : ℝ)⁻¹ := by rw [hprod]
        _ = ((Nat.totient (n.gcd q) * Nat.totient (n / n.gcd q) : ℕ) : ℝ)⁻¹ := by
          rw [Nat.totient_mul hcop]
        _ = ((Nat.totient (n.gcd q) : ℝ) *
            Nat.totient (n / n.gcd q))⁻¹ := by push_cast; rfl
        _ = _ := mul_inv _ _
    dsimp only [f, g, e]
    rw [hphi]
    calc
      ((N : ℝ) + 3 * (n : ℝ) * z / 2)⁻¹ *
          ((Nat.totient (n.gcd q) : ℝ)⁻¹ *
            (Nat.totient (n / n.gcd q) : ℝ)⁻¹) ≤
        ((N : ℝ) + 3 * ((n / n.gcd q : ℕ) : ℝ) * z / 2)⁻¹ *
          ((Nat.totient (n.gcd q) : ℝ)⁻¹ *
            (Nat.totient (n / n.gcd q) : ℝ)⁻¹) := by
          exact mul_le_mul_of_nonneg_right hw (by positivity)
      _ = (Nat.totient (n.gcd q) : ℝ)⁻¹ *
          (((N : ℝ) + 3 * ((n / n.gcd q : ℕ) : ℝ) * z / 2)⁻¹ *
            (Nat.totient (n / n.gcd q) : ℝ)⁻¹) := by ring
  have hg : ∀ p ∈ D ×ˢ R, p ∉ Finset.image e A → 0 ≤ g p := by
    intro p _ _
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (by positivity))
  have hsum : (∑ n ∈ A, f n) ≤ ∑ p ∈ D ×ˢ R, g p :=
    Finset.sum_le_sum_of_injOn e he he_mem hterm hg
  change (∑ n ∈ A, f n) ≤
    (∑ d ∈ D, (Nat.totient d : ℝ)⁻¹) *
      ∑ r ∈ R,
        ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ * (Nat.totient r : ℝ)⁻¹
  refine hsum.trans_eq ?_
  rw [Finset.sum_product]
  simp only [g]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

private theorem btTotient_prod_primes (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    Nat.totient (∏ p ∈ s, p) = ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hcop : Nat.Coprime p (∏ a ∈ s, a) := by
        rw [Nat.coprime_prod_right_iff]
        intro a ha
        exact (Nat.coprime_primes (hs p (Finset.mem_insert_self p s))
          (hs a (Finset.mem_insert_of_mem ha))).mpr (by
            intro hpa
            subst a
            exact hp ha)
      rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.totient_mul hcop,
        Nat.totient_prime (hs p (Finset.mem_insert_self p s)), ih]
      intro a ha
      exact hs a (Finset.mem_insert_of_mem ha)

private theorem btSquarefreeDivisorSum_eq_primeFactors (q : ℕ) (hq : 0 < q) :
    btSquarefreeDivisorSum q =
      ∑ t ∈ q.primeFactors.powerset,
        ∏ p ∈ t, ((p : ℝ) - 1)⁻¹ := by
  unfold btSquarefreeDivisorSum
  rw [Nat.sum_divisors_filter_squarefree hq.ne', Nat.factors_eq]
  have hpf : (↑q.primeFactorsList : Multiset ℕ).toFinset = q.primeFactors := by
    ext p
    rw [Multiset.mem_toFinset, Multiset.mem_coe, ← List.mem_toFinset,
      Nat.toFinset_factors]
  rw [hpf]
  apply Finset.sum_congr rfl
  intro t ht
  have htq := Finset.mem_powerset.mp ht
  have htprime : ∀ p ∈ t, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactors (htq hp)
  rw [t.prod_val, Function.id_def, btTotient_prod_primes t htprime]
  calc
    (↑(∏ p ∈ t, (p - 1)) : ℝ)⁻¹ =
        (∏ p ∈ t, ((p : ℝ) - 1))⁻¹ := by
      congr 1
      push_cast
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (htprime p hp).one_le]
      norm_num
    _ = ∏ p ∈ t, ((p : ℝ) - 1)⁻¹ := by
      rw [Finset.prod_inv_distrib]

private theorem btSquarefreeDivisorSum_eq_prod (q : ℕ) (hq : 0 < q) :
    btSquarefreeDivisorSum q =
      ∏ p ∈ q.primeFactors, (1 + ((p : ℝ) - 1)⁻¹) := by
  rw [btSquarefreeDivisorSum_eq_primeFactors q hq]
  calc
    (∑ t ∈ q.primeFactors.powerset,
        ∏ p ∈ t, ((p : ℝ) - 1)⁻¹) =
        ∏ p ∈ q.primeFactors, (((p : ℝ) - 1)⁻¹ + 1) := by
      rw [Finset.prod_add]
      simp
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p _
      ring

private theorem btTotientEulerReal (q : ℕ) :
    (Nat.totient q : ℝ) =
      (q : ℝ) * ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun x : ℚ ↦ (x : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  norm_num at h
  exact h

private theorem btPrimeEulerFactors_mul {p : ℕ} (hp : p.Prime) :
    (1 + ((p : ℝ) - 1)⁻¹) * (1 - (p : ℝ)⁻¹) = 1 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  field_simp [hp0, hp1]
  ring

private theorem btSquarefreeDivisorSum_eq_totientRatio (q : ℕ) (hq : 0 < q) :
    btSquarefreeDivisorSum q = (q : ℝ) / Nat.totient q := by
  rw [btSquarefreeDivisorSum_eq_prod q hq]
  let A : ℝ := ∏ p ∈ q.primeFactors, (1 + ((p : ℝ) - 1)⁻¹)
  let B : ℝ := ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹)
  have hAB : A * B = 1 := by
    dsimp only [A, B]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    exact btPrimeEulerFactors_mul (Nat.prime_of_mem_primeFactors hp)
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hAB
    norm_num at hAB
  have hqReal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  change A = (q : ℝ) / Nat.totient q
  rw [btTotientEulerReal q]
  change A = (q : ℝ) / ((q : ℝ) * B)
  rw [eq_inv_of_mul_eq_one_left hAB]
  field_simp [hqReal, hB]

private theorem btSieveDensity_le_totientRatio_mul_restricted
    (N z q : ℕ) (hq : 0 < q) :
    btSieveDensity N z ≤
      ((q : ℝ) / Nat.totient q) * btRestrictedSieveDensity N z q := by
  rw [← btSquarefreeDivisorSum_eq_totientRatio q hq]
  exact btSieveDensity_le_divisor_mul_restricted N z q hq

private theorem btProgressionCard_mul_density (N z q a : ℕ) (hz : 0 < z)
    (hq : 0 < q) (S : Finset ℕ) (hS : S ⊆ Finset.range N)
    (hprime : ∀ n ∈ S, (q * n + a).Prime)
    (hlarge : ∀ n ∈ S, z < q * n + a) :
    btSieveDensity N z * S.card ^ 2 ≤
      ((q : ℝ) / Nat.totient q) * S.card := by
  have hden := btSieveDensity_le_totientRatio_mul_restricted N z q hq
  have hprog := btProgressionLargeSieve N z q a hz S hS hprime hlarge
  calc
    btSieveDensity N z * S.card ^ 2 ≤
        (((q : ℝ) / Nat.totient q) * btRestrictedSieveDensity N z q) *
          S.card ^ 2 := mul_le_mul_of_nonneg_right hden (sq_nonneg _)
    _ = ((q : ℝ) / Nat.totient q) *
        (btRestrictedSieveDensity N z q * S.card ^ 2) := by ring
    _ ≤ ((q : ℝ) / Nat.totient q) * S.card := by
      exact mul_le_mul_of_nonneg_left hprog (by positivity)

/--
**Arithmetic large sieve for primes in a progression.** Let $N$, $z$, $q$ and $a$ be natural
numbers with $z > 0$ and $q > 0$, and let $S$ be a finite set of natural numbers less than $N$
such that for every $n \in S$ the number $qn + a$ is prime and greater than $z$. Write $\mu$ for
the Möbius function and $\varphi$ for Euler's totient function. Then
$$
\left(\sum_{r=1}^{z} \frac{\mu(r)^2}{\varphi(r)\,(N + 3rz/2)}\right) |S|^2
\le \frac{q}{\varphi(q)}\,|S|.
$$

Source: Montgomery–Vaughan, *The large sieve* (1973), Corollary 1 and Lemma 3,
equations (2.7) and (3.2), lines 322–461. The Farey fractions are weighted by
the denominator-dependent spacing from `weightedLargeSieve`.
-/
public theorem arithmeticLargeSieve_progression (N z q a : ℕ) (hz : 0 < z)
    (hq : 0 < q) (S : Finset ℕ) (hS : S ⊆ Finset.range N)
    (hprime : ∀ n ∈ S, (q * n + a).Prime)
    (hlarge : ∀ n ∈ S, z < q * n + a) :
    (∑ r ∈ Finset.Icc 1 z,
        ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
          (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)) *
        S.card ^ 2 ≤ ((q : ℝ) / Nat.totient q) * S.card := by
  simpa only [btSieveDensity] using
    btProgressionCard_mul_density N z q a hz hq S hS hprime hlarge

end MathlibExt.NumberTheory.PrimeCounting
