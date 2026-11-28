/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.BinomialHarmonicExpansion
public import MathlibExt.NumberTheory.FermatQuotient
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A harmonic Fermat-quotient congruence

Over the field with `p` elements for a prime `p ≥ 5`, we compare derivatives of the finite
logarithm, finite dilogarithm, and a polynomial weighted by harmonic numbers. Bounds on
the degrees and evaluations at zero and one determine the integration constants.
At two the harmonic part with the lagged weight vanishes, and an integer binomial
expansion relates the finite logarithm to the Fermat quotient.

## References

* Chahinaze Djadi and Hacène Belbachir, *Congruence Properties for the Delannoy Triangle
  Coefficients*, Journal of Integer Sequences 29 (2026), Article 26.5.2, Lemma 7 and the
  vanishing harmonic sum at the end of the proof of Theorem 4.
-/

namespace MathlibExt.NumberTheory.DelannoyTriangleWanted

open Finset Polynomial

private noncomputable def finiteLog (p : ℕ) : (ZMod p)[X] :=
  ∑ i ∈ range (p - 1), C (((i + 1 : ℕ) : ZMod p)⁻¹) * X ^ (i + 1)

private noncomputable def finiteDilog (p : ℕ) : (ZMod p)[X] :=
  ∑ i ∈ range (p - 1), C ((((i + 1 : ℕ) : ZMod p)⁻¹) ^ 2) * X ^ (i + 1)

private theorem cast_index_ne_zero {p k : ℕ} (hk : 0 < k) (hkp : k < p) :
    (k : ZMod p) ≠ 0 := fun h =>
  Nat.not_dvd_of_pos_of_lt hk hkp ((ZMod.natCast_eq_zero_iff k p).mp h)

private theorem harmonicMod_succ (p n : ℕ) :
    harmonicMod p (n + 1) = harmonicMod p n + (((n + 1 : ℕ) : ZMod p)⁻¹) := by
  unfold harmonicMod
  rw [sum_Icc_succ_top (Nat.succ_pos n)]

private theorem sum_shift_to_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ range n, f (i + 1) = ∑ k ∈ Icc 1 n, f k := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]

private theorem sum_zmod_as_range (p : ℕ) [Fact p.Prime] (f : ZMod p → ZMod p) :
    ∑ x : ZMod p, f x = ∑ k ∈ range p, f (k : ZMod p) := by
  classical
  calc
    _ = ∑ i : Fin p, f ((i.val : ℕ) : ZMod p) := by
      symm
      refine sum_bij (fun i _ => (i.val : ZMod p)) (fun _ _ => mem_univ _) ?_ ?_ (fun _ _ => rfl)
      · intro a _ b _ h
        apply Fin.ext
        simpa only [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using
          congrArg ZMod.val h
      · intro a _
        exact ⟨⟨a.val, ZMod.val_lt a⟩, mem_univ _, ZMod.natCast_zmod_val a⟩
    _ = _ := Fin.sum_univ_eq_sum_range (fun k : ℕ => f (k : ZMod p)) p

private theorem sum_range_pred_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    {n : ℕ} (hn : 0 < n) (hzero : f 0 = 0) :
    ∑ k ∈ range n, f k = ∑ i ∈ range (n - 1), f (i + 1) := by
  conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ n by omega), sum_range_succ', hzero, add_zero]

private theorem harmonicMod_full (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    harmonicMod p (p - 1) = 0 := by
  have hp : 0 < p := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (cast_index_ne_zero (p := p) (k := 2) (by decide) (by omega))
  have h := Equiv.sum_comp (Equiv.neg (ZMod p)) (fun x => x⁻¹)
  simp only [Equiv.neg_apply, inv_neg, sum_neg_distrib] at h
  have hz : (∑ x : ZMod p, x⁻¹) = 0 := by
    apply (mul_eq_zero.mp (show (2 : ZMod p) * (∑ x : ZMod p, x⁻¹) = 0 by
      linear_combination -h)).resolve_left h2
  rw [sum_zmod_as_range p, sum_range_pred_succ (fun k : ℕ => (k : ZMod p)⁻¹) hp (by simp)] at hz
  rw [sum_shift_to_Icc (fun k : ℕ => (k : ZMod p)⁻¹)] at hz
  exact hz

private theorem finiteDilog_eval_one (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (finiteDilog p).eval 1 = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (cast_index_ne_zero (p := p) (k := 2) (by decide) (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := by
    exact_mod_cast (cast_index_ne_zero (p := p) (k := 3) (by decide) (by omega))
  have h := Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod p) h2) (fun x => x⁻¹ ^ 2)
  change ∑ x : ZMod p, (2 * x)⁻¹ ^ 2 = ∑ x : ZMod p, x⁻¹ ^ 2 at h
  simp only [mul_inv_rev, mul_pow, mul_comm _ ((2 : ZMod p)⁻¹ ^ 2), ← mul_sum] at h
  have hmul : (2 : ZMod p) ^ 2 * ((2 : ZMod p)⁻¹ ^ 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ h2, one_pow]
  have hz : (∑ x : ZMod p, x⁻¹ ^ 2) = 0 := by
    apply (mul_eq_zero.mp (show (3 : ZMod p) * (∑ x : ZMod p, x⁻¹ ^ 2) = 0 by
      linear_combination -(2 : ZMod p) ^ 2 * h +
        (∑ x : ZMod p, x⁻¹ ^ 2) * hmul)).resolve_left h3
  rw [sum_zmod_as_range p,
    sum_range_pred_succ (fun k : ℕ => (k : ZMod p)⁻¹ ^ 2) (by omega) (by simp)] at hz
  rw [finiteDilog, eval_finsetSum]
  simpa only [eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one] using hz

private theorem finiteDilog_eval_neg_one (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (finiteDilog p).eval (-1) = 0 := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (cast_index_ne_zero (p := p) (k := 2) (by decide) (by omega))
  let f (i : ℕ) := (((i + 1 : ℕ) : ZMod p)⁻¹) ^ 2 * (-1 : ZMod p) ^ (i + 1)
  have href : ∀ i ∈ range (p - 1), f (p - 1 - 1 - i) = -f i := by
    intro i hi
    have hip := mem_range.mp hi
    have hidx : p - 1 - 1 - i + 1 = p - (i + 1) := by omega
    have hc : ((p - (i + 1) : ℕ) : ZMod p) = -((i + 1 : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (by omega : i + 1 ≤ p), ZMod.natCast_self, zero_sub]
    have hpow : (-1 : ZMod p) ^ (p - (i + 1)) = -((-1 : ZMod p) ^ (i + 1)) := by
      let a : ZMod p := (-1) ^ (i + 1)
      have ha : a * a = 1 := by
        dsimp [a]
        rw [← mul_pow]
        simp
      have hm : (-1 : ZMod p) ^ (p - (i + 1)) * a = -1 := by
        dsimp [a]
        rw [← pow_add, Nat.sub_add_cancel (by omega), (hp.odd_of_ne_two (by omega)).neg_one_pow]
      calc
        _ = (-1 : ZMod p) ^ (p - (i + 1)) * (a * a) := by rw [ha, mul_one]
        _ = -a := by rw [← mul_assoc, hm, neg_one_mul]
    dsimp only [f]
    rw [hidx, hc, inv_neg, neg_sq, hpow, mul_neg]
  have h := sum_range_reflect f (p - 1)
  simp_rw [show (∑ i ∈ range (p - 1), f (p - 1 - 1 - i)) =
      ∑ i ∈ range (p - 1), -f i from sum_congr rfl href, sum_neg_distrib] at h
  have hz : (∑ i ∈ range (p - 1), f i) = 0 := by
    apply (mul_eq_zero.mp (show (2 : ZMod p) * (∑ i ∈ range (p - 1), f i) = 0 by
      linear_combination -h)).resolve_left h2
  rw [finiteDilog, eval_finsetSum]
  simpa only [eval_mul, eval_C, eval_pow, eval_X, f] using hz

private noncomputable def finiteHarmonic (p : ℕ) : (ZMod p)[X] :=
  ∑ i ∈ range (p - 1), C (harmonicMod p i * (((i + 1 : ℕ) : ZMod p)⁻¹)) * X ^ (i + 1)

private theorem harmonic_poly_telescope (p n : ℕ) :
    (1 - X) * (∑ i ∈ range (n + 1), C (harmonicMod p i) * X ^ i) =
      (∑ i ∈ range n, C (((i + 1 : ℕ) : ZMod p)⁻¹) * X ^ (i + 1)) -
        C (harmonicMod p n) * X ^ (n + 1) := by
  induction n with
  | zero => simp [harmonicMod]
  | succ n ih =>
    rw [sum_range_succ (fun i => C (harmonicMod p i) * X ^ i), mul_add, ih,
      sum_range_succ (fun i => C (((i + 1 : ℕ) : ZMod p)⁻¹) * X ^ (i + 1)),
      harmonicMod_succ p n, map_add, pow_succ X (n + 1)]
    ring

private theorem finiteHarmonic_derivative (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (1 - X) * (finiteHarmonic p).derivative = finiteLog p := by
  have hsum : (finiteHarmonic p).derivative = ∑ i ∈ range (p - 1), C (harmonicMod p i) * X ^ i := by
    rw [finiteHarmonic, derivative_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.mp hi
    have hn := cast_index_ne_zero (p := p) (k := i + 1) (by omega) (by omega)
    rw [derivative_C_mul_X_pow, Nat.add_sub_cancel, mul_assoc, inv_mul_cancel₀ hn, mul_one]
  have hn : p - 2 + 1 = p - 1 := by omega
  have hlast : harmonicMod p (p - 2) = -(((p - 2 + 1 : ℕ) : ZMod p)⁻¹) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← harmonicMod_succ p (p - 2), hn, harmonicMod_full p hp5]
  conv_lhs => rw [hsum, ← hn, harmonic_poly_telescope, hlast, map_neg, neg_mul,
    sub_neg_eq_add, ← sum_range_succ, hn]
  rfl

private theorem finiteHarmonic_degree_lt (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (finiteHarmonic p).natDegree < p := by
  unfold finiteHarmonic
  apply lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ ?_) (show p - 1 < p by omega)
  intro i hi
  exact (natDegree_C_mul_X_pow_le _ _).trans (by simpa using mem_range.mp hi)

private theorem finiteLog_natDegree_le (p : ℕ) : (finiteLog p).natDegree ≤ p - 1 := by
  unfold finiteLog
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_C_mul_X_pow_le _ _).trans (by simpa using Nat.succ_le_of_lt (mem_range.mp hi))

private theorem finiteDilog_natDegree_le (p : ℕ) : (finiteDilog p).natDegree ≤ p - 1 := by
  unfold finiteDilog
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_C_mul_X_pow_le _ _).trans (by simpa using Nat.succ_le_of_lt (mem_range.mp hi))

private theorem one_sub_X_natDegree_le (p : ℕ) [Fact p.Prime] :
    (1 - X : (ZMod p)[X]).natDegree ≤ 1 := by
  simpa using (natDegree_sub_le (1 : (ZMod p)[X]) X)

private theorem finiteDilog_comp_one_sub_X_natDegree_le (p : ℕ) [Fact p.Prime] :
    ((finiteDilog p).comp (1 - X)).natDegree ≤ p - 1 :=
  natDegree_comp_le.trans (by
    simpa using Nat.mul_le_mul (finiteDilog_natDegree_le p) (one_sub_X_natDegree_le p))

private theorem natCast_ne_zero_of_mem_range (p i : ℕ) (hi : i ∈ range (p - 1)) :
    ((i + 1 : ℕ) : ZMod p) ≠ 0 := by
  intro hz
  have hle := Nat.le_of_dvd (Nat.succ_pos i) ((ZMod.natCast_eq_zero_iff (i + 1) p).mp hz)
  have hlt := mem_range.mp hi
  omega

private theorem finiteLog_derivative (p : ℕ) [Fact p.Prime] :
    (finiteLog p).derivative = ∑ i ∈ range (p - 1), X ^ i := by
  rw [finiteLog, derivative_sum]
  apply sum_congr rfl
  intro i hi
  rw [derivative_C_mul_X_pow, inv_mul_cancel₀ (natCast_ne_zero_of_mem_range p i hi)]
  simp

private theorem one_sub_X_mul_finiteLog_derivative (p : ℕ) [Fact p.Prime] :
    (1 - X) * (finiteLog p).derivative = 1 - X ^ (p - 1) := by
  rw [finiteLog_derivative, mul_comm]
  exact geom_sum_mul_neg _ _

private theorem X_mul_finiteDilog_derivative (p : ℕ) [Fact p.Prime] (_hp5 : 5 ≤ p) :
    X * (finiteDilog p).derivative = finiteLog p := by
  rw [finiteDilog, derivative_sum, mul_sum, finiteLog]
  apply sum_congr rfl
  intro i hi
  rw [derivative_C_mul_X_pow, pow_two, mul_assoc,
    inv_mul_cancel₀ (natCast_ne_zero_of_mem_range p i hi), mul_one, Nat.add_sub_cancel]
  rw [← mul_assoc, mul_comm X, mul_assoc, ← pow_succ']

private theorem finiteLog_eval_zero (p : ℕ) : (finiteLog p).eval 0 = 0 := by
  change evalRingHom 0 (∑ i ∈ range (p - 1), _) = 0
  rw [map_sum]
  simp

private theorem coeff_eq_of_derivative_eq_of_not_dvd (p : ℕ) [Fact p.Prime]
    {f g : (ZMod p)[X]} (h : f.derivative = g.derivative) {n : ℕ} (hn : ¬ p ∣ n) :
    f.coeff n = g.coeff n := by
  cases n with
  | zero => exact (hn (dvd_zero p)).elim
  | succ k =>
    have hk : ((k : ZMod p) + 1) ≠ 0 := by
      rw [← Nat.cast_succ]
      exact fun hz => hn ((ZMod.natCast_eq_zero_iff _ p).mp hz)
    have hc := congrArg (fun q : (ZMod p)[X] => q.coeff k) h
    simpa only [coeff_derivative] using mul_right_cancel₀ hk (by
      simpa only [coeff_derivative] using hc :
      f.coeff (k + 1) * ((k : ZMod p) + 1) = g.coeff (k + 1) * ((k : ZMod p) + 1))

private theorem eq_of_derivative_eq_of_natDegree_lt (p : ℕ) [Fact p.Prime]
    {f g : (ZMod p)[X]} (hf : f.natDegree < p) (hg : g.natDegree < p)
    (hd : f.derivative = g.derivative) (h0 : f.eval 0 = g.eval 0) : f = g := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro n
  obtain rfl | hn := eq_or_ne n 0
  · simpa only [coeff_zero_eq_eval_zero] using h0
  by_cases hnp : n < p
  · exact coeff_eq_of_derivative_eq_of_not_dvd p hd
      (fun h => hn (Nat.eq_zero_of_dvd_of_lt h hnp))
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < n),
        coeff_eq_zero_of_natDegree_lt (by omega : g.natDegree < n)]

private theorem eq_of_derivative_eq_of_natDegree_lt_twice (p : ℕ) [Fact p.Prime]
    {f g : (ZMod p)[X]} (hf : f.natDegree < 2 * p) (hg : g.natDegree < 2 * p)
    (hd : f.derivative = g.derivative) (h0 : f.eval 0 = g.eval 0)
    (h1 : f.eval 1 = g.eval 1) : f = g := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let q := f - g
  have hq : q.natDegree < 2 * p := (natDegree_sub_le f g).trans_lt (max_lt hf hg)
  have hqd : q.derivative = 0 := by simp [q, hd]
  have hq0 : q.eval 0 = 0 := by simp [q, h0]
  have hq1 : q.eval 1 = 0 := by simp [q, h1]
  have hshape : q = C (q.coeff p) * X ^ p := by
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro n
    rw [coeff_C_mul_X_pow]
    obtain rfl | hnp := eq_or_ne n p
    · simp
    rw [ite_eq_right hnp]
    obtain rfl | hn0 := eq_or_ne n 0
    · simpa only [coeff_zero_eq_eval_zero] using hq0
    by_cases hn : n < 2 * p
    · have hnd : ¬ p ∣ n := by
        rintro ⟨k, rfl⟩
        have hk0 : k ≠ 0 := by intro hk; simp [hk] at hn0
        have hk1 : k ≠ 1 := by intro hk; simp [hk] at hnp
        have hle := Nat.mul_le_mul_left p (show 2 ≤ k by omega)
        rw [Nat.mul_comm p 2] at hle
        omega
      simpa using coeff_eq_of_derivative_eq_of_not_dvd p (g := 0) (by simpa using hqd) hnd
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hc : q.coeff p = 0 := by
    have he := congrArg (Polynomial.eval 1) hshape
    simpa [hq1] using he.symm
  exact sub_eq_zero.mp (show q = 0 by rw [hshape, hc]; simp)

private theorem one_sub_X_pow (p : ℕ) [Fact p.Prime] :
    (1 - X : (ZMod p)[X]) ^ p = 1 - X ^ p := by
  rw [sub_pow_char, one_pow]

private theorem one_sub_X_ne_zero (p : ℕ) [Fact p.Prime] : (1 - X : (ZMod p)[X]) ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval 0) h
  simp at he

private theorem two_ne_zero_zmod (p : ℕ) (hp5 : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  simpa using natCast_ne_zero_of_mem_range p 1 (mem_range.mpr (by omega))

private theorem finiteLog_symm (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (finiteLog p).comp (1 - X) = finiteLog p := by
  let L := finiteLog p
  let B : (ZMod p)[X] := 1 - X
  have hpos : p - 1 + 1 = p := by omega
  have hgeom : B * L.derivative = 1 - X ^ (p - 1) := one_sub_X_mul_finiteLog_derivative p
  have hflip : X * L.derivative.comp B = 1 - B ^ (p - 1) := by
    have h := congrArg (fun q : (ZMod p)[X] => q.comp B) hgeom
    have hB : B.comp B = X := by simp [B]
    simpa only [mul_comp, hB, sub_comp, one_comp, pow_comp, X_comp] using h
  have hsum : L.derivative + L.derivative.comp B = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero (X_ne_zero : (X : (ZMod p)[X]) ≠ 0) (one_sub_X_ne_zero p))
    calc
      X * B * (L.derivative + L.derivative.comp B) =
          X * (B * L.derivative) + B * (X * L.derivative.comp B) := by ring
      _ = X * (1 - X ^ (p - 1)) + B * (1 - B ^ (p - 1)) := by rw [hgeom, hflip]
      _ = X + B - X ^ p - B ^ p := by
        have hx : X * (X : (ZMod p)[X]) ^ (p - 1) = X ^ p := by rw [← pow_succ', hpos]
        have hb : B * B ^ (p - 1) = B ^ p := by rw [← pow_succ', hpos]
        rw [mul_sub, mul_sub, mul_one, mul_one, hx, hb]
        ring
      _ = X * B * 0 := by rw [show B ^ p = 1 - X ^ p from one_sub_X_pow p]; dsimp [B]; ring
  have hd : (L.comp B).derivative = L.derivative := by
    rw [derivative_comp, show B.derivative = -1 by simp [B], neg_one_mul]
    linear_combination -hsum
  have hL : L.natDegree < p := (finiteLog_natDegree_le p).trans_lt (by omega)
  have hLB : (L.comp B).natDegree < p := natDegree_comp_le.trans_lt (by
    have hB : B.natDegree ≤ 1 := one_sub_X_natDegree_le p
    have h := Nat.mul_le_mul_left L.natDegree hB
    rw [Nat.mul_one] at h
    exact h.trans_lt hL)
  have hoff : L.comp B = L + C (L.eval 1) := by
    apply eq_of_derivative_eq_of_natDegree_lt p hLB
    · exact (natDegree_add_le (p := L) (q := C (L.eval 1))).trans_lt (by simpa using hL)
    · simpa using hd
    · simp [eval_comp, B, L, finiteLog_eval_zero]
  have hval : L.eval 1 = 0 := by
    have he : (0 : ZMod p) = L.eval 1 + L.eval 1 := by
      simpa [eval_comp, B, L, finiteLog_eval_zero] using congrArg (Polynomial.eval 1) hoff
    have hz : (2 : ZMod p) * L.eval 1 = 0 := by rw [two_mul]; exact he.symm
    exact (mul_eq_zero.mp hz).resolve_left (two_ne_zero_zmod p hp5)
  change L.comp B = L
  simpa [hval] using hoff

private theorem finiteLog_square (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (h1 : (finiteDilog p).eval 1 = 0) :
    C ((2 : ZMod p)⁻¹) * (finiteLog p) ^ 2 =
      -X ^ p * finiteDilog p - (1 - X ^ p) * (finiteDilog p).comp (1 - X) := by
  let L := finiteLog p
  let D := finiteDilog p
  let B : (ZMod p)[X] := 1 - X
  let E := D.comp B
  change C ((2 : ZMod p)⁻¹) * L ^ 2 = -X ^ p * D - (1 - X ^ p) * E
  have hL0 : L.eval 0 = 0 := finiteLog_eval_zero p
  have hL1 : L.eval 1 = 0 := by
    have h := congrArg (Polynomial.eval 0) (finiteLog_symm p hp5)
    simpa [eval_comp, L, finiteLog_eval_zero] using h
  have hD : X * D.derivative = L := X_mul_finiteDilog_derivative p hp5
  have hE : B * E.derivative = -L := by
    have h := congrArg (fun q : (ZMod p)[X] => q.comp B) hD
    have hc : B * D.derivative.comp B = L := by
      simpa only [mul_comp, X_comp, show L.comp B = L from finiteLog_symm p hp5] using h
    change B * (D.comp B).derivative = -L
    rw [derivative_comp, show B.derivative = -1 by simp [B], neg_one_mul, mul_neg, hc]
  have hgeom : X * B * L.derivative = X - X ^ p := by
    have hp : p - 1 + 1 = p := by omega
    rw [mul_assoc, show B * L.derivative = 1 - X ^ (p - 1) from
      one_sub_X_mul_finiteLog_derivative p, mul_sub, mul_one, ← pow_succ', hp]
  have hpow : (X ^ p : (ZMod p)[X]).derivative = 0 := by
    rw [derivative_X_pow, ZMod.natCast_self, map_zero, zero_mul]
  have hleft : (C ((2 : ZMod p)⁻¹) * L ^ 2).derivative = L * L.derivative := by
    rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_pow]
    rw [show (2 - 1 : ℕ) = 1 by decide, pow_one, ← mul_assoc, ← mul_assoc, ← map_mul]
    norm_num only [Nat.cast_ofNat]
    rw [inv_mul_cancel₀ (two_ne_zero_zmod p hp5), map_one, one_mul]
  have hright : (-X ^ p * D - (1 - X ^ p) * E).derivative =
      -X ^ p * D.derivative - (1 - X ^ p) * E.derivative := by
    simp [derivative_sub, derivative_mul, derivative_neg, hpow]
  refine eq_of_derivative_eq_of_natDegree_lt_twice p ?_ ?_ ?_ ?_ ?_
  · have hdeg : L.natDegree ≤ p - 1 := finiteLog_natDegree_le p
    have hb : (L ^ 2).natDegree ≤ 2 * L.natDegree := natDegree_pow_le
    exact (natDegree_C_mul_le _ _).trans_lt (hb.trans_lt (by omega))
  · have hdeg : D.natDegree ≤ p - 1 := finiteDilog_natDegree_le p
    have hedeg : E.natDegree ≤ p - 1 := finiteDilog_comp_one_sub_X_natDegree_le p
    have hbase : (1-X ^ p : (ZMod p)[X]).natDegree ≤ p := by
      simpa using (natDegree_sub_le (1 : (ZMod p)[X]) (X ^ p))
    apply (natDegree_sub_le _ _).trans_lt (max_lt _ _)
    · apply natDegree_mul_le.trans_lt
      rw [natDegree_neg, natDegree_X_pow]
      omega
    · exact natDegree_mul_le.trans_lt (by omega)
  · rw [hleft, hright]
    apply mul_left_cancel₀ (mul_ne_zero (X_ne_zero : (X : (ZMod p)[X]) ≠ 0) (one_sub_X_ne_zero p))
    rw [← show B ^ p = 1 - X ^ p from one_sub_X_pow p]
    calc
      X * B * (L * L.derivative) = L * (X * B * L.derivative) := by ring
      _ = L * (X - X ^ p) := by rw [hgeom]
      _ = -(B * X ^ p) * (X * D.derivative) - (X * B ^ p) * (B * E.derivative) := by
        rw [hD, hE, show B ^ p = 1 - X ^ p from one_sub_X_pow p]
        dsimp [B]
        ring
      _ = X * B * (-X ^ p * D.derivative - B ^ p * E.derivative) := by ring
  · have hp : p ≠ 0 := by omega
    simp [E, B, eval_comp, hL0, show D.eval 1 = 0 from h1, zero_pow hp]
  · simp [hL1, show D.eval 1 = 0 from h1]


private def binomialQuotient (p j : ℕ) : ℕ := p.choose (j + 1) / p

private theorem not_dvd_succ_of_lt_pred {p j : ℕ} (hj : j < p - 1) : ¬ p ∣ j + 1 :=
  fun hd => (not_le_of_gt (show j + 1 < p by omega)) (Nat.le_of_dvd (Nat.succ_pos j) hd)

private theorem binomialQuotient_spec (p : ℕ) (hp : p.Prime) {j : ℕ} (hj : j < p - 1) :
    binomialQuotient p j * p = p.choose (j + 1) ∧
    binomialQuotient p j * (j + 1) = (p - 1).choose j := by
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
  have hchoose : p.choose (j + 1) * (j + 1) = (p - 1).choose j * p := by
    conv_lhs => rw [← hpred, Nat.choose_succ_succ]
    rw [add_mul, Nat.choose_succ_right_eq, ← Nat.mul_add]
    rw [show j + 1 + (p - 1 - j) = p by omega]
  have hd : p ∣ p.choose (j + 1) :=
    (hp.dvd_mul.mp (hchoose ▸ dvd_mul_left p ((p - 1).choose j))).resolve_right
      (not_dvd_succ_of_lt_pred hj)
  have hq : binomialQuotient p j * p = p.choose (j + 1) := Nat.div_mul_cancel hd
  refine ⟨hq, Nat.mul_right_cancel hp.pos ?_⟩
  calc
    binomialQuotient p j * (j + 1) * p = (binomialQuotient p j * p) * (j + 1) := by ring
    _ = (p - 1).choose j * p := by rw [hq, hchoose]

private theorem choose_pred_mod (p : ℕ) (hp : p.Prime) {j : ℕ} (hj : j ≤ p - 1) :
    (((p - 1).choose j : ℕ) : ZMod p) = (-1 : ZMod p) ^ j := by
  let : Fact p.Prime := ⟨hp⟩
  induction j with
  | zero => simp
  | succ j ih =>
    have hn : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact not_dvd_succ_of_lt_pred (by omega)
    have hc := congrArg (fun a : ℕ => (a : ZMod p)) (Nat.choose_succ_right_eq (p - 1) j)
    simp only [Nat.cast_mul] at hc
    have hsum : ((p - 1 - j : ℕ) : ZMod p) + ((j + 1 : ℕ) : ZMod p) = 0 := by
      rw [← Nat.cast_add, show (p - 1 - j) + (j + 1) = p by omega, ZMod.natCast_self]
    have hs : ((p - 1 - j : ℕ) : ZMod p) = -((j + 1 : ℕ) : ZMod p) := by
      calc
        _ = ((p - 1 - j : ℕ) : ZMod p) + ((j + 1 : ℕ) : ZMod p) -
            ((j + 1 : ℕ) : ZMod p) := by ring
        _ = _ := by rw [hsum, zero_sub]
    apply mul_right_cancel₀ hn
    rw [hc, hs, ih (by omega), pow_succ]
    ring

private theorem signed_binomialQuotient_mod (p : ℕ) (hp : p.Prime) {j : ℕ}
    (hj : j < p - 1) :
    (-1 : ZMod p) ^ j * (binomialQuotient p j : ZMod p) =
      (((j + 1 : ℕ) : ZMod p))⁻¹ := by
  let : Fact p.Prime := ⟨hp⟩
  have hn : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact not_dvd_succ_of_lt_pred hj
  have hq := congrArg (fun a : ℕ => (a : ZMod p)) (binomialQuotient_spec p hp hj).2
  simp only [Nat.cast_mul] at hq
  apply mul_right_cancel₀ hn
  rw [inv_mul_cancel₀ hn, mul_assoc, hq, choose_pred_mod p hp (Nat.le_of_lt hj), ← mul_pow]
  simp

private theorem signed_binomialQuotient_sum (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (h2p : IsCoprime (2 : ℤ) (p : ℤ)) :
    (∑ j ∈ range (p - 1), (-1 : ℤ) ^ j * (binomialQuotient p j : ℤ) * 2 ^ (j + 1)) =
      -2 * Int.fermatQuotient p hp 2 h2p := by
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  -- Expand (1 - 2)^p and remove the terms of degree zero and p.
  let f (k : ℕ) : ℤ := (-2) ^ k * (p.choose k : ℤ)
  have hbin : (∑ k ∈ range (p + 1), f k) = -1 := by
    have h := add_pow (-2 : ℤ) 1 p
    rw [show (-2 : ℤ) + 1 = -1 by norm_num, hodd.neg_pow] at h
    simpa [f] using h.symm
  have hsplit := Finset.sum_range_succ' f (p - 1)
  rw [hpred] at hsplit
  rw [Finset.sum_range_succ, hsplit] at hbin
  have hf0 : f 0 = 1 := by simp [f]
  have hfp : f p = -(2 : ℤ) ^ p := by simp [f, hodd.neg_pow]
  rw [hf0, hfp] at hbin
  have hmid : (∑ j ∈ range (p - 1), f (j + 1)) = (2 : ℤ) ^ p - 2 := by omega
  -- Cancel p over the integers, before reducing modulo p.
  apply mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)
  calc
    _ = ∑ j ∈ range (p - 1), -f (j + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hq : (p : ℤ) * (binomialQuotient p j : ℤ) = (p.choose (j + 1) : ℤ) := by
        rw [mul_comm]
        exact_mod_cast (binomialQuotient_spec p hp (Finset.mem_range.mp hj)).1
      have hs : (-2 : ℤ) ^ (j + 1) = -((-1 : ℤ) ^ j * 2 ^ (j + 1)) := by
        calc
          _ = ((-1 : ℤ) * 2) ^ (j + 1) := by norm_num
          _ = _ := by rw [mul_pow, pow_succ (-1 : ℤ)]; ring
      dsimp [f]
      rw [hs]
      calc
        _ = (-1 : ℤ) ^ j * ((p : ℤ) * (binomialQuotient p j : ℤ)) * 2 ^ (j + 1) := by ring
        _ = _ := by rw [hq]; ring
    _ = -(∑ j ∈ range (p - 1), f (j + 1)) := Finset.sum_neg_distrib (fun j => f (j + 1))
    _ = (p : ℤ) * (-2 * Int.fermatQuotient p hp 2 h2p) := by
      have hpow : (2 : ℤ) ^ p = 2 ^ (p - 1) * 2 :=
        (congrArg (fun n : ℕ => (2 : ℤ) ^ n) hpred.symm).trans (pow_succ _ _)
      rw [hmid, hpow, ← mul_left_comm, Int.natCast_mul_fermatQuotient]
      ring

private theorem finiteLog_eval_two (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (h2p : IsCoprime (2 : ℤ) (p : ℤ)) :
    (finiteLog p).eval 2 = -2 * (Int.fermatQuotient p hp 2 h2p : ZMod p) := by
  have h := congrArg (fun a : ℤ => (a : ZMod p)) (signed_binomialQuotient_sum p hp hp5 h2p)
  push_cast at h
  calc
    (finiteLog p).eval 2 =
        ∑ j ∈ range (p - 1), (((j + 1 : ℕ) : ZMod p))⁻¹ * 2 ^ (j + 1) := by
      simp [finiteLog, Polynomial.eval_finsetSum]
    _ = _ := by
      convert h using 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [signed_binomialQuotient_mod p hp (Finset.mem_range.mp hj)]

private theorem finiteHarmonic_eq_neg_comp (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    finiteHarmonic p = -((finiteDilog p).comp (1 - X)) := by
  apply eq_of_derivative_eq_of_natDegree_lt p (finiteHarmonic_degree_lt p hp5)
  · rw [natDegree_neg]
    exact (finiteDilog_comp_one_sub_X_natDegree_le p).trans_lt (by omega)
  · apply mul_left_cancel₀ (one_sub_X_ne_zero p)
    rw [finiteHarmonic_derivative p hp5, derivative_neg, derivative_comp_one_sub_X, neg_neg]
    have h := congrArg (fun f : (ZMod p)[X] => f.comp (1 - X))
      (X_mul_finiteDilog_derivative p hp5)
    simpa only [mul_comp, X_comp, finiteLog_symm p hp5] using h.symm
  · simp [finiteHarmonic, eval_finsetSum, eval_comp, finiteDilog_eval_one p hp5]

/-- **The lagged harmonic sum at two vanishes modulo $p$.** For any prime $p \ge 5$, write
$H_j = \sum_{i=1}^j i^{-1}$ in $\mathbb{Z}/p\mathbb{Z}$. Then
$\sum_{j=0}^{p-2} H_j\,2^{j+1}/(j+1) = 0$ in $\mathbb{Z}/p\mathbb{Z}$.

Source: Chahinaze Djadi and Hacène Belbachir, *Congruence Properties for the Delannoy Triangle
Coefficients*, vanishing sum at the end of the proof of Theorem 4. -/
public theorem sum_lagged_harmonic_two_pow_div_eq_zero (p : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ j ∈ range (p - 1), harmonicMod p j * (2 : ZMod p) ^ (j + 1) *
      ((j + 1 : ℕ) : ZMod p)⁻¹) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have h : (finiteHarmonic p).eval 2 = 0 := by
    rw [finiteHarmonic_eq_neg_comp p hp5, eval_neg, eval_comp]
    simp [show (1 : ZMod p) - 2 = -1 by ring, finiteDilog_eval_neg_one p hp5]
  rw [finiteHarmonic, eval_finsetSum] at h
  simpa only [eval_mul, eval_C, eval_pow, eval_X, mul_right_comm] using h

private theorem harmonicSum_eq_evals (p : ℕ) :
    (∑ k ∈ Icc 1 (p - 1), harmonicMod p k * (2 : ZMod p) ^ k * (k : ZMod p)⁻¹) =
      (finiteHarmonic p).eval 2 + (finiteDilog p).eval 2 := by
  rw [← sum_shift_to_Icc (fun k : ℕ => harmonicMod p k * (2 : ZMod p) ^ k * (k : ZMod p)⁻¹),
    finiteHarmonic, finiteDilog, eval_finsetSum, eval_finsetSum, ← sum_add_distrib]
  refine sum_congr rfl (fun i _ => ?_)
  simp only [harmonicMod_succ, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- **Sum of $H_k 2^k / k$ over $1 \le k \le p - 1$ modulo $p$.** Let $p \ge 5$ be a prime, let
$q_p(2) = (2^{p-1} - 1)/p$ be the Fermat quotient of $2$, and let $H_k = \sum_{i=1}^{k} 1/i$
be the harmonic number modulo $p$, where $1/i$ is the inverse of $i$ modulo $p$. Then
$$\sum_{k=1}^{p-1} \frac{H_k\, 2^k}{k} \equiv -q_p(2)^2 \pmod{p}.$$

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Lemma 7. -/
public theorem sum_harmonic_two_pow_div (p : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (h2p : IsCoprime (2 : ℤ) (p : ℤ)) :
    (∑ k ∈ Finset.Icc 1 (p - 1),
        harmonicMod p k * (2 : ZMod p) ^ k * (k : ZMod p)⁻¹) =
      -((Int.fermatQuotient p hp 2 h2p : ZMod p)) ^ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let q : ZMod p := Int.fermatQuotient p hp 2 h2p
  have hlog : (finiteLog p).eval 2 = -2 * q := finiteLog_eval_two p hp hp5 h2p
  have hneg := finiteDilog_eval_neg_one p hp5
  have htwo := congrArg (Polynomial.eval (2 : ZMod p))
    (finiteLog_square p hp5 (finiteDilog_eval_one p hp5))
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_neg, eval_X, eval_one, eval_comp,
    ZMod.pow_card, show (1 : ZMod p) - 2 = -1 by ring, hlog, hneg, mul_zero, sub_zero] at htwo
  have halgebra : (2 : ZMod p)⁻¹ * (-2 * q) ^ 2 = 2 * q ^ 2 := by
    calc
      _ = ((2 : ZMod p)⁻¹ * 2) * (2 * q ^ 2) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (two_ne_zero_zmod p hp5), one_mul]
  rw [halgebra] at htwo
  have hdilog : (finiteDilog p).eval 2 = -(q ^ 2) := by
    apply mul_left_cancel₀ (two_ne_zero_zmod p hp5)
    calc
      (2 : ZMod p) * (finiteDilog p).eval 2 = -(2 * q ^ 2) := by
        rw [htwo]
        ring
      _ = _ := by ring
  rw [harmonicSum_eq_evals, finiteHarmonic_eq_neg_comp p hp5, eval_neg, eval_comp]
  simp [hdilog, hneg, show (1 : ZMod p) - 2 = -1 by ring, q]

end MathlibExt.NumberTheory.DelannoyTriangleWanted
