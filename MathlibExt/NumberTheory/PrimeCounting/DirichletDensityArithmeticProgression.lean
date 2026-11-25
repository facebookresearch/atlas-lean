/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Dirichlet density of primes in an arithmetic progression

Relative Dirichlet density of the primes in one reduced residue class.
-/

open Topology Filter

open Complex LSeries

private lemma LSeries_ofReal_eq_ofReal_tsum_rpow (f : ℕ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    LSeries (fun n => ((f n : ℝ) : ℂ)) (x : ℂ) =
      ((∑' n : ℕ, f n / (n : ℝ) ^ x : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · rw [term_zero]
    simp only [Nat.cast_zero, Real.zero_rpow hx, div_zero, Complex.ofReal_zero]
  · rw [term_of_ne_zero hn]
    rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_natCast]

private lemma abscissaOfAbsConv_primeAPInd_le_one (m a : ℕ) :
    LSeries.abscissaOfAbsConv
      (fun n => (((if n.Prime ∧ n ≡ a [MOD m] then (1 : ℝ) else 0) : ℝ) : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_le_const
  refine ⟨1, fun n _ => ?_⟩
  split_ifs with h
  · simp
  · simp

open Complex LSeries ArithmeticFunction

private lemma logMul_primeAPInd (m a : ℕ) :
    LSeries.logMul (fun n => (((if n.Prime ∧ n ≡ a [MOD m] then (1 : ℝ) else 0) : ℝ) : ℂ))
      = fun n => (((if n.Prime then vonMangoldt.residueClass ((a : ℕ) : ZMod m) n else 0) : ℝ) :
          ℂ) := by
  funext n
  change Complex.log n * (((if n.Prime ∧ n ≡ a [MOD m] then (1 : ℝ) else 0) : ℝ) : ℂ) = _
  by_cases hn : n.Prime
  · by_cases hc : n ≡ a [MOD m]
    · have hcast : ((n : ℕ) : ZMod m) = ((a : ℕ) : ZMod m) :=
        (ZMod.natCast_eq_natCast_iff n a m).mpr hc
      have hres : vonMangoldt.residueClass ((a : ℕ) : ZMod m) n = vonMangoldt n := by
        simp [vonMangoldt.residueClass, hcast]
      have h1 : (if n.Prime ∧ n ≡ a [MOD m] then (1 : ℝ) else 0) = 1 :=
        ite_eq_left ⟨hn, hc⟩
      have h2 : (if n.Prime then vonMangoldt.residueClass ((a : ℕ) : ZMod m) n else 0)
          = vonMangoldt n := by rw [ite_eq_left hn]; exact hres
      rw [h1, h2, vonMangoldt_apply_prime hn]
      simp [Complex.natCast_log]
    · have hcast : ((n : ℕ) : ZMod m) ≠ ((a : ℕ) : ZMod m) :=
        fun h => hc ((ZMod.natCast_eq_natCast_iff n a m).mp h)
      have hres : vonMangoldt.residueClass ((a : ℕ) : ZMod m) n = 0 := by
        simp [vonMangoldt.residueClass, hcast]
      have h1 : (if n.Prime ∧ n ≡ a [MOD m] then (1 : ℝ) else 0) = 0 :=
        ite_eq_right (fun h => hc h.2)
      have h2 : (if n.Prime then vonMangoldt.residueClass ((a : ℕ) : ZMod m) n else 0) = 0 := by
        rw [ite_eq_left hn, hres]
      rw [h1, h2]
      simp
  · have h1 : (if n.Prime ∧ n ≡ a [MOD m] then (1 : ℝ) else 0) = 0 :=
      ite_eq_right (fun h => hn h.1)
    have h2 : (if n.Prime then vonMangoldt.residueClass ((a : ℕ) : ZMod m) n else 0) = 0 :=
      ite_eq_right hn
    rw [h1, h2]
    simp

private lemma primeAPRpowSum_eq_LSeries (m a : ℕ) (x : ℝ) (hx : x ≠ 0) :
    ((∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-x) : ℝ) : ℂ)
      = LSeries (fun n => (((if n.Prime ∧ n ≡ a [MOD m] then (1 : ℝ) else 0) : ℝ) : ℂ))
          (x : ℂ) := by
  have hsub : (∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-x))
      = ∑' n, ({p : ℕ | p.Prime ∧ p ≡ a [MOD m]}.indicator (fun n => (n : ℝ) ^ (-x)) n) :=
    tsum_subtype {p : ℕ | p.Prime ∧ p ≡ a [MOD m]} (fun n : ℕ => (n : ℝ) ^ (-x))
  rw [LSeries_ofReal_eq_ofReal_tsum_rpow _ x hx, hsub]
  congr 1
  apply tsum_congr
  intro n
  by_cases hn : n.Prime ∧ n ≡ a [MOD m]
  · rw [Set.indicator_of_mem (by simpa using hn), ite_eq_left hn,
      Real.rpow_neg (Nat.cast_nonneg n), one_div]
  · rw [Set.indicator_of_notMem (by simpa using hn), ite_eq_right hn]
    simp

private lemma hasDerivAt_primeAPRpowSum (m a : ℕ) (x : ℝ) (hx : 1 < x) :
    HasDerivAt (fun s : ℝ => ∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-s))
      (-(∑' n : ℕ, (if n.Prime then
        ArithmeticFunction.vonMangoldt.residueClass ((a : ℕ) : ZMod m) n else 0) /
        (n : ℝ) ^ x)) x := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have habs : LSeries.abscissaOfAbsConv
      (fun n => (((if n.Prime ∧ n ≡ a [MOD m] then (1 : ℝ) else 0) : ℝ) : ℂ)) <
      ((x : ℂ)).re := by
    rw [Complex.ofReal_re]
    have h1 : LSeries.abscissaOfAbsConv
        (fun n => (((if n.Prime ∧ n ≡ a [MOD m] then (1 : ℝ) else 0) : ℝ) : ℂ)) ≤
        ((1 : ℝ) : EReal) := by
      simpa using abscissaOfAbsConv_primeAPInd_le_one m a
    exact lt_of_le_of_lt h1 (by exact_mod_cast hx)
  have hderiv := LSeries_hasDerivAt habs
  have hre := hderiv.real_of_complex
  have hval : (-LSeries (LSeries.logMul
      (fun n => (((if n.Prime ∧ n ≡ a [MOD m] then (1 : ℝ) else 0) : ℝ) : ℂ)))
      (↑x : ℂ)).re =
      -(∑' n : ℕ, (if n.Prime then
        ArithmeticFunction.vonMangoldt.residueClass ((a : ℕ) : ZMod m) n else 0) /
        (n : ℝ) ^ x) := by
    rw [logMul_primeAPInd m a, LSeries_ofReal_eq_ofReal_tsum_rpow _ x hx0,
      Complex.neg_re, Complex.ofReal_re]
  rw [hval] at hre
  have hfun : (fun s : ℝ => ∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}),
      (p.val : ℝ) ^ (-s)) =ᶠ[nhds x]
      (fun t : ℝ => (LSeries
        (fun n => (((if n.Prime ∧ n ≡ a [MOD m] then (1 : ℝ) else 0) : ℝ) : ℂ))
        (↑t : ℂ)).re) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one (Set.mem_Ioi.mp ht))
    have h := primeAPRpowSum_eq_LSeries m a t ht0
    have h2 := congrArg Complex.re h
    simpa using h2
  exact hre.congr_of_eventuallyEq hfun

open Complex LSeries ArithmeticFunction.vonMangoldt

private lemma abs_tsum_residueClass_rpow_sub_pole_le {q : ℕ} [NeZero q] {b : ZMod q}
    (hb : IsUnit b) :
    ∃ C : ℝ, ∀ x ∈ Set.Ioc 1 2,
      |∑' n : ℕ, ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ) ^ x -
        ((q.totient : ℝ))⁻¹ / (x - 1)| ≤ C := by
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ) ^ x =
        (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux b x).re +
          (q.totient : ℝ)⁻¹ / (x - 1) := by
    refine Complex.ofReal_injective ?_
    simp only [Complex.ofReal_tsum, Complex.ofReal_div,
      Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast,
      Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one]
    simp_rw [← ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux_real hb hx,
      ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux hb
        <| Set.mem_ofPred.mpr (Complex.ofReal_re x ▸ hx),
      sub_add_cancel, LSeries, LSeries.term]
    refine tsum_congr fun n ↦ ?_
    split_ifs with hn
    · simp only [hn, ArithmeticFunction.vonMangoldt.residueClass_apply_zero,
        Complex.ofReal_zero, zero_div]
    · rfl
  have hcont : ContinuousOn
      (fun x : ℝ ↦ (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux b x).re)
      (Set.Icc 1 2) :=
    continuous_re.continuousOn.comp (t := Set.univ)
        (ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux b)
        (fun ⦃x⦄ _ ↦ trivial)
      |>.comp Complex.continuous_ofReal.continuousOn fun x hx ↦ by
        simpa only [Set.mem_ofPred_eq, Complex.ofReal_re] using hx.1
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  refine ⟨C, fun x hx => ?_⟩
  rw [H hx.1, add_sub_cancel_right, ← Real.norm_eq_abs]
  exact hC x (Set.mem_Icc_of_Ioc hx)

private lemma abs_tsum_primeResidueClass_rpow_sub_pole_le {q : ℕ} [NeZero q] {b : ZMod q}
    (hb : IsUnit b) :
    ∃ C : ℝ, ∀ x ∈ Set.Ioc 1 2,
      |∑' n : ℕ, (if n.Prime then
        ArithmeticFunction.vonMangoldt.residueClass b n else 0) / (n : ℝ) ^ x -
        ((q.totient : ℝ))⁻¹ / (x - 1)| ≤ C := by
  obtain ⟨C₂, hC₂⟩ := abs_tsum_residueClass_rpow_sub_pole_le hb
  have hS : Summable
      (fun n : ℕ => (if n.Prime then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ)) :=
    ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div b
  refine ⟨C₂ + |∑' n : ℕ, (if n.Prime then (0 : ℝ) else
      ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ)|, fun x hx => ?_⟩
  have hx1 : 1 < x := hx.1
  have hnp_nonneg : ∀ n : ℕ, 0 ≤ (if n.Prime then (0 : ℝ) else
      ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ) ^ x := by
    intro n
    split_ifs with hn
    · exact div_nonneg le_rfl (Real.rpow_nonneg (Nat.cast_nonneg n) x)
    · exact div_nonneg (ArithmeticFunction.vonMangoldt.residueClass_nonneg b n)
        (Real.rpow_nonneg (Nat.cast_nonneg n) x)
  have hnp_le : ∀ n : ℕ, (if n.Prime then (0 : ℝ) else
      ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ) ^ x ≤
      (if n.Prime then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ) := by
    intro n
    rcases n.eq_zero_or_pos with rfl | hnpos
    · have h0 : (if (0 : ℕ).Prime then (0 : ℝ) else
          ArithmeticFunction.vonMangoldt.residueClass b 0) = 0 := by
        rw [ite_eq_right Nat.not_prime_zero,
          ArithmeticFunction.vonMangoldt.residueClass_apply_zero]
      rw [h0, zero_div, zero_div]
    · have hbase : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
      have hnposR : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hbase
      have hpow : (n : ℝ) ≤ (n : ℝ) ^ x := by
        conv_lhs => rw [← Real.rpow_one n]
        exact Real.rpow_le_rpow_of_exponent_le hbase hx1.le
      split_ifs with hnP
      · rw [zero_div, zero_div]
      · exact div_le_div_of_nonneg_left
          (ArithmeticFunction.vonMangoldt.residueClass_nonneg b n) hnposR hpow
  have hnp : Summable (fun n : ℕ => (if n.Prime then (0 : ℝ) else
      ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ) ^ x) :=
    Summable.of_nonneg_of_le hnp_nonneg hnp_le hS
  have hfull : Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ) ^ x) :=
    LSeries.summable_real_of_abscissaOfAbsConv_lt
      ((ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one b).trans_lt
        (by exact_mod_cast hx1))
  have hsplit : ∀ n : ℕ,
      ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ) ^ x =
        (if n.Prime then ArithmeticFunction.vonMangoldt.residueClass b n else 0) /
          (n : ℝ) ^ x +
        (if n.Prime then (0 : ℝ) else
          ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ) ^ x := by
    intro n
    split_ifs with hn
    · simp
    · simp
  have hQ : (fun n : ℕ => (if n.Prime then
      ArithmeticFunction.vonMangoldt.residueClass b n else 0) / (n : ℝ) ^ x) =
      (fun n : ℕ => ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ) ^ x) -
      (fun n : ℕ => (if n.Prime then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ) ^ x) := by
    funext n
    simp only [Pi.sub_apply]
    rw [hsplit n]
    ring
  have htri : ∀ A B : ℝ, |A - B| ≤ |A| + |B| := by
    intro A B
    calc |A - B| = |A + (-B)| := by rw [sub_eq_add_neg]
      _ ≤ |A| + |-B| := abs_add_le _ _
      _ = |A| + |B| := by rw [abs_neg]
  have hQtsum : (∑' n : ℕ, (if n.Prime then
      ArithmeticFunction.vonMangoldt.residueClass b n else 0) / (n : ℝ) ^ x) =
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ) ^ x) -
      ∑' n : ℕ, (if n.Prime then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ) ^ x := by
    rw [hQ]
    exact Summable.tsum_sub hfull hnp
  have hnp_ge : 0 ≤ ∑' n : ℕ, (if n.Prime then (0 : ℝ) else
      ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ) ^ x :=
    tsum_nonneg hnp_nonneg
  have hnp_le_S : (∑' n : ℕ, (if n.Prime then (0 : ℝ) else
      ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ) ^ x) ≤
      ∑' n : ℕ, (if n.Prime then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ) :=
    Summable.tsum_le_tsum hnp_le hnp hS
  have e : (∑' n : ℕ, (if n.Prime then
      ArithmeticFunction.vonMangoldt.residueClass b n else 0) / (n : ℝ) ^ x) -
      (q.totient : ℝ)⁻¹ / (x - 1) =
      ((∑' n : ℕ, ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ) ^ x) -
        (q.totient : ℝ)⁻¹ / (x - 1)) -
      ∑' n : ℕ, (if n.Prime then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ) ^ x := by
    rw [hQtsum]; ring
  rw [e]
  calc |((∑' n : ℕ, ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ) ^ x) -
        (q.totient : ℝ)⁻¹ / (x - 1)) -
      ∑' n : ℕ, (if n.Prime then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ) ^ x|
      ≤ |(∑' n : ℕ, ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ) ^ x) -
        (q.totient : ℝ)⁻¹ / (x - 1)| +
        |∑' n : ℕ, (if n.Prime then (0 : ℝ) else
          ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ) ^ x| :=
      htri _ _
    _ ≤ C₂ + |∑' n : ℕ, (if n.Prime then (0 : ℝ) else
        ArithmeticFunction.vonMangoldt.residueClass b n) / (n : ℝ)| := by
        apply add_le_add (hC₂ x hx)
        rw [abs_of_nonneg hnp_ge]
        exact le_trans hnp_le_S (le_abs_self _)

private lemma abs_primeAPRpowSum_add_log_le (m a : ℕ) (hm : 0 < m) (hcop : Nat.Coprime a m) :
    ∃ C : ℝ, ∀ x ∈ Set.Ioc 1 2,
      |∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-x) +
        ((Nat.totient m : ℝ))⁻¹ * Real.log (x - 1)| ≤ C := by
  have : NeZero m := ⟨hm.ne'⟩
  have hb : IsUnit ((a : ℕ) : ZMod m) := (ZMod.isUnit_iff_coprime a m).mpr hcop
  obtain ⟨C₂, hC₂⟩ := abs_tsum_primeResidueClass_rpow_sub_pole_le hb
  have hg : ∀ t : ℝ, 1 < t → HasDerivAt
      (fun s : ℝ => (∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-s)) +
        ((Nat.totient m : ℝ))⁻¹ * Real.log (s - 1))
      (-(∑' n : ℕ, (if n.Prime then
        ArithmeticFunction.vonMangoldt.residueClass ((a : ℕ) : ZMod m) n else 0) /
        (n : ℝ) ^ t) + ((Nat.totient m : ℝ))⁻¹ * (t - 1)⁻¹) t := by
    intro t ht
    have hP := hasDerivAt_primeAPRpowSum m a t ht
    have hlog : HasDerivAt (fun y : ℝ => Real.log (y - 1)) (1 / (t - 1)) t :=
      ((hasDerivAt_id t).sub_const 1).log
        (show (id t - 1) ≠ 0 from sub_ne_zero.mpr (ne_of_gt ht))
    have hcm : HasDerivAt (fun y : ℝ => ((Nat.totient m : ℝ))⁻¹ * Real.log (y - 1))
        (((Nat.totient m : ℝ))⁻¹ * (1 / (t - 1))) t :=
      hlog.const_mul _
    have hadd := hP.add hcm
    rwa [one_div] at hadd
  have e21 : (2 : ℝ) - 1 = 1 := by norm_num
  refine ⟨|∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-(2 : ℝ))| +
    max C₂ 0, fun x hx => ?_⟩
  have hx1 : 1 < x := hx.1
  have hx2 : x ≤ 2 := hx.2
  have key : ∀ t ∈ Set.Icc x 2, HasDerivWithinAt
      (fun s : ℝ => (∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-s)) +
        ((Nat.totient m : ℝ))⁻¹ * Real.log (s - 1))
      (-(∑' n : ℕ, (if n.Prime then
        ArithmeticFunction.vonMangoldt.residueClass ((a : ℕ) : ZMod m) n else 0) /
        (n : ℝ) ^ t) + ((Nat.totient m : ℝ))⁻¹ * (t - 1)⁻¹)
      (Set.Icc x 2) t := by
    intro t ht
    exact (hg t (lt_of_lt_of_le hx1 ht.1)).hasDerivWithinAt
  have bnd : ∀ t ∈ Set.Ico x 2,
      ‖-(∑' n : ℕ, (if n.Prime then
        ArithmeticFunction.vonMangoldt.residueClass ((a : ℕ) : ZMod m) n else 0) /
        (n : ℝ) ^ t) + ((Nat.totient m : ℝ))⁻¹ * (t - 1)⁻¹‖ ≤ C₂ := by
    intro t ht
    have htmem : t ∈ Set.Ioc 1 2 := ⟨lt_of_lt_of_le hx1 ht.1, le_of_lt ht.2⟩
    have hN3 := hC₂ t htmem
    have e : -(∑' n : ℕ, (if n.Prime then
        ArithmeticFunction.vonMangoldt.residueClass ((a : ℕ) : ZMod m) n else 0) /
        (n : ℝ) ^ t) + ((Nat.totient m : ℝ))⁻¹ * (t - 1)⁻¹ =
        -((∑' n : ℕ, (if n.Prime then
        ArithmeticFunction.vonMangoldt.residueClass ((a : ℕ) : ZMod m) n else 0) /
        (n : ℝ) ^ t) - ((Nat.totient m : ℝ))⁻¹ / (t - 1)) := by
      rw [div_eq_mul_inv]; ring
    rw [e, Real.norm_eq_abs, abs_neg]
    exact hN3
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' key bnd 2
    (Set.right_mem_Icc.mpr hx2)
  have hstep : |(∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-x)) +
      ((Nat.totient m : ℝ))⁻¹ * Real.log (x - 1)| ≤
      |∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-(2 : ℝ))| +
      C₂ * (2 - x) := by
    have h1 : |(∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-x)) +
        ((Nat.totient m : ℝ))⁻¹ * Real.log (x - 1)| -
        |∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-(2 : ℝ))| ≤
        |((∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-(2 : ℝ))) +
        ((Nat.totient m : ℝ))⁻¹ * Real.log ((2 : ℝ) - 1)) -
        ((∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-x)) +
        ((Nat.totient m : ℝ))⁻¹ * Real.log (x - 1))| := by
      calc |(∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-x)) +
          ((Nat.totient m : ℝ))⁻¹ * Real.log (x - 1)| -
          |∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-(2 : ℝ))| ≤
          |((∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-x)) +
          ((Nat.totient m : ℝ))⁻¹ * Real.log (x - 1)) -
          ∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-(2 : ℝ))| :=
          abs_sub_abs_le_abs_sub _ _
        _ = |((∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-(2 : ℝ))) +
          ((Nat.totient m : ℝ))⁻¹ * Real.log ((2 : ℝ) - 1)) -
          ((∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-x)) +
          ((Nat.totient m : ℝ))⁻¹ * Real.log (x - 1))| := by
          rw [e21, Real.log_one, mul_zero, add_zero]
          exact abs_sub_comm _ _
    have h2 : |((∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-(2 : ℝ))) +
        ((Nat.totient m : ℝ))⁻¹ * Real.log ((2 : ℝ) - 1)) -
        ((∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-x)) +
        ((Nat.totient m : ℝ))⁻¹ * Real.log (x - 1))| ≤ C₂ * (2 - x) := by
      have h := hmvt
      rwa [Real.norm_eq_abs] at h
    linarith
  calc |(∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-x)) +
      ((Nat.totient m : ℝ))⁻¹ * Real.log (x - 1)| ≤
      |∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-(2 : ℝ))| +
      C₂ * (2 - x) := hstep
    _ ≤ |∑' (p : {p : ℕ // p.Prime ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-(2 : ℝ))| +
      max C₂ 0 := by
      have hle : C₂ * (2 - x) ≤ max C₂ 0 := by
        rcases le_total 0 C₂ with h | h
        · calc C₂ * (2 - x) ≤ C₂ * 1 :=
              mul_le_mul_of_nonneg_left (by linarith) h
            _ = C₂ := mul_one _
            _ ≤ max C₂ 0 := le_max_left _ _
        · calc C₂ * (2 - x) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg h (by linarith)
            _ ≤ max C₂ 0 := le_max_right _ _
      linarith

private lemma tendsto_div_of_abs_add_log_le (c : ℝ) (A B : ℝ → ℝ) (C₁ C₂ : ℝ)
    (hA : ∀ x ∈ Set.Ioc 1 2, |A x + c * Real.log (x - 1)| ≤ C₁)
    (hB : ∀ x ∈ Set.Ioc 1 2, |B x + Real.log (x - 1)| ≤ C₂) :
    Filter.Tendsto (fun x => A x / B x) (nhdsWithin 1 (Set.Ioi 1)) (nhds c) := by
  have hsub : Filter.Tendsto (fun x : ℝ => x - 1) (nhds (1 : ℝ)) (nhds (0 : ℝ)) := by
    have h := (continuous_sub_right (1 : ℝ)).tendsto (1 : ℝ)
    simpa using h
  have h1 : Filter.Tendsto (fun x : ℝ => x - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hsub.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall (fun x (hx : x ∈ Set.Ioi 1) => by
        change (0 : ℝ) < x - 1
        have hx1 : (1 : ℝ) < x := hx
        linarith))
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log (x - 1)) (𝓝[>] (1 : ℝ)) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp h1
  have hL : Filter.Tendsto (fun x : ℝ => -Real.log (x - 1)) (𝓝[>] (1 : ℝ)) atTop :=
    Filter.tendsto_neg_atBot_atTop.comp hlog
  have hinv : Filter.Tendsto (fun x : ℝ => (-Real.log (x - 1))⁻¹) (𝓝[>] (1 : ℝ))
      (nhds 0) :=
    hL.inv_tendsto_atTop
  have hIoc : Set.Ioc (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) :=
    Ioc_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)
  have hevA : ∀ᶠ x in 𝓝[>] (1 : ℝ), ‖A x - c * (-Real.log (x - 1))‖ ≤ |C₁| := by
    filter_upwards [hIoc] with x hx
    rw [Real.norm_eq_abs]
    have h := hA x hx
    have e : A x - c * (-Real.log (x - 1)) = A x + c * Real.log (x - 1) := by ring
    rw [e]
    exact le_trans h (le_abs_self C₁)
  have hevB : ∀ᶠ x in 𝓝[>] (1 : ℝ), ‖B x - (-Real.log (x - 1))‖ ≤ |C₂| := by
    filter_upwards [hIoc] with x hx
    rw [Real.norm_eq_abs]
    have h := hB x hx
    have e : B x - (-Real.log (x - 1)) = B x + Real.log (x - 1) := by ring
    rw [e]
    exact le_trans h (le_abs_self C₂)
  have he1 : Filter.Tendsto
      (fun x => (-Real.log (x - 1))⁻¹ * (A x - c * (-Real.log (x - 1))))
      (𝓝[>] (1 : ℝ)) (nhds 0) :=
    hinv.zero_mul_isBoundedUnder_le (Filter.isBoundedUnder_of_eventually_le hevA)
  have he2 : Filter.Tendsto
      (fun x => (-Real.log (x - 1))⁻¹ * (B x - (-Real.log (x - 1))))
      (𝓝[>] (1 : ℝ)) (nhds 0) :=
    hinv.zero_mul_isBoundedUnder_le (Filter.isBoundedUnder_of_eventually_le hevB)
  have hnum : Filter.Tendsto
      (fun x => c + (-Real.log (x - 1))⁻¹ * (A x - c * (-Real.log (x - 1))))
      (𝓝[>] (1 : ℝ)) (nhds c) := by
    have h := tendsto_const_nhds (x := c) |>.add he1
    simpa using h
  have hden : Filter.Tendsto
      (fun x => 1 + (-Real.log (x - 1))⁻¹ * (B x - (-Real.log (x - 1))))
      (𝓝[>] (1 : ℝ)) (nhds 1) := by
    have h := tendsto_const_nhds (x := (1 : ℝ)) |>.add he2
    simpa using h
  have hpos : ∀ᶠ x in 𝓝[>] (1 : ℝ), 0 < -Real.log (x - 1) :=
    hL.eventually (eventually_gt_atTop 0)
  have heq : (fun x => A x / B x) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun x => (c + (-Real.log (x - 1))⁻¹ * (A x - c * (-Real.log (x - 1)))) /
        (1 + (-Real.log (x - 1))⁻¹ * (B x - (-Real.log (x - 1))))) := by
    filter_upwards [hpos] with x hx
    show A x / B x = _ / _
    have hLne : (-Real.log (x - 1)) ≠ 0 := ne_of_gt hx
    have hLL : (-Real.log (x - 1))⁻¹ * (-Real.log (x - 1)) = 1 :=
      inv_mul_cancel₀ hLne
    have hN : c + (-Real.log (x - 1))⁻¹ * (A x - c * (-Real.log (x - 1))) =
        A x * (-Real.log (x - 1))⁻¹ := by
      have e : (-Real.log (x - 1))⁻¹ * (A x - c * (-Real.log (x - 1))) =
          (-Real.log (x - 1))⁻¹ * A x -
            c * ((-Real.log (x - 1))⁻¹ * (-Real.log (x - 1))) := by ring
      rw [e, hLL, mul_one]
      ring
    have hD : 1 + (-Real.log (x - 1))⁻¹ * (B x - (-Real.log (x - 1))) =
        B x * (-Real.log (x - 1))⁻¹ := by
      have e : (-Real.log (x - 1))⁻¹ * (B x - (-Real.log (x - 1))) =
          (-Real.log (x - 1))⁻¹ * B x -
            ((-Real.log (x - 1))⁻¹ * (-Real.log (x - 1))) := by ring
      rw [e, hLL]
      ring
    rw [hN, hD, mul_div_mul_right _ _ (inv_ne_zero hLne)]
  have hlim : Filter.Tendsto
      (fun x => (c + (-Real.log (x - 1))⁻¹ * (A x - c * (-Real.log (x - 1)))) /
        (1 + (-Real.log (x - 1))⁻¹ * (B x - (-Real.log (x - 1)))))
      (𝓝[>] (1 : ℝ)) (nhds c) := by
    have hdiv := hnum.div hden one_ne_zero
    rw [div_one] at hdiv
    exact hdiv.congr (fun x => rfl)
  exact hlim.congr' heq.symm

private lemma primeAPRpowSum_one_one_eq (s : ℝ) :
    (∑' (p : {p : ℕ // p.Prime ∧ p ≡ 1 [MOD 1]}), (p.val : ℝ) ^ (-s))
      = ∑' (p : {p : ℕ // p.Prime}), (p.val : ℝ) ^ (-s) := by
  have h := Equiv.tsum_eq
    (Equiv.subtypeEquivRight (show ∀ p : ℕ, (p.Prime ∧ p ≡ 1 [MOD 1]) ↔ p.Prime from
      fun p => ⟨fun h => h.1, fun h => ⟨h, Nat.modEq_one⟩⟩))
    (fun p : {p : ℕ // p.Prime} => (p.val : ℝ) ^ (-s))
  simpa [Equiv.subtypeEquivRight_apply] using h

section
namespace MetaMathlibExt.NumberTheory.PrimeCounting

/-- **Dirichlet density of primes in an arithmetic progression.** Let $a$ and $m$ be natural numbers
with $m > 0$ and $\gcd(a, m) = 1$, and let $\varphi$ be Euler's totient function. As the real
number $s$ tends to $1$ from above,
$$\frac{\sum_{p \equiv a \pmod{m}} p^{-s}}{\sum_{p} p^{-s}} \to \frac{1}{\varphi(m)},$$
where both sums run over primes $p$. That is, the primes congruent to $a$ modulo $m$ have relative
Dirichlet density $1/\varphi(m)$ among all primes.

Source: B. Li, S. J. Miller, T. Popescu, D. Sarnecki, and N. Wattanawanichkul,
"Modeling Random Walks to Infinity on Primes in Z[sqrt(2)]",
*Journal of Integer Sequences* 25 (2022), Article 22.6.1,
[TeX source](https://cs.uwaterloo.ca/journals/JIS/VOL25/Miller/miller11.tex),
relative Dirichlet-density definition at lines 281-285 and primes-in-arithmetic-
progressions statement at lines 290-292.

Proves `Wanted` entry `dirichlet_density_primes_arithmetic_progression`.
-/
theorem dirichlet_density_primes_arithmetic_progression
    (a m : ℕ) (hm : 0 < m) (hcop : Nat.Coprime a m) :
    Filter.Tendsto (fun s : ℝ =>
      (∑' (p : { p : ℕ // Nat.Prime p ∧ p ≡ a [MOD m] }), (p.val : ℝ) ^ (-s)) /
      (∑' (p : { p : ℕ // Nat.Prime p }), (p.val : ℝ) ^ (-s)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 / (Nat.totient m : ℝ))) := by
  obtain ⟨C₁, hC₁⟩ := abs_primeAPRpowSum_add_log_le m a hm hcop
  obtain ⟨C₂, hC₂⟩ := abs_primeAPRpowSum_add_log_le 1 1 Nat.zero_lt_one
    (Nat.coprime_one_right 1)
  have hB : ∀ x ∈ Set.Ioc 1 2,
      |(∑' (p : {p : ℕ // Nat.Prime p}), (p.val : ℝ) ^ (-x)) +
        Real.log (x - 1)| ≤ C₂ := by
    intro x hx
    have h := hC₂ x hx
    rw [Nat.totient_one, Nat.cast_one, inv_one, one_mul,
      primeAPRpowSum_one_one_eq] at h
    exact h
  have hlim := tendsto_div_of_abs_add_log_le ((Nat.totient m : ℝ))⁻¹
    (fun s : ℝ => ∑' (p : {p : ℕ // Nat.Prime p ∧ p ≡ a [MOD m]}), (p.val : ℝ) ^ (-s))
    (fun s : ℝ => ∑' (p : {p : ℕ // Nat.Prime p}), (p.val : ℝ) ^ (-s))
    C₁ C₂ hC₁ hB
  rw [one_div]
  exact hlim

end MetaMathlibExt.NumberTheory.PrimeCounting
end
