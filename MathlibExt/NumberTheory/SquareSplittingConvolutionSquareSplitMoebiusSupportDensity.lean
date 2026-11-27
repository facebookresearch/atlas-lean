/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SquareSplittingConvolution
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import MathlibExt.NumberTheory.SquareSplittingConvolution.DivisorProperties
import MathlibExt.NumberTheory.SquareSplittingConvolution.MoebiusInversion
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Support and density of the square-splitting Möbius function

The inverse of the constant-one function is supported on positive integers whose prime
exponents are at most three. Its support density and squared-norm average are reciprocal
values of the Riemann zeta function at four.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 11.
-/

namespace MetaMathlibExt

open Filter Topology Asymptotics

private theorem split_coords {u v : ℕ} (hu : Squarefree u) (hv : v ≠ 0) :
    squareSplitU (u * v ^ 2) = u ∧ squareSplitV (u * v ^ 2) = v := by
  have hn := mul_ne_zero hu.ne_zero (pow_ne_zero 2 hv)
  have hroot : Nat.floorRoot 2 (u * v ^ 2) = v := by
    apply Nat.eq_of_factorization_eq (Nat.floorRoot_ne_zero.mpr ⟨by decide, hn⟩) hv
    intro p
    rw [Nat.factorization_floorRoot, Finsupp.floorDiv_apply, Nat.factorization_mul hu.ne_zero
      (pow_ne_zero 2 hv), Nat.factorization_pow]
    change (u.factorization p + 2 * v.factorization p) / 2 = v.factorization p
    have := hu.natFactorization_le_one p
    omega
  have hV : squareSplitV (u * v ^ 2) = v := by
    simpa [Nat.floorRoot, hn, squareSplitV] using hroot
  have h := squareSplitU_mul_squareSplitV_sq hn
  rw [hV] at h
  exact ⟨Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (pow_ne_zero 2 hv)) h, hV⟩

private theorem split_parts {n : ℕ} (hn : n ≠ 0) :
    Squarefree (squareSplitU n) ∧ squareSplitV n ≠ 0 := by
  obtain ⟨u, v, _, hv, h, hu⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn)
  rw [mul_comm] at h
  obtain ⟨hU, hV⟩ := split_coords hu hv.ne'
  rw [← h, hU, hV]
  exact ⟨hu, hv.ne'⟩

private theorem bivariate_conv (f g : ArithmeticFunction ℂ) {u v : ℕ}
    (hu : Squarefree u) (hv : v ≠ 0) :
    squareSplitConv f g (u * v ^ 2) = ∑ a ∈ u.divisors, ∑ b ∈ v.divisors,
      f (a * b ^ 2) * g (u / a * (v / b) ^ 2) := by
  obtain ⟨hU, hV⟩ := split_coords hu hv
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2 ^ 2) ↑(u.divisors ×ˢ v.divisors) := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc, hd⟩ := Finset.mem_product.mp hcd
    have H₁ := split_coords (hu.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))
      (Nat.pos_of_mem_divisors hb).ne'
    have H₂ := split_coords (hu.squarefree_of_dvd (Nat.dvd_of_mem_divisors hc))
      (Nat.pos_of_mem_divisors hd).ne'
    change a * b ^ 2 = c * d ^ 2 at h
    rw [h] at H₁
    exact Prod.ext (H₁.1.symm.trans H₂.1) (H₁.2.symm.trans H₂.2)
  rw [squareSplitConv_apply _ _ (mul_ne_zero hu.ne_zero (pow_ne_zero 2 hv)), squareSplitDivisors,
    hU, hV, Finset.sum_image hinj, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hbv := Nat.dvd_of_mem_divisors hb
  rw [← Nat.div_mul_div_comm (Nat.dvd_of_mem_divisors ha) (pow_dvd_pow_of_dvd hbv 2)]
  simp only [sq, Nat.div_mul_div_comm hbv hbv]

private noncomputable def splitMoebius : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (ArithmeticFunction.moebius (squareSplitU n) : ℂ) *
    ArithmeticFunction.moebius (squareSplitV n), by simp⟩

private theorem splitMoebius_coords {u v : ℕ} (hu : Squarefree u) (hv : v ≠ 0) :
    splitMoebius (u * v ^ 2) = (ArithmeticFunction.moebius u : ℂ) *
      ArithmeticFunction.moebius v := by
  obtain ⟨hU, hV⟩ := split_coords hu hv
  simp [splitMoebius, mul_ne_zero hu.ne_zero (pow_ne_zero 2 hv), hU, hV]

private theorem quotient_moebius_sum (n : ℕ) :
    (∑ a ∈ n.divisors, (ArithmeticFunction.moebius (n / a) : ℂ)) =
      (1 : ArithmeticFunction ℂ) n := by
  have h := DFunLike.congr_fun (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ)) n
  rw [ArithmeticFunction.mul_apply] at h
  change (∑ x ∈ n.divisorsAntidiagonal,
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) x.1 *
      (ArithmeticFunction.moebius x.2 : ℂ)) = _ at h
  rw [Nat.sum_divisorsAntidiagonal (fun a b =>
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) a *
        (ArithmeticFunction.moebius b : ℂ))] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro a ha
  simp [ArithmeticFunction.zeta_apply_ne (Nat.pos_of_mem_divisors ha).ne']

private theorem splitMoebius_inverse :
    squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) splitMoebius = 1 := by
  apply ArithmeticFunction.ext
  intro n
  obtain rfl | hn := eq_or_ne n 0
  · simp
  obtain ⟨u, v, _, hv, h, hu⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn)
  rw [mul_comm] at h
  rw [← h, bivariate_conv _ _ hu hv.ne']
  calc
    _ = ∑ a ∈ u.divisors, ∑ b ∈ v.divisors,
        (ArithmeticFunction.moebius (u / a) : ℂ) * ArithmeticFunction.moebius (v / b) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have ha₀ := (Nat.pos_of_mem_divisors ha).ne'
      have hb₀ := (Nat.pos_of_mem_divisors hb).ne'
      have hva : v / b ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hv (Nat.dvd_of_mem_divisors hb))
        (Nat.pos_of_mem_divisors hb)).ne'
      rw [splitMoebius_coords (hu.squarefree_of_dvd (Nat.div_dvd_of_dvd
        (Nat.dvd_of_mem_divisors ha))) hva]
      simp [ArithmeticFunction.zeta_apply_ne (mul_ne_zero ha₀ (pow_ne_zero 2 hb₀))]
    _ = (1 : ArithmeticFunction ℂ) u * (1 : ArithmeticFunction ℂ) v := by
      rw [← Finset.sum_mul_sum, quotient_moebius_sum, quotient_moebius_sum]
    _ = (1 : ArithmeticFunction ℂ) (u * v ^ 2) := by
      by_cases hu₁ : u = 1 <;> by_cases hv₁ : v = 1 <;>
        simp [hu₁, hv₁]

private theorem conv_one (f : ArithmeticFunction ℂ) : squareSplitConv f 1 = f := by
  apply ArithmeticFunction.ext
  intro n
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [squareSplitConv_apply _ _ hn, Finset.sum_eq_single n]
  · simp [Nat.div_self (Nat.pos_of_ne_zero hn)]
  · intro d hd hdn
    have hdvd := (squareSplitDivisors_properties.1 n hn).2.2 d hd
    have hne : n / d ≠ 1 := by
      intro h
      exact hdn (by simpa [h] using (Nat.div_mul_cancel hdvd))
    simp [hne]
  · exact fun h => (h (squareSplitDivisors_properties.1 n hn).2.1).elim

private theorem moebius_formula (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1)
    {n : ℕ} (hn : n ≠ 0) :
    m n = (ArithmeticFunction.moebius (squareSplitU n) : ℂ) *
      ArithmeticFunction.moebius (squareSplitV n) := by
  have h := (squareSplit_moebius_inversion m hm splitMoebius 1).mp splitMoebius_inverse.symm
  rw [conv_one] at h
  rw [← h]
  simp [splitMoebius, hn]

private theorem squarefree_V_iff {n : ℕ} (hn : n ≠ 0) :
    Squarefree (squareSplitV n) ↔ ∀ p, n.factorization p ≤ 3 := by
  have hV : squareSplitV n = Nat.floorRoot 2 n := by simp [squareSplitV, Nat.floorRoot, hn]
  rw [hV, Nat.squarefree_iff_factorization_le_one (Nat.floorRoot_ne_zero.mpr ⟨by decide, hn⟩)]
  simp only [Nat.factorization_floorRoot, Finsupp.floorDiv_apply, Nat.floorDiv_eq_div]
  exact forall_congr' fun p => by omega

private theorem moebius_support (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1)
    {n : ℕ} (hn : n ≠ 0) : m n ≠ 0 ↔ ∀ p, n.factorization p ≤ 3 := by
  rw [moebius_formula m hm hn]
  simp only [mul_ne_zero_iff, ne_eq, Int.cast_eq_zero,
    ArithmeticFunction.moebius_ne_zero_iff_squarefree, (split_parts hn).1, true_and]
  exact squarefree_V_iff hn

open scoped Classical in
private theorem norm_moebius_sq (n : ℕ) :
    ‖(ArithmeticFunction.moebius n : ℂ)‖ ^ 2 = if Squarefree n then 1 else 0 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [← ArithmeticFunction.moebius_ne_zero_iff_squarefree, h]

open scoped Classical in
private theorem moebius_norm_sq (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1)
    {n : ℕ} (hn : n ≠ 0) : ‖m n‖ ^ 2 = if m n ≠ 0 then 1 else 0 := by
  conv_lhs => rw [moebius_formula m hm hn, norm_mul, mul_pow, norm_moebius_sq, norm_moebius_sq]
  simp only [(split_parts hn).1, ite_true, one_mul]
  simp only [moebius_support m hm hn, squarefree_V_iff hn]

private theorem fourthRoot_eq_one_iff {n : ℕ} (hn : n ≠ 0) :
    Nat.floorRoot 4 n = 1 ↔ ∀ p, n.factorization p ≤ 3 := by
  have hr : Nat.floorRoot 4 n ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by decide, hn⟩
  constructor
  · intro h p
    have hf := congr_arg (fun a => a.factorization p) h
    simp only [Nat.factorization_floorRoot, Finsupp.floorDiv_apply, Nat.factorization_one,
      Finsupp.zero_apply, Nat.floorDiv_eq_div] at hf
    omega
  · intro h
    apply Nat.eq_of_factorization_eq hr one_ne_zero
    intro p
    simp only [Nat.factorization_floorRoot, Finsupp.floorDiv_apply, Nat.factorization_one,
      Finsupp.zero_apply, Nat.floorDiv_eq_div]
    have := h p
    omega

open scoped Classical in
private theorem fourthfree_indicator {n X : ℕ} (hn : n ∈ Finset.Icc 1 X) :
    (if ∀ p, n.factorization p ≤ 3 then (1 : ℝ) else 0) =
      ∑ d ∈ Finset.Icc 1 X, if d ^ 4 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  obtain ⟨hn₀, hnX⟩ := Finset.mem_Icc.mp hn
  let r := Nat.floorRoot 4 n
  have hr : r ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by decide, by omega⟩
  have hs : (Finset.Icc 1 X).filter (fun d => d ^ 4 ∣ n) = r.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · exact fun h => ⟨Nat.pow_dvd_iff_dvd_floorRoot.mp h.2, hr⟩
    · rintro ⟨h, -⟩
      have hpow : d ^ 4 ∣ n := Nat.pow_dvd_iff_dvd_floorRoot.mpr h
      have hd : d ∣ n := (dvd_pow_self d (by decide : 4 ≠ 0)).trans hpow
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn₀, (Nat.le_of_dvd hn₀ hd).trans hnX⟩, hpow⟩
  rw [← Finset.sum_filter, hs, ← fourthRoot_eq_one_iff (by omega)]
  have h := DFunLike.congr_fun (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ)) r
  rw [ArithmeticFunction.coe_zeta_mul_apply] at h
  by_cases heq : Nat.floorRoot 4 n = 1 <;>
    simpa only [r, ArithmeticFunction.one_apply, ArithmeticFunction.intCoe_apply, heq,
      ite_true, ite_false] using h.symm

open scoped Classical in
private theorem fourthfree_count (X : ℕ) :
    (((Finset.Icc 1 X).filter fun n => ∀ p, n.factorization p ≤ 3).card : ℝ) =
      ∑ d ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius d : ℝ) * ((X / d ^ 4 : ℕ) : ℝ) := by
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_congr rfl (fun n hn => fourthfree_indicator hn), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hI : Finset.Icc 1 X = Finset.Ioc 0 X := by ext n; simp; omega
  rw [hI, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]

private theorem tendsto_div_count (q : ℕ) :
    Tendsto (fun X : ℕ => ((X / q : ℕ) : ℝ) / X) atTop (𝓝 (1 / (q : ℝ))) := by
  have h := (tendsto_nat_floor_mul_div_atTop (a := 1 / (q : ℝ)) (by positivity)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, one_div_mul_eq_div, Nat.floor_div_eq_div] using h

open scoped Classical in
private theorem fourthfree_density :
    Tendsto (fun X : ℕ =>
      (((Finset.Icc 1 X).filter fun n => ∀ p, n.factorization p ≤ 3).card : ℝ) / X) atTop
      (𝓝 (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ (4 : ℕ))) := by
  let f (X d : ℕ) : ℝ := (ArithmeticFunction.moebius d : ℝ) * ((X / d ^ 4 : ℕ) : ℝ) / X
  have hlim (d : ℕ) : Tendsto (fun X => f X d) atTop
      (𝓝 ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ (4 : ℕ))) := by
    have h := (tendsto_div_count (d ^ 4)).const_mul (ArithmeticFunction.moebius d : ℝ)
    rw [Nat.cast_pow] at h
    simpa only [f, one_div, div_eq_mul_inv, mul_assoc, one_mul] using h
  have hbound (X d : ℕ) : ‖f X d‖ ≤ 1 / (d : ℝ) ^ (4 : ℕ) := by
    obtain rfl | hX := eq_or_ne X 0
    · simp [f]
    have hX' : 0 < (X : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hX
    have hm : ‖(ArithmeticFunction.moebius d : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    have hc : ((X / d ^ 4 : ℕ) : ℝ) ≤ (X : ℝ) / (d : ℝ) ^ (4 : ℕ) := by
      have h := Nat.cast_div_le (m := X) (n := d ^ 4) (α := ℝ)
      rw [Nat.cast_pow] at h
      exact h
    dsimp only [f]
    rw [norm_div, norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg hX'.le]
    calc
      _ ≤ 1 * ((X / d ^ 4 : ℕ) : ℝ) / X := by gcongr
      _ ≤ _ := by rw [one_mul, div_le_iff₀ hX', div_mul_eq_mul_div, one_mul]; exact hc
  have ht := tendsto_tsum_of_dominated_convergence
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 4)) hlim (.of_forall hbound)
  apply ht.congr
  intro X
  rw [tsum_eq_sum (s := Finset.Icc 1 X), fourthfree_count]
  · simp only [f, Finset.sum_div]
  · intro d hd
    by_cases hd₀ : d = 0
    · simp [hd₀, f]
    have hlarge : X < d := by
      simpa [Finset.mem_Icc, Nat.one_le_iff_ne_zero, hd₀] using hd
    have hs : X < d ^ 4 := hlarge.trans_le (Nat.le_self_pow (by decide) _)
    simp [f, Nat.div_eq_of_lt hs]

private theorem product_eq_inverse_zeta :
    ((∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ) ^ 4) : ℝ) : ℂ) = 1 / riemannZeta 4 := by
  have hz : riemannZeta 4 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have h := (riemannZeta_eulerProduct_hasProd (s := 4) (by norm_num)).inv₀ hz
  have hprod : HasProd (fun p : Nat.Primes => ((1 - 1 / ((p : ℕ) : ℝ) ^ 4 : ℝ) : ℂ))
      (1 / riemannZeta 4) := by
    simpa [Complex.cpow_neg, Complex.cpow_ofNat, one_div] using h
  calc
    _ = ∏' p : Nat.Primes, ((1 - 1 / ((p : ℕ) : ℝ) ^ 4 : ℝ) : ℂ) :=
      Complex.isUniformEmbedding_ofReal.isClosedEmbedding.map_tprod
        (g := Complex.ofRealHom) _
    _ = _ := hprod.tprod_eq

private theorem series_eq_inverse_zeta :
    ((∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 4 : ℝ) : ℂ) =
      1 / riemannZeta 4 := by
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (s := 4) (by norm_num)
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by norm_num)] at h
  have hseries : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 4 =
      ((∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 4 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    unfold LSeries
    apply tsum_congr
    intro n
    rw [LSeries.term_of_ne_zero' (by norm_num : (4 : ℂ) ≠ 0), Complex.cpow_ofNat]
    simp
  rw [hseries] at h
  exact (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re (by norm_num))).mpr
    (by simpa only [mul_comm] using h)

private theorem density_constant :
    (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 4) =
      ∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ) ^ 4) :=
  Complex.ofReal_injective (series_eq_inverse_zeta.trans product_eq_inverse_zeta.symm)

private theorem density_constant_re :
    (∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ) ^ 4)) = 1 / (riemannZeta 4).re := by
  have hzreal : riemannZeta 4 = ((riemannZeta 4).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using riemannZeta_im_eq_zero_of_one_lt (x := 4) (by norm_num)
  have hcast : ((1 / (riemannZeta 4).re : ℝ) : ℂ) = 1 / riemannZeta 4 := by
    rw [Complex.ofReal_div, Complex.ofReal_one, ← hzreal]
  exact Complex.ofReal_injective (product_eq_inverse_zeta.trans hcast.symm)

open scoped Classical in
private theorem support_density (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) :
    Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter fun n => m n ≠ 0).card : ℝ) / N) atTop
      (𝓝 (∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ) ^ 4))) := by
  rw [← density_constant]
  apply fourthfree_density.congr
  intro N
  congr 2
  apply congr_arg Finset.card
  apply Finset.filter_congr
  intro n hn
  exact (moebius_support m hm (by have := (Finset.mem_Icc.mp hn).1; omega)).symm

open scoped Classical in
private theorem norm_sum_eq_count (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ‖m n‖ ^ 2) =
      (((Finset.Icc 1 N).filter fun n => m n ≠ 0).card : ℝ) := by
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro n hn
  exact moebius_norm_sq m hm (by have := (Finset.mem_Icc.mp hn).1; omega)

open scoped Classical in
private theorem norm_sum_asymptotic (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖m n‖ ^ 2) ~[atTop]
      fun x => x / (riemannZeta 4).re := by
  have hD := support_density m hm
  rw [density_constant_re] at hD
  have hlim := (hD.comp (tendsto_nat_floor_atTop (α := ℝ))).mul
    (tendsto_nat_floor_div_atTop (R := ℝ))
  have hnorm : Tendsto (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖m n‖ ^ 2) / x) atTop
      (𝓝 (1 / (riemannZeta 4).re)) := by
    simp only [mul_one] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [norm_sum_eq_count m hm]
    dsimp only [Function.comp_def]
    have hn : (⌊x⌋₊ : ℝ) ≠ 0 := by
      exact_mod_cast (show ⌊x⌋₊ ≠ 0 from (Nat.floor_pos.mpr hx).ne')
    field_simp
  have hz : (riemannZeta 4).re ≠ 0 :=
    (riemannZeta_re_pos_of_one_lt (x := 4) (by norm_num)).ne'
  have hratio := hnorm.mul_const (riemannZeta 4).re
  rw [one_div_mul_cancel hz] at hratio
  apply isEquivalent_of_tendsto_one
  change Tendsto (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖m n‖ ^ 2) /
    (x / (riemannZeta 4).re)) atTop (𝓝 1)
  simpa only [div_div_eq_mul_div, div_mul_eq_mul_div] using hratio

@[expose] public section

/-- **Support and density of the square-splitting Möbius function.** Let $\star$ be the
square-splitting convolution, $\mathbf{1}$ the constant function $1$ on the positive integers,
$\varepsilon$ the identity element ($\varepsilon(1) = 1$ and $\varepsilon(n) = 0$ for $n \ne 1$),
and let $\mu_\star$ be any complex-valued arithmetic function with
$\mathbf{1} \star \mu_\star = \varepsilon$. Then for every $n \ge 1$, $\mu_\star(n) \ne 0$ if and
only if every prime exponent of $n$ is at most $3$. The proportion of the integers
$1 \le n \le N$ with $\mu_\star(n) \ne 0$ tends to $\prod_p (1 - p^{-4})$ as $N \to \infty$, and
$\prod_p (1 - p^{-4}) = 1/\zeta(4)$. Finally,
$\sum_{1 \le n \le x} |\mu_\star(n)|^2 \sim x/\zeta(4)$ as $x \to \infty$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 11
(`integers-2026-A56-thm-11`). -/
public theorem squareSplitMoebius_support_density (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) :
    (∀ n ≠ 0, m n ≠ 0 ↔ ∀ p, n.factorization p ≤ 3) ∧
    Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter fun n => m n ≠ 0).card : ℝ) / N) atTop
      (𝓝 (∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ) ^ 4))) ∧
    ((∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ) ^ 4) : ℝ) : ℂ) = 1 / riemannZeta 4 ∧
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖m n‖ ^ 2) ~[atTop]
      fun x => x / (riemannZeta 4).re := by
  refine ⟨fun n hn => moebius_support m hm hn, support_density m hm,
    product_eq_inverse_zeta, norm_sum_asymptotic m hm⟩

end

end MetaMathlibExt
