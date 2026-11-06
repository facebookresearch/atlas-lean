/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.CStarAlgebra.KadisonSinger.MixedCharPoly
public import MathlibExt.Algebra.Polynomial.RealRooted
public import Mathlib.Analysis.Matrix.PosDef

import MathlibExt.Analysis.CStarAlgebra.KadisonSinger.RealStable
import Mathlib.Topology.Algebra.MvPolynomial
import MathlibExt.Algebra.MvPolynomial.PDeriv
import MathlibExt.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Lagrange

/-!
# The Marcus--Spielman--Srivastava barrier bound

This file proves `mixedCharacteristicPolynomial_maxRealRoot_le`: if positive semidefinite
matrices `A i` sum to the identity and each has trace at most `η`, the largest real root of their
mixed characteristic polynomial is at most `(1 + √η) ^ 2`.

The proof is the multivariate barrier argument. For a real-stable polynomial `p` and a point `x`
above its roots, the barrier in direction `i` is `∂ᵢp(x) / p(x)`. Restricted to a line in
direction `j`, `p` becomes a real-rooted polynomial `f` and `∂ᵢp` a polynomial `g` with
`Im (g z / f z) ≤ 0` on the upper half-plane. A Pick-function argument writes `g / f` as a
constant plus simple fractions with positive residues, so each barrier is nonincreasing and convex
along every coordinate direction. Hence, when the `i`-th barrier is at most `1 - 1 / δ`, applying
`1 - ∂ᵢ` and shifting `x` by `δ` in direction `i` keeps the point above the roots without raising
any barrier. Iterating over all coordinates and evaluating the mixed determinant polynomial at
scalar points gives the bound.
-/

@[expose] public section

open scoped BigOperators ComplexOrder Real

open Filter MvPolynomial

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

private lemma ksEval_real {σ : Type*} {p : MvPolynomial σ ℂ}
    (hp : MvPolynomial.map (starRingEnd ℂ) p = p) (x : σ → ℝ) :
    (eval (fun i ↦ (x i : ℂ)) p).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  have h := MvPolynomial.map_eval (starRingEnd ℂ) (fun i ↦ (x i : ℂ)) p
  rw [hp] at h
  have hg : (starRingEnd ℂ) ∘ (fun i ↦ (x i : ℂ)) = (fun i ↦ (x i : ℂ)) := by
    funext i
    simp
  rw [hg] at h
  simpa [RCLike.star_def] using h

private lemma ksMap_star_pderiv {σ : Type*} {p : MvPolynomial σ ℂ}
    (hp : MvPolynomial.map (starRingEnd ℂ) p = p) (i : σ) :
    MvPolynomial.map (starRingEnd ℂ) (pderiv i p) = pderiv i p := by
  rw [← MvPolynomial.pderiv_map, hp]

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

private lemma direction_one_pow (k : ℕ) (hk : 0 < k) :
    (Complex.exp (((Real.pi / (2 * k : ℝ) : ℝ) : ℂ) * Complex.I)) ^ k =
      Complex.I := by
  rw [← Complex.exp_nat_mul]
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [show (k : ℂ) * (((Real.pi / (2 * k : ℝ) : ℝ) : ℂ) * Complex.I) =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
    push_cast
    field_simp]
  simp

private lemma direction_three_pow (k : ℕ) (hk : 0 < k) :
    (Complex.exp ((((3 * Real.pi / (2 * k : ℝ) : ℝ) : ℂ)) * Complex.I)) ^ k =
      -Complex.I := by
  rw [← Complex.exp_nat_mul]
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [show (k : ℂ) * ((((3 * Real.pi / (2 * k : ℝ) : ℝ) : ℂ)) * Complex.I) =
      ((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I by
    push_cast
    field_simp]
  rw [show (((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
      ((Real.pi : ℂ) * Complex.I) +
        (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) by
    push_cast
    ring]
  rw [Complex.exp_add, Complex.exp_pi_mul_I]
  simp

private lemma direction_one_im_pos (k : ℕ) (hk : 0 < k) :
    0 < (Complex.exp (((Real.pi / (2 * k : ℝ) : ℝ) : ℂ) * Complex.I)).im := by
  rw [Complex.exp_ofReal_mul_I_im]
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * k)]
    nlinarith [Real.pi_pos]

private lemma direction_three_im_pos (k : ℕ) (hk : 2 ≤ k) :
    0 < (Complex.exp ((((3 * Real.pi / (2 * k : ℝ) : ℝ) : ℂ)) * Complex.I)).im := by
  rw [Complex.exp_ofReal_mul_I_im]
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * k)]
    nlinarith [Real.pi_pos]

private lemma eval_im_eq_zero_of_map_star_eq_self
    (p : Polynomial ℂ) (hp : p.map (starRingEnd ℂ) = p)
    (a : ℂ) (ha : a.im = 0) : (p.eval a).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  have h := Polynomial.eval_map_apply (p := p) (starRingEnd ℂ) a
  rw [hp] at h
  have ha' : (starRingEnd ℂ) a = a := by
    apply Complex.ext <;> simp [ha]
  rw [ha'] at h
  simpa [RCLike.star_def] using h.symm

private lemma inv_sub_real_re (t : ℝ) (a : ℂ) (ha : a.im = 0) :
    (((t : ℂ) - a)⁻¹).re = (t - a.re)⁻¹ := by
  have heq : (t : ℂ) - a = ((t - a.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [ha]
  rw [heq]
  rw [Complex.inv_re, Complex.normSq_ofReal]
  by_cases hzero : t - a.re = 0
  · rw [hzero]
    norm_num
  · field_simp
    simp

private lemma inv_sub_real_im (t : ℝ) (a : ℂ) (ha : a.im = 0) :
    (((t : ℂ) - a)⁻¹).im = 0 := by
  rw [Complex.inv_im]
  simp [ha]

private lemma reciprocal_shift_bounds (c u v : ℝ)
    (hc : 0 ≤ c) (hu : 0 < u) (huv : u ≤ v) :
    c / v ≤ c / u ∧ c / v ≤ c / u + (v - u) * (-c / v ^ 2) := by
  have hv : 0 < v := hu.trans_le huv
  constructor
  · exact div_le_div_of_nonneg_left hc hu huv
  · field_simp
    nlinarith [sq_nonneg (v - u)]

private lemma hasDerivAt_mul_inv_sub (r a y : ℂ) (hya : y ≠ a) :
    HasDerivAt (fun z : ℂ ↦ r * (z - a)⁻¹)
      (-r * (y - a)⁻¹ * (y - a)⁻¹) y := by
  have hsub : HasDerivAt (fun z : ℂ ↦ z - a) 1 y := by
    simpa using (hasDerivAt_id y).sub_const a
  have hinv := hsub.inv (sub_ne_zero.mpr hya)
  have hmul := (hasDerivAt_const y r).mul hinv
  convert hmul using 1
  field_simp [sub_ne_zero.mpr hya]
  simp

private lemma pick_rootMultiplicity_le_one_of_eval_ne_zero
    (F G : Polynomial ℂ) (hF0 : F ≠ 0)
    (hFreal : F.map (starRingEnd ℂ) = F)
    (hGreal : G.map (starRingEnd ℂ) = G)
    (hFupper : ∀ z : ℂ, 0 < z.im → F.eval z ≠ 0)
    (hpick : ∀ z : ℂ, 0 < z.im → (G.eval z / F.eval z).im ≤ 0)
    (a : ℂ) (ha : a.im = 0) (haroot : F.IsRoot a) (hGa : G.eval a ≠ 0) :
    F.rootMultiplicity a ≤ 1 := by
  let k := F.rootMultiplicity a
  have hkpos : 0 < k := (Polynomial.rootMultiplicity_pos hF0).2 haroot
  by_contra hnot
  have hk2 : 2 ≤ k := by omega
  let H := F /ₘ (Polynomial.X - Polynomial.C a) ^ k
  have hfactor : (Polynomial.X - Polynomial.C a) ^ k * H = F := by
    exact Polynomial.pow_mul_divByMonic_rootMultiplicity_eq F a
  have hHa : H.eval a ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hF0
  have hastar : (starRingEnd ℂ) a = a := by
    apply Complex.ext <;> simp [ha]
  have hHreal : H.map (starRingEnd ℂ) = H := by
    dsimp only [H]
    rw [Polynomial.map_divByMonic _ (Polynomial.monic_X_sub_C a |>.pow k)]
    rw [hFreal]
    congr 2
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      hastar]
  let c := G.eval a / H.eval a
  have hc0 : c ≠ 0 := div_ne_zero hGa hHa
  have hcim : c.im = 0 := by
    have hGi := eval_im_eq_zero_of_map_star_eq_self G hGreal a ha
    have hHi := eval_im_eq_zero_of_map_star_eq_self H hHreal a ha
    dsimp only [c]
    rw [Complex.div_im, hGi, hHi]
    simp
  have hcre0 : c.re ≠ 0 := by
    intro hzero
    apply hc0
    apply Complex.ext <;> simp [hzero, hcim]
  have hcontra (u : ℂ) (huim : 0 < u.im)
      (hlimit : 0 < (c / u ^ k).im) : False := by
    let w : ℝ → ℂ := fun r ↦ a + (r : ℂ) * u
    let rhs : ℝ → ℂ := fun r ↦ G.eval (w r) / (u ^ k * H.eval (w r))
    have hu0 : u ≠ 0 := by
      intro hzero
      subst u
      norm_num at huim
    have hwcont : Continuous w := by
      dsimp only [w]
      fun_prop
    have hGcont : Continuous fun z : ℂ ↦ G.eval z := by
      simpa [Polynomial.eval₂_eq_eval_map] using
        Polynomial.continuous_eval₂ G (RingHom.id ℂ)
    have hHcont : Continuous fun z : ℂ ↦ H.eval z := by
      simpa [Polynomial.eval₂_eq_eval_map] using
        Polynomial.continuous_eval₂ H (RingHom.id ℂ)
    have hrhscont : ContinuousAt rhs 0 := by
      dsimp only [rhs]
      apply (hGcont.comp hwcont).continuousAt.div
        (continuous_const.mul (hHcont.comp hwcont)).continuousAt
      dsimp only [w]
      simpa using mul_ne_zero (pow_ne_zero k hu0) hHa
    have hrhs0 : rhs 0 = c / u ^ k := by
      dsimp only [rhs, w, c]
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      field_simp
    have hpos_mem : {r : ℝ | 0 < (rhs r).im} ∈ nhds 0 := by
      have himcont : ContinuousAt (fun r ↦ (rhs r).im) 0 :=
        Complex.continuous_im.continuousAt.comp hrhscont
      have hlimit0 : 0 < (rhs 0).im := by rw [hrhs0]; exact hlimit
      exact himcont (Ioi_mem_nhds hlimit0)
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hpos_mem
    let r := ε / 2
    have hrpos : 0 < r := by dsimp only [r]; linarith
    have hrball : r ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp only [r]
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hrhspos : 0 < (rhs r).im := hε hrball
    have hwim : 0 < (w r).im := by
      dsimp only [w]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      rw [ha]
      simpa using mul_pos hrpos huim
    have hFne : F.eval (w r) ≠ 0 := hFupper (w r) hwim
    have hHne : H.eval (w r) ≠ 0 := by
      intro hzero
      apply hFne
      rw [← hfactor, Polynomial.eval_mul, Polynomial.eval_pow, hzero, mul_zero]
    have hr0 : r ≠ 0 := hrpos.ne'
    have hscale : ((r : ℂ) ^ k) * (G.eval (w r) / F.eval (w r)) = rhs r := by
      have hFeval : F.eval (w r) =
          (((r : ℂ) * u) ^ k) * H.eval (w r) := by
        rw [← hfactor, Polynomial.eval_mul, Polynomial.eval_pow]
        simp [w]
      dsimp only [rhs]
      rw [hFeval, mul_pow]
      have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0
      field_simp [hrc]
    have hscaleim := congrArg Complex.im hscale
    have hrpow : 0 < r ^ k := pow_pos hrpos k
    have hratio_pos : 0 < (G.eval (w r) / F.eval (w r)).im := by
      have hpow : (r : ℂ) ^ k = ((r ^ k : ℝ) : ℂ) := by norm_cast
      rw [hpow] at hscaleim
      rw [Complex.mul_im] at hscaleim
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        at hscaleim
      nlinarith
    exact (not_lt_of_ge (hpick (w r) hwim)) hratio_pos
  by_cases hcpos : 0 < c.re
  · let u := Complex.exp
        ((((3 * Real.pi / (2 * k : ℝ) : ℝ) : ℂ)) * Complex.I)
    apply hcontra u (direction_three_im_pos k hk2)
    rw [direction_three_pow k hkpos]
    rw [div_neg, Complex.div_I]
    simp only [neg_neg, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero]
    simpa using hcpos
  · have hcneg : c.re < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hcre0
    let u := Complex.exp
      (((Real.pi / (2 * k : ℝ) : ℝ) : ℂ) * Complex.I)
    apply hcontra u (direction_one_im_pos k hkpos)
    rw [direction_one_pow k hkpos, Complex.div_I]
    simp only [Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero]
    linarith

private lemma pick_rootMultiplicity_le_one
    (F G : Polynomial ℂ) (hF0 : F ≠ 0) (hcop : IsCoprime F G)
    (hFreal : F.map (starRingEnd ℂ) = F)
    (hGreal : G.map (starRingEnd ℂ) = G)
    (hFupper : ∀ z : ℂ, 0 < z.im → F.eval z ≠ 0)
    (hpick : ∀ z : ℂ, 0 < z.im → (G.eval z / F.eval z).im ≤ 0)
    (a : ℂ) (ha : a.im = 0) (haroot : F.IsRoot a) :
    F.rootMultiplicity a ≤ 1 := by
  have hGa : G.eval a ≠ 0 := by
    intro hzero
    have hdF : Polynomial.X - Polynomial.C a ∣ F :=
      Polynomial.dvd_iff_isRoot.mpr haroot
    have hdG : Polynomial.X - Polynomial.C a ∣ G :=
      Polynomial.dvd_iff_isRoot.mpr hzero
    exact Polynomial.not_isUnit_X_sub_C a (hcop.isUnit_of_dvd' hdF hdG)
  exact pick_rootMultiplicity_le_one_of_eval_ne_zero F G hF0 hFreal hGreal
    hFupper hpick a ha haroot hGa

private lemma scaled_ratio_eq (F G H : Polynomial ℂ) (a u : ℂ) (k : ℕ)
    (hfactor : (Polynomial.X - Polynomial.C a) ^ k * H = F)
    (r : ℝ) (hr : r ≠ 0)
    (hH : H.eval (a + (r : ℂ) * u) ≠ 0) :
    ((r : ℂ) ^ k) *
        (G.eval (a + (r : ℂ) * u) / F.eval (a + (r : ℂ) * u)) =
      G.eval (a + (r : ℂ) * u) /
        (u ^ k * H.eval (a + (r : ℂ) * u)) := by
  have hFeval : F.eval (a + (r : ℂ) * u) =
      (((r : ℂ) * u) ^ k) * H.eval (a + (r : ℂ) * u) := by
    rw [← hfactor, Polynomial.eval_mul, Polynomial.eval_pow]
    simp
  rw [hFeval, mul_pow]
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  field_simp [hrc]

private lemma pick_residue_pos_of_eval_ne_zero
    (F G : Polynomial ℂ) (hF0 : F ≠ 0)
    (hFreal : F.map (starRingEnd ℂ) = F)
    (hGreal : G.map (starRingEnd ℂ) = G)
    (hFupper : ∀ z : ℂ, 0 < z.im → F.eval z ≠ 0)
    (hpick : ∀ z : ℂ, 0 < z.im → (G.eval z / F.eval z).im ≤ 0)
    (a : ℂ) (ha : a.im = 0) (haroot : F.IsRoot a)
    (hGa : G.eval a ≠ 0) :
    0 < (G.eval a / F.derivative.eval a).re := by
  have hmult_le := pick_rootMultiplicity_le_one_of_eval_ne_zero F G hF0 hFreal hGreal
    hFupper hpick a ha haroot hGa
  have hmult_pos : 0 < F.rootMultiplicity a :=
    (Polynomial.rootMultiplicity_pos hF0).2 haroot
  have hmult : F.rootMultiplicity a = 1 := by omega
  let H := F /ₘ (Polynomial.X - Polynomial.C a)
  have hfactor : (Polynomial.X - Polynomial.C a) * H = F := by
    simpa [hmult] using Polynomial.pow_mul_divByMonic_rootMultiplicity_eq F a
  have hHa : H.eval a ≠ 0 := by
    simpa [hmult] using Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hF0
  have hastar : (starRingEnd ℂ) a = a := by
    apply Complex.ext <;> simp [ha]
  have hHreal : H.map (starRingEnd ℂ) = H := by
    dsimp only [H]
    rw [Polynomial.map_divByMonic _ (Polynomial.monic_X_sub_C a)]
    rw [hFreal]
    congr 2
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hastar]
  let c := G.eval a / H.eval a
  have hc0 : c ≠ 0 := div_ne_zero hGa hHa
  have hcim : c.im = 0 := by
    have hGi := eval_im_eq_zero_of_map_star_eq_self G hGreal a ha
    have hHi := eval_im_eq_zero_of_map_star_eq_self H hHreal a ha
    dsimp only [c]
    rw [Complex.div_im, hGi, hHi]
    simp
  let δ : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let w : ℕ → ℂ := fun n ↦ a + (δ n : ℂ) * Complex.I
  let rhs : ℕ → ℂ := fun n ↦
    G.eval (w n) / (Complex.I * H.eval (w n))
  have hδ : Tendsto δ atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hw : Tendsto w atTop (nhds a) := by
    dsimp only [w]
    simpa using tendsto_const_nhds.add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hδ).mul_const Complex.I)
  have hGcont : Continuous fun z : ℂ ↦ G.eval z := by
    simpa [Polynomial.eval₂_eq_eval_map] using
      Polynomial.continuous_eval₂ G (RingHom.id ℂ)
  have hHcont : Continuous fun z : ℂ ↦ H.eval z := by
    simpa [Polynomial.eval₂_eq_eval_map] using
      Polynomial.continuous_eval₂ H (RingHom.id ℂ)
  have hrhs : Tendsto rhs atTop (nhds (c / Complex.I)) := by
    have hcont : ContinuousAt
        (fun z ↦ G.eval z / (Complex.I * H.eval z)) a := by
      apply hGcont.continuousAt.div (continuous_const.mul hHcont).continuousAt
      exact mul_ne_zero Complex.I_ne_zero hHa
    have ht := hcont.tendsto.comp hw
    have hlim_eq : G.eval a / (Complex.I * H.eval a) = c / Complex.I := by
      dsimp only [c]
      field_simp
    rw [← hlim_eq]
    change Tendsto ((fun z ↦ G.eval z / (Complex.I * H.eval z)) ∘ w) atTop
      (nhds (G.eval a / (Complex.I * H.eval a)))
    exact ht
  have hrhs_im : Tendsto (fun n ↦ (rhs n).im) atTop
      (nhds (c / Complex.I).im) := Complex.continuous_im.continuousAt.tendsto.comp hrhs
  have hrhs_nonpos (n : ℕ) : (rhs n).im ≤ 0 := by
    have hδpos : 0 < δ n := by dsimp only [δ]; positivity
    have hwim : 0 < (w n).im := by
      dsimp only [w]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, Complex.I_im, mul_one]
      rw [ha]
      simpa using hδpos
    have hFne : F.eval (w n) ≠ 0 := hFupper (w n) hwim
    have hHne : H.eval (w n) ≠ 0 := by
      intro hzero
      apply hFne
      rw [← hfactor, Polynomial.eval_mul, hzero, mul_zero]
    have hscale := scaled_ratio_eq F G H a Complex.I 1 (by simpa using hfactor)
      (δ n) hδpos.ne' hHne
    have hscaleim := congrArg Complex.im hscale
    have hpickn := hpick (w n) hwim
    dsimp only [rhs] at hscaleim ⊢
    simp only [pow_one, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] at hscaleim
    rw [← hscaleim]
    exact mul_nonpos_of_nonneg_of_nonpos hδpos.le hpickn
  have hlim_nonpos : (c / Complex.I).im ≤ 0 := by
    apply isClosed_Iic.mem_of_tendsto hrhs_im
    exact Filter.Eventually.of_forall hrhs_nonpos
  have hcre_nonneg : 0 ≤ c.re := by
    rw [Complex.div_I, Complex.neg_im, Complex.mul_im] at hlim_nonpos
    norm_num at hlim_nonpos
    linarith
  have hcre_pos : 0 < c.re := lt_of_le_of_ne hcre_nonneg fun hzero ↦ by
    apply hc0
    apply Complex.ext <;> simp [hzero, hcim]
  have hderiv : F.derivative.eval a = H.eval a := by
    rw [← hfactor, Polynomial.derivative_mul, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_C]
    simp
  rw [hderiv]
  exact hcre_pos

private lemma pick_residue_pos
    (F G : Polynomial ℂ) (hF0 : F ≠ 0) (hcop : IsCoprime F G)
    (hFreal : F.map (starRingEnd ℂ) = F)
    (hGreal : G.map (starRingEnd ℂ) = G)
    (hFupper : ∀ z : ℂ, 0 < z.im → F.eval z ≠ 0)
    (hpick : ∀ z : ℂ, 0 < z.im → (G.eval z / F.eval z).im ≤ 0)
    (a : ℂ) (ha : a.im = 0) (haroot : F.IsRoot a) :
    0 < (G.eval a / F.derivative.eval a).re := by
  have hGa : G.eval a ≠ 0 := by
    intro hzero
    have hdF : Polynomial.X - Polynomial.C a ∣ F :=
      Polynomial.dvd_iff_isRoot.mpr haroot
    have hdG : Polynomial.X - Polynomial.C a ∣ G :=
      Polynomial.dvd_iff_isRoot.mpr hzero
    exact Polynomial.not_isUnit_X_sub_C a (hcop.isUnit_of_dvd' hdF hdG)
  exact pick_residue_pos_of_eval_ne_zero F G hF0 hFreal hGreal hFupper hpick
    a ha haroot hGa

private lemma reflect_eq_reverse_mul_X_pow (f : Polynomial ℂ) {N : ℕ}
    (hf : f.natDegree ≤ N) :
    f.reflect N = f.reverse * Polynomial.X ^ (N - f.natDegree) := by
  have hsum : f.natDegree + (N - f.natDegree) = N := Nat.add_sub_of_le hf
  rw [← hsum]
  simpa [Polynomial.reverse] using
    Polynomial.reflect_mul f (1 : Polynomial ℂ) le_rfl
      (by simp)

private lemma eval_reflect_at_inv (f : Polynomial ℂ) (N : ℕ)
    (hf : f.natDegree ≤ N) (w : ℂ) (hw : w ≠ 0) :
    (f.reflect N).eval w * (w⁻¹ ^ N) = f.eval w⁻¹ := by
  let _ := invertibleOfNonzero (inv_ne_zero hw)
  simpa [invOf_eq_inv] using
    Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) w⁻¹ N f hf

private lemma reflected_ratio_eq (f g : Polynomial ℂ) (N : ℕ)
    (hf : f.natDegree ≤ N) (hg : g.natDegree ≤ N)
    (w : ℂ) (hw : w ≠ 0) (hfw : f.eval (-w⁻¹) ≠ 0) :
    ((g.reflect N).comp (-Polynomial.X)).eval w /
        ((f.reflect N).comp (-Polynomial.X)).eval w =
      g.eval (-w⁻¹) / f.eval (-w⁻¹) := by
  have hnw : -w ≠ 0 := neg_ne_zero.mpr hw
  have hfinv := eval_reflect_at_inv f N hf (-w) hnw
  have hginv := eval_reflect_at_inv g N hg (-w) hnw
  simp only [inv_neg] at hfinv hginv
  have hpow : (-w⁻¹) ^ N ≠ 0 :=
    pow_ne_zero N (neg_ne_zero.mpr (inv_ne_zero hw))
  have hfreflect : (f.reflect N).eval (-w) ≠ 0 := by
    intro hzero
    apply hfw
    rw [← hfinv, hzero, zero_mul]
  rw [Polynomial.eval_comp, Polynomial.eval_comp]
  simp only [Polynomial.eval_neg, Polynomial.eval_X]
  rw [← hginv, ← hfinv]
  field_simp [hpow]

private lemma neg_inv_neg_one_div (t : ℝ) (ht : t ≠ 0) :
    -(-((1 / t : ℝ) : ℂ))⁻¹ = (t : ℂ) := by
  push_cast
  field_simp [ht]

private lemma div_neg_of_pos_re (c : ℂ) (d : ℝ) (hd : 0 < d) (hc : 0 < c.re) :
    (c / (-((d : ℝ) : ℂ))).re < 0 := by
  rw [Complex.div_re]
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
    neg_zero, mul_zero, Complex.normSq_neg, Complex.normSq_ofReal]
  have hd0 : d ≠ 0 := hd.ne'
  field_simp [hd0]
  nlinarith [mul_pos hc hd]

private lemma pick_degree_le_of_nonneg
    (f g : Polynomial ℂ) (hf0 : f ≠ 0)
    (hfreal : f.map (starRingEnd ℂ) = f)
    (hgreal : g.map (starRingEnd ℂ) = g)
    (hfupper : ∀ z : ℂ, 0 < z.im → f.eval z ≠ 0)
    (hpick : ∀ z : ℂ, 0 < z.im → (g.eval z / f.eval z).im ≤ 0)
    (x : ℝ) (hfray : ∀ t : ℝ, x ≤ t → f.eval (t : ℂ) ≠ 0)
    (hnonneg : ∀ t : ℝ, x ≤ t → 0 ≤ (g.eval (t : ℂ) / f.eval (t : ℂ)).re) :
    g.natDegree ≤ f.natDegree := by
  by_cases hg0 : g = 0
  · subst g
    simp
  by_contra hdegree
  have hfg : f.natDegree < g.natDegree := by omega
  let N := g.natDegree
  let F := (f.reflect N).comp (-Polynomial.X)
  let G := (g.reflect N).comp (-Polynomial.X)
  have hfN : f.natDegree ≤ N := hfg.le
  have hgN : g.natDegree ≤ N := le_rfl
  have hF0 : F ≠ 0 := by
    dsimp only [F]
    intro hzero
    rcases Polynomial.comp_eq_zero_iff.mp hzero with hreflect | ⟨_, hconst⟩
    · exact hf0 (Polynomial.reflect_eq_zero_iff.mp hreflect)
    · simp at hconst
  have hFreal : F.map (starRingEnd ℂ) = F := by
    dsimp only [F]
    rw [Polynomial.map_comp, ← Polynomial.reflect_map, hfreal]
    simp
  have hGreal : G.map (starRingEnd ℂ) = G := by
    dsimp only [G]
    rw [Polynomial.map_comp, ← Polynomial.reflect_map, hgreal]
    simp
  have hzupper (z : ℂ) (hz : 0 < z.im) : 0 < (-z⁻¹).im := by
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      norm_num at hz
    rw [Complex.neg_im, Complex.inv_im]
    exact neg_pos.mpr
      (div_neg_of_neg_of_pos (neg_neg_of_pos hz) (Complex.normSq_pos.mpr hz0))
  have hFupper (z : ℂ) (hz : 0 < z.im) : F.eval z ≠ 0 := by
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      norm_num at hz
    have hfz := hfupper (-z⁻¹) (hzupper z hz)
    have hreflect := eval_reflect_at_inv f N hfN (-z) (neg_ne_zero.mpr hz0)
    simp only [inv_neg] at hreflect
    dsimp only [F]
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_neg, Polynomial.eval_X]
    intro hzero
    apply hfz
    rw [← hreflect, hzero, zero_mul]
  have hpickFG (z : ℂ) (hz : 0 < z.im) :
      (G.eval z / F.eval z).im ≤ 0 := by
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      norm_num at hz
    have hfz := hfupper (-z⁻¹) (hzupper z hz)
    have hratio := reflected_ratio_eq f g N hfN hgN z hz0 hfz
    dsimp only [F, G]
    rw [hratio]
    exact hpick (-z⁻¹) (hzupper z hz)
  have hFroot : F.IsRoot 0 := by
    dsimp only [F]
    change ((f.reflect N).comp (-Polynomial.X)).eval 0 = 0
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_neg, Polynomial.eval_X, neg_zero]
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
      Polynomial.revAt_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt hfg
  have hGzero : G.eval 0 ≠ 0 := by
    dsimp only [G, N]
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_neg, Polynomial.eval_X, neg_zero]
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
      Polynomial.revAt_zero]
    exact Polynomial.leadingCoeff_ne_zero.mpr hg0
  have hFmult : F.rootMultiplicity 0 = N - f.natDegree := by
    have hnegX : (-Polynomial.X : Polynomial ℂ) =
        Polynomial.C (-1) * Polynomial.X + Polynomial.C 0 := by
      simp
    dsimp only [F]
    rw [hnegX, Polynomial.rootMultiplicity_comp_C_mul_X_add_C _ (-1) 0 0 (by simp)]
    simp only [mul_zero, add_zero]
    rw [reflect_eq_reverse_mul_X_pow f hfN]
    have hreverse0 : f.reverse ≠ 0 := by simpa using hf0
    have hXpow0 : (Polynomial.X : Polynomial ℂ) ^ (N - f.natDegree) ≠ 0 := by
      exact pow_ne_zero _ Polynomial.X_ne_zero
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hreverse0 hXpow0)]
    have hreval0 : f.reverse.eval 0 ≠ 0 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
      exact Polynomial.leadingCoeff_ne_zero.mpr hf0
    rw [Polynomial.rootMultiplicity_eq_zero (fun hroot ↦ hreval0 hroot)]
    simpa using Polynomial.rootMultiplicity_X_sub_C_pow (0 : ℂ) (N - f.natDegree)
  have hmult := pick_rootMultiplicity_le_one_of_eval_ne_zero F G hF0 hFreal hGreal
    hFupper hpickFG 0 (by simp) hFroot hGzero
  rw [hFmult] at hmult
  have hgap : N - f.natDegree = 1 := by
    have hgap_pos : 0 < N - f.natDegree := Nat.sub_pos_of_lt hfg
    omega
  let H := F /ₘ Polynomial.X
  have hfactor : Polynomial.X * H = F := by
    dsimp only [H]
    have h := Polynomial.pow_mul_divByMonic_rootMultiplicity_eq F 0
    rw [hFmult, hgap] at h
    simpa using h
  have hHzero : H.eval 0 ≠ 0 := by
    dsimp only [H]
    have h := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hF0
    rw [hFmult, hgap] at h
    simpa using h
  have hderiv : F.derivative.eval 0 = H.eval 0 := by
    rw [← hfactor, Polynomial.derivative_mul, Polynomial.derivative_X]
    simp
  have hcpos : 0 < (G.eval 0 / H.eval 0).re := by
    have hres := pick_residue_pos_of_eval_ne_zero F G hF0 hFreal hGreal hFupper
      hpickFG 0 (by simp) hFroot hGzero
    rw [hderiv] at hres
    exact hres
  let δ : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let w : ℕ → ℂ := fun n ↦ -((δ n : ℝ) : ℂ)
  have hδ : Tendsto δ atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hw : Tendsto w atTop (nhds 0) := by
    dsimp only [w]
    simpa using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hδ).neg
  have hGcont : Continuous fun z : ℂ ↦ G.eval z := by
    simpa [Polynomial.eval₂_eq_eval_map] using
      Polynomial.continuous_eval₂ G (RingHom.id ℂ)
  have hHcont : Continuous fun z : ℂ ↦ H.eval z := by
    simpa [Polynomial.eval₂_eq_eval_map] using
      Polynomial.continuous_eval₂ H (RingHom.id ℂ)
  have hquot : Tendsto (fun n ↦ G.eval (w n) / H.eval (w n)) atTop
      (nhds (G.eval 0 / H.eval 0)) := by
    exact (hGcont.continuousAt.div hHcont.continuousAt hHzero).tendsto.comp hw
  have hquotRe : Tendsto (fun n ↦ (G.eval (w n) / H.eval (w n)).re) atTop
      (nhds (G.eval 0 / H.eval 0).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hquot
  have hposEventually : ∀ᶠ n in atTop, 0 < (G.eval (w n) / H.eval (w n)).re :=
    hquotRe (Ioi_mem_nhds hcpos)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt x
  have hxEventually : ∀ᶠ n : ℕ in atTop, x ≤ (n : ℝ) + 1 :=
    (Filter.eventually_ge_atTop n₀).mono fun n hn ↦ by
      have hcast : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
  obtain ⟨n, hnpos, hnx⟩ := Filter.Eventually.exists (hposEventually.and hxEventually)
  let t : ℝ := (n : ℝ) + 1
  have htpos : 0 < t := by
    dsimp only [t]
    positivity
  have hxt : x ≤ t := by simpa [t] using hnx
  have hwt : w n = -(((1 / t : ℝ) : ℂ)) := by
    rfl
  have hwn0 : w n ≠ 0 := by
    rw [hwt]
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (one_div_ne_zero htpos.ne'))
  have hzinv : -(w n)⁻¹ = (t : ℂ) := by
    rw [hwt]
    exact neg_inv_neg_one_div t htpos.ne'
  have hfwn : f.eval (-(w n)⁻¹) ≠ 0 := by
    rw [hzinv]
    exact hfray t hxt
  have hratioFG : G.eval (w n) / F.eval (w n) =
      g.eval (t : ℂ) / f.eval (t : ℂ) := by
    have hratio := reflected_ratio_eq f g N hfN hgN (w n) hwn0 hfwn
    rw [hzinv] at hratio
    simpa only [F, G] using hratio
  have hreflect := eval_reflect_at_inv f N hfN (-(w n)) (neg_ne_zero.mpr hwn0)
  simp only [inv_neg] at hreflect
  have hFwn : F.eval (w n) ≠ 0 := by
    dsimp only [F]
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_neg, Polynomial.eval_X]
    intro hzero
    apply hfwn
    rw [← hreflect, hzero, zero_mul]
  have hHwn : H.eval (w n) ≠ 0 := by
    intro hzero
    apply hFwn
    rw [← hfactor, Polynomial.eval_mul, hzero, mul_zero]
  have hquotient : G.eval (w n) / F.eval (w n) =
      (G.eval (w n) / H.eval (w n)) / w n := by
    rw [← hfactor, Polynomial.eval_mul, Polynomial.eval_X]
    field_simp [hwn0, hHwn]
  have hnegative : (G.eval (w n) / F.eval (w n)).re < 0 := by
    rw [hquotient, hwt]
    exact div_neg_of_pos_re _ (1 / t) (one_div_pos.mpr htpos) hnpos
  have hnonnegative := hnonneg t hxt
  rw [← hratioFG] at hnonnegative
  linarith

private lemma pick_ratio_eq_sum
    (F G : Polynomial ℂ) (hF0 : F ≠ 0) (hcop : IsCoprime F G)
    (hFreal : F.map (starRingEnd ℂ) = F)
    (hGreal : G.map (starRingEnd ℂ) = G)
    (hdegree : G.natDegree ≤ F.natDegree)
    (hroots : ∀ a ∈ F.roots, a.im = 0)
    (hFupper : ∀ z : ℂ, 0 < z.im → F.eval z ≠ 0)
    (hpick : ∀ z : ℂ, 0 < z.im → (G.eval z / F.eval z).im ≤ 0) :
    ∃ q₀ : ℂ, ∀ z : ℂ, F.eval z ≠ 0 →
      G.eval z / F.eval z = q₀ +
        ∑ a ∈ F.roots.toFinset,
          (G.eval a / F.derivative.eval a) * (z - a)⁻¹ := by
  let s := F.roots.toFinset
  have hnodup : F.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro a
    by_cases ha : a ∈ F.roots
    · rw [Polynomial.count_roots]
      exact pick_rootMultiplicity_le_one F G hF0 hcop hFreal hGreal
        hFupper hpick a (hroots a ha) ((Polynomial.mem_roots hF0).mp ha)
    · exact (Multiset.count_eq_zero.mpr ha).le.trans (by omega)
  have hscard : s.card = F.natDegree := by
    rw [show s.card = F.roots.card from Multiset.toFinset_card_of_nodup hnodup]
    exact (IsAlgClosed.splits F).natDegree_eq_card_roots.symm
  let Q := G / F
  let R := G % F
  have hlc0 : F.leadingCoeff⁻¹ ≠ 0 :=
    inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hF0)
  have hQdegree : Q.natDegree = 0 := by
    dsimp only [Q]
    rw [Polynomial.div_def, Polynomial.natDegree_C_mul hlc0,
      Polynomial.natDegree_divByMonic _ (Polynomial.monic_mul_leadingCoeff_inv hF0)]
    rw [Polynomial.natDegree_mul_C hlc0]
    omega
  have hQ : Q = Polynomial.C (Q.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hQdegree
  have hRdegree : R.degree < (s.card : WithBot ℕ) := by
    dsimp only [R]
    rw [hscard]
    simpa [Polynomial.degree_eq_natDegree hF0] using Polynomial.degree_mod_lt G hF0
  have hRinterp : R = Lagrange.interpolate s (fun a : ℂ ↦ a) (fun a ↦ R.eval a) :=
    Lagrange.eq_interpolate (Set.injOn_id _) hRdegree
  have hFnodal : F = Polynomial.C F.leadingCoeff *
      Lagrange.nodal s (fun a : ℂ ↦ a) := by
    calc
      F = Polynomial.C F.leadingCoeff *
          (F.roots.map (fun a ↦ Polynomial.X - Polynomial.C a)).prod :=
        (IsAlgClosed.splits F).eq_prod_roots
      _ = Polynomial.C F.leadingCoeff *
          Lagrange.nodal s (fun a : ℂ ↦ a) := by
        congr 1
        rw [Finset.prod_multiset_map_count, Lagrange.nodal_eq]
        apply Finset.prod_congr rfl
        intro a ha
        have hamem : a ∈ F.roots := by simpa [s] using ha
        rw [(Multiset.nodup_iff_count_eq_one.mp hnodup) a hamem, pow_one]
  refine ⟨Q.coeff 0, fun z hz ↦ ?_⟩
  have hznode (a : ℂ) (ha : a ∈ s) : z ≠ a := by
    intro hza
    subst z
    apply hz
    exact (Polynomial.mem_roots hF0).mp (by simpa [s] using ha)
  have hReval := congrArg (Polynomial.eval z) hRinterp
  rw [Lagrange.eval_interpolate_not_at_node (fun a ↦ R.eval a) hznode] at hReval
  have hFeval := congrArg (Polynomial.eval z) hFnodal
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at hFeval
  have hdiv := congrArg (Polynomial.eval z) (EuclideanDomain.div_add_mod G F)
  simp only [Polynomial.eval_add, Polynomial.eval_mul] at hdiv
  change F.eval z * Q.eval z + R.eval z = G.eval z at hdiv
  rw [hQ] at hdiv
  simp only [Polynomial.eval_C] at hdiv
  rw [← hdiv]
  rw [add_div, mul_div_cancel_left₀ _ hz]
  congr 1
  rw [hReval, hFeval]
  have hnodal_ne : (Lagrange.nodal s (fun a : ℂ ↦ a)).eval z ≠ 0 := by
    exact Lagrange.eval_nodal_not_at_node hznode
  rw [mul_comm F.leadingCoeff, mul_div_mul_left _ _ hnodal_ne]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  have haroot : F.IsRoot a :=
    (Polynomial.mem_roots hF0).mp (by simpa [s] using ha)
  have hRa : R.eval a = G.eval a := by
    have hdiva := congrArg (Polynomial.eval a) (EuclideanDomain.div_add_mod G F)
    simp only [Polynomial.eval_add, Polynomial.eval_mul] at hdiva
    change F.eval a * Q.eval a + R.eval a = G.eval a at hdiva
    rw [haroot, zero_mul, zero_add] at hdiva
    exact hdiva
  have hderiv : F.derivative.eval a = F.leadingCoeff *
      (Lagrange.nodal s (fun a : ℂ ↦ a)).derivative.eval a := by
    have h := congrArg (Polynomial.eval a) (congrArg Polynomial.derivative hFnodal)
    simpa using h
  have hrespos := pick_residue_pos F G hF0 hcop hFreal hGreal
    hFupper hpick a (hroots a (by simpa [s] using ha)) haroot
  have hderiv0 : F.derivative.eval a ≠ 0 := by
    intro hzero
    rw [hzero, div_zero] at hrespos
    norm_num at hrespos
  have hnodal_deriv0 :
      (Lagrange.nodal s (fun a : ℂ ↦ a)).derivative.eval a ≠ 0 := by
    intro hzero
    apply hderiv0
    rw [hderiv, hzero, mul_zero]
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal ha, hRa, hderiv]
  field_simp

private lemma pick_ratio_shift_bounds_coprime
    (F G : Polynomial ℂ) (hF0 : F ≠ 0) (hcop : IsCoprime F G)
    (hFreal : F.map (starRingEnd ℂ) = F)
    (hGreal : G.map (starRingEnd ℂ) = G)
    (hdegree : G.natDegree ≤ F.natDegree)
    (hFupper : ∀ z : ℂ, 0 < z.im → F.eval z ≠ 0)
    (hpick : ∀ z : ℂ, 0 < z.im → (G.eval z / F.eval z).im ≤ 0)
    (x y : ℝ) (hxy : x ≤ y)
    (hroots : ∀ a ∈ F.roots, a.im = 0 ∧ a.re < x) :
    (G.eval (y : ℂ) / F.eval (y : ℂ)).re ≤
        (G.eval (x : ℂ) / F.eval (x : ℂ)).re ∧
      (G.eval (y : ℂ) / F.eval (y : ℂ)).re ≤
        (G.eval (x : ℂ) / F.eval (x : ℂ)).re + (y - x) *
          ((G.derivative.eval (y : ℂ) * F.eval (y : ℂ) -
              G.eval (y : ℂ) * F.derivative.eval (y : ℂ)) /
            F.eval (y : ℂ) ^ 2).re ∧
      ((G.derivative.eval (y : ℂ) * F.eval (y : ℂ) -
            G.eval (y : ℂ) * F.derivative.eval (y : ℂ)) /
          F.eval (y : ℂ) ^ 2).re ≤ 0 := by
  let s := F.roots.toFinset
  have hFne (t : ℝ) (ht : x ≤ t) : F.eval (t : ℂ) ≠ 0 := by
    intro hzero
    have hmem : (t : ℂ) ∈ F.roots := (Polynomial.mem_roots hF0).mpr hzero
    have hlt := (hroots (t : ℂ) hmem).2
    norm_num at hlt
    linarith
  have hxne := hFne x le_rfl
  have hyne := hFne y hxy
  obtain ⟨q₀, hratio⟩ := pick_ratio_eq_sum F G hF0 hcop hFreal hGreal hdegree
    (fun a ha ↦ (hroots a ha).1) hFupper hpick
  have hFdreal : F.derivative.map (starRingEnd ℂ) = F.derivative := by
    rw [← Polynomial.derivative_map, hFreal]
  have hres_im (a : ℂ) (ha : a ∈ s) :
      (G.eval a / F.derivative.eval a).im = 0 := by
    have hamem : a ∈ F.roots := by simpa [s] using ha
    have hGi := eval_im_eq_zero_of_map_star_eq_self G hGreal a (hroots a hamem).1
    have hFi := eval_im_eq_zero_of_map_star_eq_self F.derivative hFdreal a
      (hroots a hamem).1
    rw [Complex.div_im, hGi, hFi]
    simp
  have hres_pos (a : ℂ) (ha : a ∈ s) :
      0 < (G.eval a / F.derivative.eval a).re := by
    have hamem : a ∈ F.roots := by simpa [s] using ha
    exact pick_residue_pos F G hF0 hcop hFreal hGreal hFupper hpick a
      (hroots a hamem).1 ((Polynomial.mem_roots hF0).mp hamem)
  have hrepr (t : ℝ) (ht : x ≤ t) :
      (G.eval (t : ℂ) / F.eval (t : ℂ)).re = q₀.re +
        ∑ a ∈ s, (G.eval a / F.derivative.eval a).re * (t - a.re)⁻¹ := by
    have h := congrArg Complex.re (hratio (t : ℂ) (hFne t ht))
    rw [Complex.add_re] at h
    have hsum_re :
        (∑ a ∈ F.roots.toFinset,
          (G.eval a / F.derivative.eval a) * ((t : ℂ) - a)⁻¹).re =
        ∑ a ∈ F.roots.toFinset,
          ((G.eval a / F.derivative.eval a) * ((t : ℂ) - a)⁻¹).re :=
      map_sum Complex.reCLM _ _
    rw [hsum_re] at h
    have hsum_eq :
        ∑ a ∈ F.roots.toFinset,
          ((G.eval a / F.derivative.eval a) * ((t : ℂ) - a)⁻¹).re =
        ∑ a ∈ s, (G.eval a / F.derivative.eval a).re * (t - a.re)⁻¹ := by
      change (∑ a ∈ s,
        ((G.eval a / F.derivative.eval a) * ((t : ℂ) - a)⁻¹).re) = _
      apply Finset.sum_congr rfl
      intro a ha
      rw [Complex.mul_re, hres_im a ha, inv_sub_real_re t a (hroots a (by
        simpa [s] using ha)).1, inv_sub_real_im t a (hroots a (by
        simpa [s] using ha)).1]
      ring
    rw [hsum_eq] at h
    exact h
  have hslope :
      ((G.derivative.eval (y : ℂ) * F.eval (y : ℂ) -
            G.eval (y : ℂ) * F.derivative.eval (y : ℂ)) /
          F.eval (y : ℂ) ^ 2).re =
        ∑ a ∈ s, -(G.eval a / F.derivative.eval a).re * (y - a.re)⁻¹ ^ 2 := by
    let lhs : ℂ → ℂ := fun z ↦ G.eval z / F.eval z
    let rhs : ℂ → ℂ := fun z ↦ q₀ +
      ∑ a ∈ s, (G.eval a / F.derivative.eval a) * (z - a)⁻¹
    have hleft : HasDerivAt lhs
        ((G.derivative.eval (y : ℂ) * F.eval (y : ℂ) -
            G.eval (y : ℂ) * F.derivative.eval (y : ℂ)) /
          F.eval (y : ℂ) ^ 2) (y : ℂ) := by
      exact (Polynomial.hasDerivAt G (y : ℂ)).div
        (Polynomial.hasDerivAt F (y : ℂ)) hyne
    have hsum : HasDerivAt
        (fun z : ℂ ↦ ∑ a ∈ s,
          (G.eval a / F.derivative.eval a) * (z - a)⁻¹)
        (∑ a ∈ s, -(G.eval a / F.derivative.eval a) *
          ((y : ℂ) - a)⁻¹ * ((y : ℂ) - a)⁻¹) (y : ℂ) := by
      have hraw := HasDerivAt.sum (u := s) fun a ha ↦
        hasDerivAt_mul_inv_sub (G.eval a / F.derivative.eval a) a (y : ℂ) (by
          intro hya
          apply hyne
          rw [hya]
          exact (Polynomial.mem_roots hF0).mp (by simpa [s] using ha))
      apply hraw.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun z ↦ by simp
    have hright : HasDerivAt rhs
        (∑ a ∈ s, -(G.eval a / F.derivative.eval a) *
          ((y : ℂ) - a)⁻¹ * ((y : ℂ) - a)⁻¹) (y : ℂ) := by
      dsimp only [rhs]
      convert (hasDerivAt_const (y : ℂ) q₀).add hsum using 1
      all_goals simp
    have hFcont : Continuous fun z : ℂ ↦ F.eval z := by
      simpa [Polynomial.eval₂_eq_eval_map] using
        Polynomial.continuous_eval₂ F (RingHom.id ℂ)
    have heq : lhs =ᶠ[nhds (y : ℂ)] rhs :=
      (hFcont.continuousAt.eventually_ne hyne).mono fun z hz ↦ hratio z hz
    have hderiv := hleft.unique (hright.congr_of_eventuallyEq heq)
    have hre := congrArg Complex.re hderiv
    have hsum_re :
        (∑ a ∈ s, -(G.eval a / F.derivative.eval a) *
          ((y : ℂ) - a)⁻¹ * ((y : ℂ) - a)⁻¹).re =
        ∑ a ∈ s, (-(G.eval a / F.derivative.eval a) *
          ((y : ℂ) - a)⁻¹ * ((y : ℂ) - a)⁻¹).re :=
      map_sum Complex.reCLM _ _
    rw [hsum_re] at hre
    have hsum_eq :
        ∑ a ∈ s, (-(G.eval a / F.derivative.eval a) *
          ((y : ℂ) - a)⁻¹ * ((y : ℂ) - a)⁻¹).re =
        ∑ a ∈ s, -(G.eval a / F.derivative.eval a).re * (y - a.re)⁻¹ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Complex.mul_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
        hres_im a ha, inv_sub_real_re y a (hroots a (by simpa [s] using ha)).1,
        inv_sub_real_im y a (hroots a (by simpa [s] using ha)).1]
      ring
    rw [hsum_eq] at hre
    simpa [lhs, rhs, mul_assoc] using hre
  have hterm (a : ℂ) (ha : a ∈ s) :
      let c := (G.eval a / F.derivative.eval a).re
      c * (y - a.re)⁻¹ ≤ c * (x - a.re)⁻¹ ∧
        c * (y - a.re)⁻¹ ≤ c * (x - a.re)⁻¹ +
          (y - x) * (-c * (y - a.re)⁻¹ ^ 2) := by
    have hamem : a ∈ F.roots := by simpa [s] using ha
    have hax : 0 < x - a.re := by linarith [(hroots a hamem).2]
    have hxy' : x - a.re ≤ y - a.re := by linarith
    have h := reciprocal_shift_bounds (G.eval a / F.derivative.eval a).re
      (x - a.re) (y - a.re) (hres_pos a ha).le hax hxy'
    simpa [div_eq_mul_inv, mul_assoc] using h
  refine ⟨?_, ?_, ?_⟩
  · rw [hrepr y hxy, hrepr x le_rfl]
    simpa [add_comm] using
      add_le_add_left (Finset.sum_le_sum fun a ha ↦ (hterm a ha).1) q₀.re
  · rw [hrepr y hxy, hrepr x le_rfl, hslope]
    have hsum := Finset.sum_le_sum fun a ha ↦ (hterm a ha).2
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    linarith
  · rw [hslope]
    apply Finset.sum_nonpos
    intro a ha
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hres_pos a ha).le)
      (sq_nonneg _)

private lemma pick_ratio_shift_bounds
    (f g : Polynomial ℂ) (hf0 : f ≠ 0)
    (hfreal : f.map (starRingEnd ℂ) = f)
    (hgreal : g.map (starRingEnd ℂ) = g)
    (hfupper : ∀ z : ℂ, 0 < z.im → f.eval z ≠ 0)
    (hpick : ∀ z : ℂ, 0 < z.im → (g.eval z / f.eval z).im ≤ 0)
    (x y : ℝ) (hxy : x ≤ y)
    (hroots : ∀ a ∈ f.roots, a.im = 0 ∧ a.re < x)
    (hnonneg : ∀ t : ℝ, x ≤ t → 0 ≤ (g.eval (t : ℂ) / f.eval (t : ℂ)).re) :
    (g.eval (y : ℂ) / f.eval (y : ℂ)).re ≤
        (g.eval (x : ℂ) / f.eval (x : ℂ)).re ∧
      (g.eval (y : ℂ) / f.eval (y : ℂ)).re ≤
        (g.eval (x : ℂ) / f.eval (x : ℂ)).re + (y - x) *
          ((g.derivative.eval (y : ℂ) * f.eval (y : ℂ) -
              g.eval (y : ℂ) * f.derivative.eval (y : ℂ)) /
            f.eval (y : ℂ) ^ 2).re ∧
      ((g.derivative.eval (y : ℂ) * f.eval (y : ℂ) -
            g.eval (y : ℂ) * f.derivative.eval (y : ℂ)) /
          f.eval (y : ℂ) ^ 2).re ≤ 0 := by
  have hfne (t : ℝ) (ht : x ≤ t) : f.eval (t : ℂ) ≠ 0 := by
    intro hzero
    have hmem : (t : ℂ) ∈ f.roots := (Polynomial.mem_roots hf0).mpr hzero
    have hlt := (hroots (t : ℂ) hmem).2
    norm_num at hlt
    linarith
  have hdegree := pick_degree_le_of_nonneg f g hf0 hfreal hgreal hfupper hpick x
    hfne hnonneg
  by_cases hg0 : g = 0
  · subst g
    simp
  let _ : GCDMonoid (Polynomial ℂ) := EuclideanDomain.gcdMonoid (Polynomial ℂ)
  let d := EuclideanDomain.gcd f g
  let F := f / d
  let G := g / d
  have hd0 : d ≠ 0 := gcd_ne_zero_of_left hf0
  have hF0 : F ≠ 0 := left_div_gcd_ne_zero hf0
  have hG0 : G ≠ 0 := right_div_gcd_ne_zero hg0
  have hfactorF : d * F = f :=
    EuclideanDomain.mul_div_cancel' hd0 (GCDMonoid.gcd_dvd_left f g)
  have hfactorG : d * G = g :=
    EuclideanDomain.mul_div_cancel' hd0 (GCDMonoid.gcd_dvd_right f g)
  have hcop : IsCoprime F G := isCoprime_div_gcd_div_gcd hg0
  have hdreal : d.map (starRingEnd ℂ) = d := by
    have h := Polynomial.gcd_map (p := f) (q := g) (starRingEnd ℂ)
    rw [hfreal, hgreal] at h
    simpa only [d] using h.symm
  have hFreal : F.map (starRingEnd ℂ) = F := by
    dsimp only [F]
    rw [Polynomial.map_div, hfreal, hdreal]
  have hGreal : G.map (starRingEnd ℂ) = G := by
    dsimp only [G]
    rw [Polynomial.map_div, hgreal, hdreal]
  have hdegreeFG : G.natDegree ≤ F.natDegree := by
    have hfdeg := Polynomial.natDegree_mul hd0 hF0
    have hgdeg := Polynomial.natDegree_mul hd0 hG0
    rw [hfactorF] at hfdeg
    rw [hfactorG] at hgdeg
    omega
  have hFupper (z : ℂ) (hz : 0 < z.im) : F.eval z ≠ 0 := by
    intro hzero
    apply hfupper z hz
    rw [← hfactorF, Polynomial.eval_mul, hzero, mul_zero]
  have hratio (z : ℂ) (hz : 0 < z.im) :
      G.eval z / F.eval z = g.eval z / f.eval z := by
    have hfz := hfupper z hz
    have hdz : d.eval z ≠ 0 := by
      intro hzero
      apply hfz
      rw [← hfactorF, Polynomial.eval_mul, hzero, zero_mul]
    rw [← hfactorF, ← hfactorG, Polynomial.eval_mul, Polynomial.eval_mul]
    field_simp
  have hpickFG (z : ℂ) (hz : 0 < z.im) :
      (G.eval z / F.eval z).im ≤ 0 := by rw [hratio z hz]; exact hpick z hz
  have hrootsF (a : ℂ) (ha : a ∈ F.roots) : a.im = 0 ∧ a.re < x := by
    have hFa : F.eval a = 0 := (Polynomial.mem_roots hF0).mp ha
    have hfa : f.eval a = 0 := by
      rw [← hfactorF, Polynomial.eval_mul, hFa, mul_zero]
    exact hroots a ((Polynomial.mem_roots hf0).mpr hfa)
  have hbounds := pick_ratio_shift_bounds_coprime F G hF0 hcop hFreal hGreal
    hdegreeFG hFupper hpickFG x y hxy hrootsF
  have hratio_real (t : ℝ) (ht : x ≤ t) :
      G.eval (t : ℂ) / F.eval (t : ℂ) =
        g.eval (t : ℂ) / f.eval (t : ℂ) := by
    have hft := hfne t ht
    have hdt : d.eval (t : ℂ) ≠ 0 := by
      intro hzero
      apply hft
      rw [← hfactorF, Polynomial.eval_mul, hzero, zero_mul]
    rw [← hfactorF, ← hfactorG, Polynomial.eval_mul, Polynomial.eval_mul]
    field_simp
  have hslope :
      (G.derivative.eval (y : ℂ) * F.eval (y : ℂ) -
            G.eval (y : ℂ) * F.derivative.eval (y : ℂ)) /
          F.eval (y : ℂ) ^ 2 =
        (g.derivative.eval (y : ℂ) * f.eval (y : ℂ) -
            g.eval (y : ℂ) * f.derivative.eval (y : ℂ)) /
          f.eval (y : ℂ) ^ 2 := by
    have hfy := hfne y hxy
    have hdy : d.eval (y : ℂ) ≠ 0 := by
      intro hzero
      apply hfy
      rw [← hfactorF, Polynomial.eval_mul, hzero, zero_mul]
    rw [← hfactorF, ← hfactorG]
    simp only [Polynomial.eval_mul, Polynomial.derivative_mul, Polynomial.eval_add]
    field_simp
    ring
  rw [hratio_real x le_rfl, hratio_real y hxy, hslope] at hbounds
  exact hbounds

private lemma ksPolynomial_derivative_div_nonneg
    (f : Polynomial ℂ) (hf0 : f ≠ 0) (x t : ℝ) (hxt : x ≤ t)
    (hroots : ∀ a ∈ f.roots, a.im = 0 ∧ a.re < x) :
    0 ≤ (f.derivative.eval (t : ℂ) / f.eval (t : ℂ)).re := by
  have hft : f.eval (t : ℂ) ≠ 0 := by
    intro hzero
    have hmem : (t : ℂ) ∈ f.roots := (Polynomial.mem_roots hf0).mpr hzero
    have hlt := (hroots (t : ℂ) hmem).2
    norm_num at hlt
    linarith
  rw [(IsAlgClosed.splits f).eval_derivative_div_eval_of_ne_zero hft]
  change 0 ≤ Complex.reCLM.toAddMonoidHom
    ((f.roots.map fun z ↦ 1 / ((t : ℂ) - z)).sum)
  rw [map_multiset_sum Complex.reCLM.toAddMonoidHom, Multiset.map_map]
  apply Multiset.sum_nonneg
  intro r hr
  simp only [Multiset.mem_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  change 0 ≤ (1 / ((t : ℂ) - a)).re
  rw [one_div, inv_sub_real_re t a (hroots a ha).1]
  exact inv_nonneg.mpr (sub_nonneg.mpr ((hroots a ha).2.le.trans hxt))

private lemma ksPolynomial_derivative_div_im_nonpos
    (f : Polynomial ℂ) (w : ℂ) (hw : 0 ≤ w.im)
    (hfw : f.eval w ≠ 0) (hroots : ∀ a ∈ f.roots, a.im ≤ 0) :
    (f.derivative.eval w / f.eval w).im ≤ 0 := by
  rw [(IsAlgClosed.splits f).eval_derivative_div_eval_of_ne_zero hfw]
  have hsum (s : Multiset ℂ) (hs : ∀ a ∈ s, a.im ≤ 0) :
      ((s.map fun z ↦ 1 / (w - z)).sum).im ≤ 0 := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_im]
        apply add_nonpos
        · rw [one_div, Complex.inv_im]
          apply div_nonpos_of_nonpos_of_nonneg
          · simp only [Complex.sub_im]
            linarith [hs a (by simp)]
          · exact Complex.normSq_nonneg _
        · apply ih
          intro b hb
          exact hs b (by simp [hb])
  exact hsum f.roots hroots

private def ksAboveRoots {σ : Type*} (p : MvPolynomial σ ℂ) (x : σ → ℝ) : Prop :=
  ∀ y : σ → ℝ, (∀ i, x i ≤ y i) → 0 < (eval (fun i ↦ (y i : ℂ)) p).re

private lemma ksUnivariateSpecialization_data
    {σ : Type*} [DecidableEq σ] {p : MvPolynomial σ ℂ}
    (hp : p.IsRealStable) {x y : σ → ℝ} (hpx : ksAboveRoots p x)
    (hxy : ∀ j, x j ≤ y j) (i : σ) :
    let f := univariateSpecialization i (fun j ↦ (y j : ℂ)) p
    f ≠ 0 ∧ f.map (starRingEnd ℂ) = f ∧
      ∀ a ∈ f.roots, a.im = 0 ∧ a.re < y i := by
  let yC : σ → ℂ := fun j ↦ (y j : ℂ)
  let f := univariateSpecialization i yC p
  have hupdate : Function.update yC i (y i : ℂ) = yC := by
    exact Function.update_eq_self _ _
  have hfeval : f.eval (y i : ℂ) = eval yC p := by
    rw [show f = univariateSpecialization i yC p by rfl,
      eval_univariateSpecialization, hupdate]
  have hpy : 0 < (eval yC p).re := hpx y hxy
  have hf0 : f ≠ 0 := by
    intro hzero
    rw [hzero] at hfeval
    simp only [Polynomial.eval_zero] at hfeval
    have hre := congrArg Complex.re hfeval
    norm_num at hre
    linarith
  have hfreal : f.map (starRingEnd ℂ) = f := by
    dsimp only [f, yC]
    apply map_star_univariateSpecialization i (fun j ↦ (y j : ℂ)) p hp.1
    intro j hji
    simp
  have hrootsLower : ∀ a ∈ f.roots, a.im ≤ 0 := by
    dsimp only [f, yC]
    exact MvPolynomial.IsStable.roots_im_nonpos_univariateSpecialization hp.2 i
      (fun j ↦ (y j : ℂ)) (fun j hji ↦ by simp) hf0
  have hrealRooted : f.IsRealRooted :=
    Polynomial.isRealRooted_of_map_star_eq_self_of_roots_im_nonpos
      f hf0 hfreal hrootsLower
  refine ⟨hf0, hfreal, ?_⟩
  intro a ha
  have haim : a.im = 0 := hrealRooted a ha
  refine ⟨haim, ?_⟩
  by_contra hnot
  push Not at hnot
  let z := Function.update y i a.re
  have hxz : ∀ j, x j ≤ z j := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [z, Function.update_self]
      exact (hxy i).trans (hnot)
    · simp only [z, Function.update_of_ne hji]
      exact hxy j
  have hpz : 0 < (eval (fun j ↦ (z j : ℂ)) p).re := hpx z hxz
  have haroot : f.eval a = 0 := (Polynomial.mem_roots hf0).mp ha
  have haeq : a = (a.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using haim
  have hupdatez : Function.update yC i a = fun j ↦ (z j : ℂ) := by
    funext j
    by_cases hji : j = i
    · subst j
      dsimp only [z]
      simpa only [Function.update_self] using haeq
    · dsimp only [z, yC]
      rw [Function.update_of_ne hji, Function.update_of_ne hji]
  have hzero : eval (fun j ↦ (z j : ℂ)) p = 0 := by
    rw [← hupdatez, ← eval_univariateSpecialization i yC a p]
    exact haroot
  rw [hzero] at hpz
  norm_num at hpz

private lemma ksSpecialization_antiPick
    {σ : Type*} [DecidableEq σ] {p : MvPolynomial σ ℂ}
    (hp : p.IsRealStable) {x : σ → ℝ} (hpx : ksAboveRoots p x) (i j : σ) :
    let f := univariateSpecialization j (fun k ↦ (x k : ℂ)) p
    let g := univariateSpecialization j (fun k ↦ (x k : ℂ)) (pderiv i p)
    ∀ z : ℂ, 0 < z.im → f.eval z ≠ 0 ∧ (g.eval z / f.eval z).im ≤ 0 := by
  let xC : σ → ℂ := fun k ↦ (x k : ℂ)
  let f := univariateSpecialization j xC p
  let g := univariateSpecialization j xC (pderiv i p)
  change ∀ z : ℂ, 0 < z.im → f.eval z ≠ 0 ∧ (g.eval z / f.eval z).im ≤ 0
  have hdata := ksUnivariateSpecialization_data hp hpx (fun k ↦ le_rfl) j
  have hf0 := hdata.1
  have hfroots := hdata.2.2
  intro z hz
  have hfz : f.eval z ≠ 0 := by
    intro hzero
    have hzroot : z ∈ f.roots := (Polynomial.mem_roots hf0).mpr hzero
    linarith [(hfroots z hzroot).1]
  refine ⟨hfz, ?_⟩
  let a := Function.update xC j z
  let q := univariateSpecialization i a p
  have hfeval : f.eval z = eval a p := by
    dsimp only [f, a]
    exact eval_univariateSpecialization j xC z p
  have hqeval : q.eval (a i) = eval a p := by
    dsimp only [q]
    rw [eval_univariateSpecialization]
    rw [Function.update_eq_self]
  have hqne : q.eval (a i) ≠ 0 := by
    rw [hqeval, ← hfeval]
    exact hfz
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero] at hqne
    simp at hqne
  have haroots : ∀ r ∈ q.roots, r.im ≤ 0 := by
    dsimp only [q]
    apply MvPolynomial.IsStable.roots_im_nonpos_univariateSpecialization hp.2 i a
    · intro k hki
      by_cases hkj : k = j
      · subst k
        simp only [a, Function.update_self]
        exact hz.le
      · simp [a, xC, hkj]
    · exact hq0
  have hai : 0 ≤ (a i).im := by
    by_cases hij : i = j
    · subst i
      simp only [a, Function.update_self]
      exact hz.le
    · simp [a, xC, hij]
  have hqbound := ksPolynomial_derivative_div_im_nonpos q (a i) hai hqne haroots
  have hgeval : g.eval z = eval a (pderiv i p) := by
    dsimp only [g, a]
    exact eval_univariateSpecialization j xC z (pderiv i p)
  have hqderiv : q.derivative.eval (a i) = eval a (pderiv i p) := by
    rw [← derivative_univariateSpecialization i a p]
    rw [eval_univariateSpecialization, Function.update_eq_self]
  rw [hgeval, hfeval, ← hqderiv, ← hqeval]
  exact hqbound

private lemma ksPderiv_div_nonneg
    {σ : Type*} {p : MvPolynomial σ ℂ}
    (hp : p.IsRealStable) {x y : σ → ℝ} (hpx : ksAboveRoots p x)
    (hxy : ∀ j, x j ≤ y j) (i : σ) :
    0 ≤ (eval (fun j ↦ (y j : ℂ)) (pderiv i p) /
      eval (fun j ↦ (y j : ℂ)) p).re := by
  classical
  let yC : σ → ℂ := fun j ↦ (y j : ℂ)
  let f := univariateSpecialization i yC p
  have hdata := ksUnivariateSpecialization_data hp hpx hxy i
  have hf0 := hdata.1
  have hfroots := hdata.2.2
  have hbound := ksPolynomial_derivative_div_nonneg f hf0 (y i) (y i) le_rfl hfroots
  have hfeval : f.eval (y i : ℂ) = eval yC p := by
    dsimp only [f]
    rw [eval_univariateSpecialization, Function.update_eq_self]
  have hderiv : f.derivative.eval (y i : ℂ) = eval yC (pderiv i p) := by
    rw [← derivative_univariateSpecialization i yC p]
    rw [eval_univariateSpecialization, Function.update_eq_self]
  rw [hderiv, hfeval] at hbound
  exact hbound

private lemma ksDiv_re_of_im_eq_zero (a b : ℂ) (ha : a.im = 0) (hb : b.im = 0) :
    (a / b).re = a.re / b.re := by
  have haeq : a = (a.re : ℂ) := Complex.ext rfl (by simpa using ha)
  have hbeq : b = (b.re : ℂ) := Complex.ext rfl (by simpa using hb)
  rw [haeq, hbeq]
  norm_cast

private lemma ksLogDerivativeSlope_re
    (a b c e : ℂ) (ha : a.im = 0) (hb : b.im = 0)
    (hc : c.im = 0) (he : e.im = 0) :
    ((e * a - b * c) / a ^ 2).re =
      (e.re * a.re - b.re * c.re) / a.re ^ 2 := by
  have haeq : a = (a.re : ℂ) := Complex.ext rfl (by simpa using ha)
  have hbeq : b = (b.re : ℂ) := Complex.ext rfl (by simpa using hb)
  have hceq : c = (c.re : ℂ) := Complex.ext rfl (by simpa using hc)
  have heeq : e = (e.re : ℂ) := Complex.ext rfl (by simpa using he)
  rw [haeq, hbeq, hceq, heeq]
  norm_cast

private noncomputable def ksBarrierValue {σ : Type*}
    (p : MvPolynomial σ ℂ) (x : σ → ℝ) (i : σ) : ℝ :=
  (eval (fun j ↦ (x j : ℂ)) (pderiv i p)).re /
    (eval (fun j ↦ (x j : ℂ)) p).re

private noncomputable def ksBarrierSlope {σ : Type*}
    (p : MvPolynomial σ ℂ) (x : σ → ℝ) (i j : σ) : ℝ :=
  let a := (eval (fun k ↦ (x k : ℂ)) p).re
  let b := (eval (fun k ↦ (x k : ℂ)) (pderiv i p)).re
  let c := (eval (fun k ↦ (x k : ℂ)) (pderiv j p)).re
  let e := (eval (fun k ↦ (x k : ℂ)) (pderiv j (pderiv i p))).re
  (e * a - b * c) / a ^ 2

private def ksShift {σ : Type*} [DecidableEq σ]
    (x : σ → ℝ) (i : σ) (t : ℝ) : σ → ℝ :=
  Function.update x i (x i + t)

private lemma ksUpdate_complex {σ : Type*} [DecidableEq σ]
    (x : σ → ℝ) (i : σ) (t : ℝ) :
    Function.update (fun k ↦ (x k : ℂ)) i (t : ℂ) =
      fun k ↦ (Function.update x i t k : ℂ) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp
  · simp [hki]

private lemma ksShift_self {σ : Type*} [DecidableEq σ]
    (x : σ → ℝ) (i : σ) (t : ℝ) : ksShift x i t i = x i + t := by
  simp [ksShift]

private lemma ksShift_of_ne {σ : Type*} [DecidableEq σ]
    (x : σ → ℝ) {i j : σ} (hji : j ≠ i) (t : ℝ) : ksShift x i t j = x j := by
  simp [ksShift, hji]

private lemma ksShift_le {σ : Type*} [DecidableEq σ]
    (x : σ → ℝ) (i : σ) {t : ℝ} (ht : 0 ≤ t) : ∀ j, x j ≤ ksShift x i t j := by
  intro j
  by_cases hji : j = i
  · subst j
    rw [ksShift_self]
    linarith
  · rw [ksShift_of_ne x hji]

private lemma ksBarrierValue_shift_bounds
    {σ : Type*} [DecidableEq σ] {p : MvPolynomial σ ℂ}
    (hp : p.IsRealStable) {x : σ → ℝ} (hpx : ksAboveRoots p x)
    (i j : σ) (t : ℝ) (ht : 0 ≤ t) :
    ksBarrierValue p (ksShift x j t) i ≤ ksBarrierValue p x i ∧
      ksBarrierValue p (ksShift x j t) i ≤
        ksBarrierValue p x i + t * ksBarrierSlope p (ksShift x j t) i j ∧
      ksBarrierSlope p (ksShift x j t) i j ≤ 0 := by
  let xC : σ → ℂ := fun k ↦ (x k : ℂ)
  let f := univariateSpecialization j xC p
  let g := univariateSpecialization j xC (pderiv i p)
  have hdata := ksUnivariateSpecialization_data hp hpx (fun k ↦ le_rfl) j
  have hf0 := hdata.1
  have hfreal := hdata.2.1
  have hfroots := hdata.2.2
  have hgreal : g.map (starRingEnd ℂ) = g := by
    dsimp only [g, xC]
    apply map_star_univariateSpecialization j (fun k ↦ (x k : ℂ))
      (pderiv i p) (ksMap_star_pderiv hp.1 i)
    intro k hkj
    simp
  have hanti := ksSpecialization_antiPick hp hpx i j
  change ∀ z : ℂ, 0 < z.im →
    f.eval z ≠ 0 ∧ (g.eval z / f.eval z).im ≤ 0 at hanti
  have hfupper (z : ℂ) (hz : 0 < z.im) : f.eval z ≠ 0 := (hanti z hz).1
  have hpick (z : ℂ) (hz : 0 < z.im) : (g.eval z / f.eval z).im ≤ 0 :=
    (hanti z hz).2
  have hnonneg (s : ℝ) (hs : x j ≤ s) :
      0 ≤ (g.eval (s : ℂ) / f.eval (s : ℂ)).re := by
    let y := Function.update x j s
    have hxy : ∀ k, x k ≤ y k := by
      intro k
      by_cases hkj : k = j
      · subst k
        simpa [y] using hs
      · simp [y, hkj]
    have hbound := ksPderiv_div_nonneg hp hpx hxy i
    have hgeval : g.eval (s : ℂ) = eval (fun k ↦ (y k : ℂ)) (pderiv i p) := by
      dsimp only [g]
      rw [eval_univariateSpecialization, ksUpdate_complex]
    have hfeval : f.eval (s : ℂ) = eval (fun k ↦ (y k : ℂ)) p := by
      dsimp only [f]
      rw [eval_univariateSpecialization, ksUpdate_complex]
    rw [hgeval, hfeval]
    exact hbound
  have hbounds := pick_ratio_shift_bounds f g hf0 hfreal hgreal hfupper hpick
    (x j) (x j + t) (by linarith) hfroots hnonneg
  let y := ksShift x j t
  have hratio_x : (g.eval (x j : ℂ) / f.eval (x j : ℂ)).re =
      ksBarrierValue p x i := by
    have hgeval : g.eval (x j : ℂ) = eval xC (pderiv i p) := by
      dsimp only [g]
      rw [eval_univariateSpecialization, Function.update_eq_self]
    have hfeval : f.eval (x j : ℂ) = eval xC p := by
      dsimp only [f]
      rw [eval_univariateSpecialization, Function.update_eq_self]
    rw [hgeval, hfeval]
    exact ksDiv_re_of_im_eq_zero _ _ (ksEval_real (ksMap_star_pderiv hp.1 i) x)
      (ksEval_real hp.1 x)
  have hratio_y : (g.eval ((x j + t : ℝ) : ℂ) /
      f.eval ((x j + t : ℝ) : ℂ)).re =
      ksBarrierValue p y i := by
    have hgeval : g.eval ((x j + t : ℝ) : ℂ) =
        eval (fun k ↦ (y k : ℂ)) (pderiv i p) := by
      dsimp only [g, y, ksShift]
      rw [eval_univariateSpecialization, ksUpdate_complex]
    have hfeval : f.eval ((x j + t : ℝ) : ℂ) =
        eval (fun k ↦ (y k : ℂ)) p := by
      dsimp only [f, y, ksShift]
      rw [eval_univariateSpecialization, ksUpdate_complex]
    rw [hgeval, hfeval]
    exact ksDiv_re_of_im_eq_zero _ _
      (ksEval_real (ksMap_star_pderiv hp.1 i) y) (ksEval_real hp.1 y)
  have hslope :
      ((g.derivative.eval ((x j + t : ℝ) : ℂ) *
            f.eval ((x j + t : ℝ) : ℂ) -
          g.eval ((x j + t : ℝ) : ℂ) *
            f.derivative.eval ((x j + t : ℝ) : ℂ)) /
        f.eval ((x j + t : ℝ) : ℂ) ^ 2).re = ksBarrierSlope p y i j := by
    have hgeval : g.eval ((x j + t : ℝ) : ℂ) =
        eval (fun k ↦ (y k : ℂ)) (pderiv i p) := by
      dsimp only [g, y, ksShift]
      rw [eval_univariateSpecialization, ksUpdate_complex]
    have hfeval : f.eval ((x j + t : ℝ) : ℂ) =
        eval (fun k ↦ (y k : ℂ)) p := by
      dsimp only [f, y, ksShift]
      rw [eval_univariateSpecialization, ksUpdate_complex]
    have hgderiv : g.derivative.eval ((x j + t : ℝ) : ℂ) =
        eval (fun k ↦ (y k : ℂ)) (pderiv j (pderiv i p)) := by
      rw [← derivative_univariateSpecialization j xC (pderiv i p)]
      dsimp only [y, ksShift]
      rw [eval_univariateSpecialization, ksUpdate_complex]
    have hfderiv : f.derivative.eval ((x j + t : ℝ) : ℂ) =
        eval (fun k ↦ (y k : ℂ)) (pderiv j p) := by
      rw [← derivative_univariateSpecialization j xC p]
      dsimp only [y, ksShift]
      rw [eval_univariateSpecialization, ksUpdate_complex]
    rw [hgeval, hfeval, hgderiv, hfderiv]
    exact ksLogDerivativeSlope_re _ _ _ _ (ksEval_real hp.1 y)
      (ksEval_real (ksMap_star_pderiv hp.1 i) y)
      (ksEval_real (ksMap_star_pderiv hp.1 j) y)
      (ksEval_real (ksMap_star_pderiv (ksMap_star_pderiv hp.1 i) j) y)
  rw [hratio_x, hratio_y, hslope] at hbounds
  simpa [y] using hbounds

private lemma ksBarrierValue_antitone
    {σ : Type*} [Finite σ] {p : MvPolynomial σ ℂ}
    (hp : p.IsRealStable) {x y z : σ → ℝ} (hpx : ksAboveRoots p x)
    (hxy : ∀ k, x k ≤ y k) (hyz : ∀ k, y k ≤ z k) (i : σ) :
    ksBarrierValue p z i ≤ ksBarrierValue p y i := by
  classical
  let _ := Fintype.ofFinite σ
  let w : Finset σ → σ → ℝ := fun S k ↦ if k ∈ S then z k else y k
  have hyw (S : Finset σ) (k : σ) : y k ≤ w S k := by
    by_cases hk : k ∈ S
    · simp [w, hk, hyz k]
    · simp [w, hk]
  have habove (S : Finset σ) : ksAboveRoots p (w S) := by
    intro u hwu
    apply hpx u
    intro k
    exact (hxy k).trans ((hyw S k).trans (hwu k))
  have hstep (S : Finset σ) (a : σ) (ha : a ∉ S) :
      ksBarrierValue p (w (insert a S)) i ≤ ksBarrierValue p (w S) i := by
    have hdelta : 0 ≤ z a - y a := sub_nonneg.mpr (hyz a)
    have hwa : w S a = y a := by simp [w, ha]
    have hupdate : w (insert a S) = ksShift (w S) a (z a - y a) := by
      funext k
      by_cases hka : k = a
      · subst k
        simp [w, ksShift, ha]
      · simp [w, ksShift, hka]
    rw [hupdate]
    exact (ksBarrierValue_shift_bounds hp (habove S) i a (z a - y a) hdelta).1
  have hind (S : Finset σ) : ksBarrierValue p (w S) i ≤ ksBarrierValue p y i := by
    induction S using Finset.induction with
    | empty => simp [w]
    | @insert a S ha ih => exact (hstep S a ha).trans ih
  simpa [w] using hind Finset.univ

private lemma ksBarrierValue_sub_pderiv
    {σ : Type*} (p : MvPolynomial σ ℂ) (y : σ → ℝ) (i j : σ)
    (hpval : 0 < (eval (fun k ↦ (y k : ℂ)) p).re)
    (hphi : ksBarrierValue p y i < 1) :
    ksBarrierValue (p - pderiv i p) y j =
      ksBarrierValue p y j - ksBarrierSlope p y j i /
        (1 - ksBarrierValue p y i) := by
  let a := (eval (fun k ↦ (y k : ℂ)) p).re
  let b := (eval (fun k ↦ (y k : ℂ)) (pderiv i p)).re
  have ha0 : a ≠ 0 := ne_of_gt hpval
  have hba : b < a := by
    dsimp only [ksBarrierValue] at hphi
    exact (div_lt_one hpval).mp hphi
  have hab0 : a - b ≠ 0 := ne_of_gt (sub_pos.mpr hba)
  dsimp only [ksBarrierValue, ksBarrierSlope]
  simp only [map_sub, Complex.sub_re]
  rw [MvPolynomial.pderiv_comm j i p]
  dsimp only [a, b] at ha0 hab0 ⊢
  field_simp
  ring

private lemma ksBarrier_step
    {σ : Type*} [Finite σ] [DecidableEq σ] {p : MvPolynomial σ ℂ}
    (hp : p.IsRealStable) {x : σ → ℝ} (hpx : ksAboveRoots p x)
    (i : σ) (δ : ℝ) (hδ : 0 < δ)
    (hbar : ksBarrierValue p x i ≤ 1 - 1 / δ) :
    let q := p - pderiv i p
    let y := ksShift x i δ
    q.IsRealStable ∧ ksAboveRoots q y ∧
      ∀ j, ksBarrierValue q y j ≤ ksBarrierValue p x j := by
  let q := p - pderiv i p
  let y := ksShift x i δ
  have hxy : ∀ k, x k ≤ y k := ksShift_le x i hδ.le
  have hpy : 0 < (eval (fun k ↦ (y k : ℂ)) p).re := hpx y hxy
  have hshift_i := ksBarrierValue_shift_bounds hp hpx i i δ hδ.le
  have hphiy_le : ksBarrierValue p y i ≤ 1 - 1 / δ := hshift_i.1.trans hbar
  have hinvpos : 0 < 1 / δ := one_div_pos.mpr hδ
  have hphiy_lt : ksBarrierValue p y i < 1 := by linarith
  have hqabove : ksAboveRoots q y := by
    intro z hyz
    have hxz : ∀ k, x k ≤ z k := fun k ↦ (hxy k).trans (hyz k)
    have hpz : 0 < (eval (fun k ↦ (z k : ℂ)) p).re := hpx z hxz
    have hphiz_le := ksBarrierValue_antitone hp hpx hxy hyz i
    have hphiz_lt : ksBarrierValue p z i < 1 :=
      lt_of_le_of_lt (hphiz_le.trans hphiy_le) (by linarith)
    have hderiv_lt :
        (eval (fun k ↦ (z k : ℂ)) (pderiv i p)).re <
          (eval (fun k ↦ (z k : ℂ)) p).re := by
      dsimp only [ksBarrierValue] at hphiz_lt
      exact (div_lt_one hpz).mp hphiz_lt
    dsimp only [q]
    simp only [map_sub, Complex.sub_re]
    linarith
  refine ⟨MvPolynomial.IsRealStable.sub_pderiv hp i, hqabove, ?_⟩
  intro j
  have hshift := ksBarrierValue_shift_bounds hp hpx j i δ hδ.le
  have hslope : ksBarrierSlope p y j i ≤ 0 := hshift.2.2
  have hdenom : 1 / δ ≤ 1 - ksBarrierValue p y i := by linarith
  have hdenom_pos : 0 < 1 - ksBarrierValue p y i := hinvpos.trans_le hdenom
  have hprod_pre := mul_le_mul_of_nonneg_left hdenom hδ.le
  have hδinv : δ * (1 / δ) = 1 := by field_simp
  rw [hδinv] at hprod_pre
  have hmul_nonpos := mul_nonpos_of_nonpos_of_nonneg hslope
    (sub_nonneg.mpr hprod_pre)
  have hmul : δ * ksBarrierSlope p y j i *
      (1 - ksBarrierValue p y i) ≤ ksBarrierSlope p y j i := by
    nlinarith
  have hquot : δ * ksBarrierSlope p y j i ≤
      ksBarrierSlope p y j i / (1 - ksBarrierValue p y i) :=
    (le_div_iff₀ hdenom_pos).2 hmul
  rw [ksBarrierValue_sub_pderiv p y i j hpy hphiy_lt]
  linarith [hshift.2.1]

private def ksShiftList {σ : Type*} [DecidableEq σ]
    (indices : List σ) (x : σ → ℝ) (δ : ℝ) : σ → ℝ :=
  indices.foldl (fun y i ↦ ksShift y i δ) x

private lemma ksShiftList_apply {σ : Type*} [DecidableEq σ]
    (indices : List σ) (x : σ → ℝ) (δ : ℝ) (k : σ) :
    ksShiftList indices x δ k = x k + (indices.count k : ℝ) * δ := by
  induction indices generalizing x with
  | nil => simp [ksShiftList]
  | cons i indices ih =>
      rw [show ksShiftList (i :: indices) x δ =
        ksShiftList indices (ksShift x i δ) δ by rfl, ih]
      by_cases hki : k = i
      · subst k
        simp [ksShift]
        ring
      · have hik : i ≠ k := Ne.symm hki
        simp [ksShift, hki, hik]

private lemma ksBarrier_iterate
    {σ : Type*} [Finite σ] [DecidableEq σ] {p : MvPolynomial σ ℂ}
    (hp : p.IsRealStable) {x : σ → ℝ} (hpx : ksAboveRoots p x)
    (indices : List σ) (δ : ℝ) (hδ : 0 < δ)
    (hbar : ∀ i ∈ indices, ksBarrierValue p x i ≤ 1 - 1 / δ) :
    let q := mixedDifferential indices p
    let y := ksShiftList indices x δ
    q.IsRealStable ∧ ksAboveRoots q y := by
  induction indices generalizing p x with
  | nil => exact ⟨hp, hpx⟩
  | cons i indices ih =>
      have hstep := ksBarrier_step hp hpx i δ hδ (hbar i (by simp))
      apply ih hstep.1 hstep.2.1
      intro j hj
      exact (hstep.2.2 j).trans (hbar j (by simp [hj]))

private lemma ksPderiv_bind_add_C
    {σ R : Type*} [CommRing R]
    (a : σ → R) (p : MvPolynomial σ R) (i : σ) :
    pderiv i (bind₁ (fun j ↦ X j + C (a j)) p) =
      bind₁ (fun j ↦ X j + C (a j)) (pderiv i p) := by
  classical
  let f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
    bind₁ (fun j ↦ X j + C (a j))
  change pderiv i (f p) = f (pderiv i p)
  induction p using MvPolynomial.induction_on with
  | C r => simp [f]
  | add p q hp hq =>
      calc
        pderiv i (f (p + q)) = pderiv i (f p + f q) :=
          congrArg (pderiv i) (f.map_add p q)
        _ = pderiv i (f p) + pderiv i (f q) := (pderiv i).map_add _ _
        _ = f (pderiv i p) + f (pderiv i q) := by rw [hp, hq]
        _ = f (pderiv i p + pderiv i q) := (f.map_add _ _).symm
        _ = f (pderiv i (p + q)) := by rw [(pderiv i).map_add]
  | mul_X p j hp =>
      have hXderiv : pderiv i (f (X j)) = f (pderiv i (X j)) := by
        by_cases hij : i = j
        · subst j
          simp [f]
        · simp [f, pderiv_X, hij]
      calc
        pderiv i (f (p * X j)) = pderiv i (f p * f (X j)) :=
          congrArg (pderiv i) (f.map_mul p (X j))
        _ = pderiv i (f p) * f (X j) + f p * pderiv i (f (X j)) :=
          pderiv_mul
        _ = f (pderiv i p) * f (X j) + f p * f (pderiv i (X j)) := by
          rw [hp, hXderiv]
        _ = f (pderiv i p * X j + p * pderiv i (X j)) := by
          symm
          calc
            f (pderiv i p * X j + p * pderiv i (X j)) =
                f (pderiv i p * X j) + f (p * pderiv i (X j)) :=
              f.map_add _ _
            _ = f (pderiv i p) * f (X j) + f p * f (pderiv i (X j)) :=
              congrArg₂ (· + ·) (f.map_mul _ _) (f.map_mul _ _)
        _ = f (pderiv i (p * X j)) := by rw [pderiv_mul]

private lemma ksBind_mixedDifferential_add_C
    {σ R : Type*} [CommRing R]
    (a : σ → R) (is : List σ) (p : MvPolynomial σ R) :
    bind₁ (fun j ↦ X j + C (a j)) (mixedDifferential is p) =
      mixedDifferential is (bind₁ (fun j ↦ X j + C (a j)) p) := by
  induction is generalizing p with
  | nil => rfl
  | cons i is ih =>
      rw [mixedDifferential_cons, ih, mixedDifferential_cons, map_sub,
        ksPderiv_bind_add_C]

private def ksMatrixOffset {m : ℕ} (c : ℂ) : Unit ⊕ Fin m → ℂ :=
  Sum.elim (fun _ ↦ 0) (fun _ ↦ c)

private def ksScalarOffset {m : ℕ} (c : ℂ) : Unit ⊕ Fin m → ℂ :=
  Sum.elim (fun _ ↦ c) (fun _ ↦ 0)

private lemma ksBind_mixedDetPolynomial_matrixOffset_eq_scalarOffset
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (hsum : ∑ i, A i = 1) (c : ℂ) :
    bind₁ (fun j ↦ X j + C (ksMatrixOffset c j)) (mixedDetPolynomial A) =
      bind₁ (fun j ↦ X j + C (ksScalarOffset c j)) (mixedDetPolynomial A) := by
  apply MvPolynomial.funext
  intro z
  simp only [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
  simp only [map_add, eval₂Hom_X', eval₂Hom_C, RingHom.id_apply]
  change eval (fun i ↦ z i + ksMatrixOffset c i) (mixedDetPolynomial A) =
    eval (fun i ↦ z i + ksScalarOffset c i) (mixedDetPolynomial A)
  rw [eval_mixedDetPolynomial, eval_mixedDetPolynomial]
  congr 1
  ext a b
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply]
  have hsum_apply : ∑ i, A i a b = (1 : Matrix d d ℂ) a b := by
    simpa only [Matrix.sum_apply] using
      congrArg (fun M : Matrix d d ℂ ↦ M a b) hsum
  by_cases hab : a = b
  · subst b
    have hsum_diag : ∑ i, A i a a = 1 := by simpa using hsum_apply
    simp only [ksMatrixOffset, ksScalarOffset, Sum.elim_inl, Sum.elim_inr,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq, smul_eq_mul, add_zero,
      ]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsum_diag]
    ring
  · have hsum_off : ∑ i, A i a b = 0 := by
      simpa [Matrix.one_apply, hab] using hsum_apply
    simp only [ksMatrixOffset, ksScalarOffset, Sum.elim_inl, Sum.elim_inr,
      Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hab, smul_eq_mul,
      add_zero, zero_add]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsum_off]
    ring

private lemma ksEval_bind_add_C
    {σ R : Type*} [CommRing R] (a z : σ → R) (p : MvPolynomial σ R) :
    eval z (bind₁ (fun j ↦ X j + C (a j)) p) = eval (fun j ↦ z j + a j) p := by
  simp only [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁, map_add, eval₂Hom_X',
    eval₂Hom_C, RingHom.id_apply]

private lemma ksEval_mixedDifferential_diagonal_shift
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (hsum : ∑ i, A i = 1)
    (is : List (Unit ⊕ Fin m)) (s c : ℂ) :
    eval (Sum.elim (fun _ ↦ s) (fun _ ↦ c))
        (mixedDifferential is (mixedDetPolynomial A)) =
      eval (Sum.elim (fun _ ↦ s + c) (fun _ ↦ 0))
        (mixedDifferential is (mixedDetPolynomial A)) := by
  let p := mixedDetPolynomial A
  let q := mixedDifferential is p
  have hbind :
      bind₁ (fun j ↦ X j + C (ksMatrixOffset c j)) q =
        bind₁ (fun j ↦ X j + C (ksScalarOffset c j)) q := by
    calc
      bind₁ (fun j ↦ X j + C (ksMatrixOffset c j)) q =
          mixedDifferential is
            (bind₁ (fun j ↦ X j + C (ksMatrixOffset c j)) p) :=
        ksBind_mixedDifferential_add_C _ _ _
      _ = mixedDifferential is
          (bind₁ (fun j ↦ X j + C (ksScalarOffset c j)) p) := by
        rw [ksBind_mixedDetPolynomial_matrixOffset_eq_scalarOffset A hsum c]
      _ = bind₁ (fun j ↦ X j + C (ksScalarOffset c j)) q :=
        (ksBind_mixedDifferential_add_C _ _ _).symm
  let z : Unit ⊕ Fin m → ℂ := Sum.elim (fun _ ↦ s) (fun _ ↦ 0)
  have heval := congrArg (eval z) hbind
  rw [ksEval_bind_add_C, ksEval_bind_add_C] at heval
  have hmatrix : (fun j ↦ z j + ksMatrixOffset c j) =
      Sum.elim (fun _ ↦ s) (fun _ ↦ c) := by
    funext j
    rcases j with u | i
    · cases u
      simp [z, ksMatrixOffset]
    · simp [z, ksMatrixOffset]
  have hscalar : (fun j ↦ z j + ksScalarOffset c j) =
      Sum.elim (fun _ ↦ s + c) (fun _ ↦ 0) := by
    funext j
    rcases j with u | i
    · cases u
      simp [z, ksScalarOffset]
    · simp [z, ksScalarOffset]
  rw [hmatrix, hscalar] at heval
  exact heval

private def ksScalarPoint {m : ℕ} (t : ℝ) : Unit ⊕ Fin m → ℝ :=
  Sum.elim (fun _ ↦ t) (fun _ ↦ 0)

private lemma ksEval_mixedDetPolynomial_scalarPoint
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (t : ℝ) :
    eval (fun j ↦ (ksScalarPoint t j : ℂ)) (mixedDetPolynomial A) =
      (t : ℂ) ^ Fintype.card d := by
  rw [eval_mixedDetPolynomial]
  simp only [ksScalarPoint, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_zero,
    zero_smul, Finset.sum_const_zero, add_zero, Matrix.scalar_apply,
    Matrix.det_diagonal]
  simp

private lemma ksUnivariateSpecialization_mixedDetPolynomial_scalarPoint
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (i : Fin m) (t : ℝ) :
    univariateSpecialization (Sum.inr i) (fun j ↦ (ksScalarPoint t j : ℂ))
        (mixedDetPolynomial A) =
      Matrix.det
        ((Matrix.scalar d (t : ℂ)).map Polynomial.C +
          (Polynomial.X : Polynomial ℂ) • (A i).map Polynomial.C) := by
  apply Polynomial.funext
  intro u
  rw [eval_univariateSpecialization, eval_mixedDetPolynomial]
  symm
  change (Polynomial.evalRingHom u)
    (Matrix.det
      ((Matrix.scalar d (t : ℂ)).map Polynomial.C +
        (Polynomial.X : Polynomial ℂ) • (A i).map Polynomial.C)) = _
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply]
  by_cases hab : a = b
  · subst b
    simp only [ksScalarPoint, Sum.elim_inl, Matrix.scalar_apply,
      map_zero, Matrix.diagonal_map,
      RingHom.mapMatrix_apply, Polynomial.coe_evalRingHom, Matrix.map_apply,
      Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul,
      Polynomial.X_mul_C, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, ne_eq, reduceCtorEq,
      not_false_eq_true, Function.update_of_ne, Sum.update_inr_apply_inr]
    rw [Finset.sum_eq_single i]
    · simp [mul_comm]
    · intro j hj hji
      simp [Function.update_of_ne hji]
    · simp
  · simp only [ksScalarPoint, Sum.elim_inl, Matrix.scalar_apply,
      map_zero, Matrix.diagonal_map, Matrix.diagonal_apply_ne _ hab,
      RingHom.mapMatrix_apply, Polynomial.coe_evalRingHom, Matrix.map_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Polynomial.X_mul_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, ne_eq, reduceCtorEq, not_false_eq_true,
      Function.update_of_ne, Sum.update_inr_apply_inr]
    rw [Finset.sum_eq_single i]
    · simp [mul_comm]
    · intro j hj hji
      simp [Function.update_of_ne hji]
    · simp

private lemma ksDetLinear_scalar_div_det
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) (t : ℂ) (ht : t ≠ 0) :
    Matrix.detLinear (Matrix.scalar d t) A / Matrix.det (Matrix.scalar d t) =
      Matrix.trace A / t := by
  let B : Matrix d d (Polynomial ℂ) :=
    1 + (Polynomial.X : Polynomial ℂ) • ((t⁻¹ • A).map Polynomial.C)
  have hunit : Polynomial.C t * Polynomial.C t⁻¹ = 1 := by
    rw [← map_mul]
    simp [ht]
  have hscale (x : ℂ) :
      Polynomial.C t *
          (Polynomial.C (t⁻¹ * x) * Polynomial.X) =
        Polynomial.C x * Polynomial.X := by
    calc
      Polynomial.C t *
          (Polynomial.C (t⁻¹ * x) * Polynomial.X) =
          (Polynomial.C t * Polynomial.C t⁻¹) *
            (Polynomial.C x * Polynomial.X) := by
        rw [map_mul]
        ring
      _ = Polynomial.C x * Polynomial.X := by rw [hunit, one_mul]
  have hmatrix :
      (Matrix.scalar d t).map Polynomial.C +
          (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C =
        Polynomial.C t • B := by
    apply Matrix.ext
    intro a b
    by_cases hab : a = b
    · subst b
      simp only [B, Matrix.scalar_apply, map_zero, Matrix.diagonal_map,
        Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
        Matrix.map_apply, smul_eq_mul, Polynomial.X_mul_C, Matrix.one_apply_eq,
        ]
      rw [mul_add, mul_one, hscale]
    · simp only [B, Matrix.scalar_apply, map_zero, Matrix.diagonal_map,
        Matrix.diagonal_apply_ne _ hab, Matrix.add_apply, Matrix.smul_apply,
        Matrix.map_apply, smul_eq_mul, Polynomial.X_mul_C,
        Matrix.one_apply_ne hab, zero_add]
      exact (hscale (A a b)).symm
  have hdet :
      Matrix.det
          ((Matrix.scalar d t).map Polynomial.C +
            (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C) =
        Polynomial.C (t ^ Fintype.card d) * Matrix.det B := by
    rw [hmatrix, Matrix.det_smul]
    simp
  have hlinear : Matrix.detLinear (Matrix.scalar d t) A =
      t ^ Fintype.card d * (t⁻¹ * Matrix.trace A) := by
    rw [← Matrix.coeff_one_det_add_X_smul, hdet, Polynomial.coeff_C_mul]
    dsimp only [B]
    rw [Matrix.coeff_det_one_add_X_smul_one, Matrix.trace_smul]
    simp
  have hdetScalar : Matrix.det (Matrix.scalar d t) = t ^ Fintype.card d := by
    simp [Matrix.scalar_apply, Matrix.det_diagonal]
  rw [hlinear, hdetScalar]
  have hpow : t ^ Fintype.card d ≠ 0 := pow_ne_zero _ ht
  field_simp

private lemma ksEval_pderiv_mixedDetPolynomial_scalarPoint
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (i : Fin m) (t : ℝ) :
    eval (fun j ↦ (ksScalarPoint t j : ℂ))
        (pderiv (Sum.inr i) (mixedDetPolynomial A)) =
      Matrix.detLinear (Matrix.scalar d (t : ℂ)) (A i) := by
  let z : Unit ⊕ Fin m → ℂ := fun j ↦ (ksScalarPoint t j : ℂ)
  let f := univariateSpecialization (Sum.inr i) z (mixedDetPolynomial A)
  calc
    eval z (pderiv (Sum.inr i) (mixedDetPolynomial A)) =
        (univariateSpecialization (Sum.inr i) z
          (pderiv (Sum.inr i) (mixedDetPolynomial A))).eval 0 := by
      rw [eval_univariateSpecialization]
      congr 2
      funext j
      by_cases hji : j = Sum.inr i
      · subst j
        simp [z, ksScalarPoint]
      · simp [hji]
    _ = f.derivative.eval 0 := by
      rw [← derivative_univariateSpecialization]
    _ = f.coeff 1 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
      norm_num
    _ = Matrix.detLinear (Matrix.scalar d (t : ℂ)) (A i) := by
      rw [show f = univariateSpecialization (Sum.inr i)
          (fun j ↦ (ksScalarPoint t j : ℂ)) (mixedDetPolynomial A) by rfl]
      rw [ksUnivariateSpecialization_mixedDetPolynomial_scalarPoint]
      exact Matrix.coeff_one_det_add_X_smul _ _

private lemma ksBarrierValue_mixedDetPolynomial_scalarPoint
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (i : Fin m) (t : ℝ) (ht : 0 < t) :
    ksBarrierValue (mixedDetPolynomial A) (ksScalarPoint t) (Sum.inr i) =
      (Matrix.trace (A i)).re / t := by
  unfold ksBarrierValue
  rw [ksEval_pderiv_mixedDetPolynomial_scalarPoint,
    ksEval_mixedDetPolynomial_scalarPoint]
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hratio := ksDetLinear_scalar_div_det (A i) (t : ℂ) htC
  have hdetScalar : Matrix.det (Matrix.scalar d (t : ℂ)) =
      (t : ℂ) ^ Fintype.card d := by
    simp [Matrix.scalar_apply, Matrix.det_diagonal]
  rw [hdetScalar] at hratio
  have hpowC : (t : ℂ) ^ Fintype.card d ≠ 0 := pow_ne_zero _ htC
  have hlinear : Matrix.detLinear (Matrix.scalar d (t : ℂ)) (A i) =
      Matrix.trace (A i) / (t : ℂ) * (t : ℂ) ^ Fintype.card d :=
    (div_eq_iff hpowC).mp hratio
  rw [hlinear]
  have hpow_cast : (t : ℂ) ^ Fintype.card d =
      ((t ^ Fintype.card d : ℝ) : ℂ) :=
    (Complex.ofReal_pow t _).symm
  have hpow_re : ((t : ℂ) ^ Fintype.card d).re = t ^ Fintype.card d := by
    calc
      ((t : ℂ) ^ Fintype.card d).re =
          (((t ^ Fintype.card d : ℝ) : ℂ)).re := congrArg Complex.re hpow_cast
      _ = t ^ Fintype.card d := Complex.ofReal_re _
  have hpow_im : ((t : ℂ) ^ Fintype.card d).im = 0 := by
    calc
      ((t : ℂ) ^ Fintype.card d).im =
          (((t ^ Fintype.card d : ℝ) : ℂ)).im := congrArg Complex.im hpow_cast
      _ = 0 := Complex.ofReal_im _
  norm_num [Complex.div_re, Complex.div_im]
  rw [hpow_re, hpow_im]
  have hpowR : t ^ Fintype.card d ≠ 0 := pow_ne_zero _ ht.ne'
  field_simp
  ring

private lemma ksAboveRoots_mixedDetPolynomial_scalarPoint
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (hA : ∀ i, (A i).PosSemidef)
    (t : ℝ) (ht : 0 < t) :
    ksAboveRoots (mixedDetPolynomial A) (ksScalarPoint t) := by
  intro y hxy
  rw [eval_mixedDetPolynomial]
  have hscalar_pos : 0 < y (Sum.inl ()) :=
    ht.trans_le (hxy (Sum.inl ()))
  have hscalar : (Matrix.scalar d (y (Sum.inl ()) : ℂ)).PosDef := by
    rw [Matrix.scalar_apply]
    apply Matrix.PosDef.diagonal
    intro i
    exact_mod_cast hscalar_pos
  have hsumPSD : (∑ i, (y (Sum.inr i) : ℂ) • A i).PosSemidef := by
    simpa only [Finset.sum_const_zero, Finset.sum_filter] using
      Matrix.posSemidef_sum Finset.univ (fun i hi ↦
        (hA i).smul (by
          have hy : 0 ≤ y (Sum.inr i) := by
            simpa [ksScalarPoint] using hxy (Sum.inr i)
          exact_mod_cast hy))
  exact (RCLike.pos_iff.mp (hscalar.add_posSemidef hsumPSD).det_pos).1

private lemma ksEval_mixedCharacteristicPolynomial
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (x : ℂ) :
    Polynomial.eval x (mixedCharacteristicPolynomial A) =
      eval (Sum.elim (fun _ ↦ x) (fun _ ↦ 0))
        (mixedDifferential ((List.finRange m).map Sum.inr)
          (mixedDetPolynomial A)) := by
  let q := mixedDifferential ((List.finRange m).map Sum.inr) (mixedDetPolynomial A)
  change (Polynomial.evalRingHom x)
    ((eval₂Hom Polynomial.C (Sum.elim (fun _ ↦ Polynomial.X) (fun _ ↦ 0))) q) = _
  change ((Polynomial.evalRingHom x).comp
    (eval₂Hom Polynomial.C (Sum.elim (fun _ ↦ Polynomial.X) (fun _ ↦ 0)))) q = _
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro j
    rcases j with u | i
    · cases u
      simp
    · simp

/-- **Marcus--Spielman--Srivastava barrier bound.** Let $d$ be a nonempty finite index set, let
$A_1, \dots, A_m$ be positive semidefinite complex $d \times d$ matrices with $\sum_i A_i = I$,
and let $\eta \ge 0$ be a real number such that $\operatorname{Re} \operatorname{tr} A_i \le \eta$
for every $i$. Then the largest real part of a root of the mixed characteristic polynomial of
$A_1, \dots, A_m$ is at most $(1 + \sqrt{\eta})^2$. -/
public theorem mixedCharacteristicPolynomial_maxRealRoot_le
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (A : Fin m → Matrix d d ℂ) (η : ℝ) (hη : 0 ≤ η)
    (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i = 1)
    (htrace : ∀ i, (Matrix.trace (A i)).re ≤ η) :
    (mixedCharacteristicPolynomial A).maxRealRoot ≤ (1 + Real.sqrt η) ^ 2 := by
  by_cases hηzero : η = 0
  · subst η
    have hAzero : ∀ i, A i = 0 := by
      intro i
      apply (hA i).trace_eq_zero_iff.mp
      have htrace_nonneg := RCLike.nonneg_iff.mp (hA i).trace_nonneg
      apply Complex.ext
      · norm_num
        have htrace_le := htrace i
        have htrace_re_nonneg : 0 ≤ (Matrix.trace (A i)).re := by
          simpa using htrace_nonneg.1
        linarith
      · simpa using htrace_nonneg.2
    obtain ⟨j⟩ := ‹Nonempty d›
    have hsumzero : ∑ i, A i = 0 := by simp [hAzero]
    rw [hsumzero] at hsum
    have hentry := congrArg (fun M : Matrix d d ℂ ↦ M j j) hsum
    simp at hentry
  · have hηpos : 0 < η := lt_of_le_of_ne hη (Ne.symm hηzero)
    let s := Real.sqrt η
    let t := s + η
    let δ := 1 + s
    have hspos : 0 < s := by
      exact Real.sqrt_pos.2 hηpos
    have hsquare : s ^ 2 = η := by
      exact Real.sq_sqrt hη
    have htpos : 0 < t := by
      dsimp only [t]
      linarith
    have hδpos : 0 < δ := by
      dsimp only [δ]
      linarith
    have htprod : t = s * δ := by
      dsimp only [t, δ]
      rw [← hsquare]
      ring
    have hparameter : η / t = 1 - 1 / δ := by
      rw [← hsquare, htprod]
      dsimp only [δ]
      field_simp [hspos.ne']
      ring
    let p := mixedDetPolynomial A
    let x : Unit ⊕ Fin m → ℝ := ksScalarPoint t
    let indices : List (Unit ⊕ Fin m) :=
      (List.finRange m).map (Sum.inr : Fin m → Unit ⊕ Fin m)
    have hp : p.IsRealStable := mixedDetPolynomial_isRealStable_of_posSemidef A hA
    have hpx : ksAboveRoots p x :=
      ksAboveRoots_mixedDetPolynomial_scalarPoint A hA t htpos
    have hbar : ∀ i ∈ indices, ksBarrierValue p x i ≤ 1 - 1 / δ := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      rw [show ksBarrierValue p x (Sum.inr i) =
          (Matrix.trace (A i)).re / t by
        exact ksBarrierValue_mixedDetPolynomial_scalarPoint A i t htpos]
      rw [← hparameter]
      exact div_le_div_of_nonneg_right (htrace i) htpos.le
    have hiter := ksBarrier_iterate hp hpx indices δ hδpos hbar
    let q := mixedDifferential indices p
    let y := ksShiftList indices x δ
    have hqAbove : ksAboveRoots q y := hiter.2
    have hyLeft : y (Sum.inl ()) = t := by
      rw [show y = ksShiftList indices x δ by rfl, ksShiftList_apply]
      have hcount :
          @List.count (Unit ⊕ Fin m) instBEqOfDecidableEq (Sum.inl ()) indices = 0 := by
        rw [@List.count_eq_zero (Unit ⊕ Fin m) instBEqOfDecidableEq
          (by infer_instance)]
        simp [indices]
      rw [hcount]
      simp [x, ksScalarPoint]
    have hyRight (i : Fin m) : y (Sum.inr i) = δ := by
      rw [show y = ksShiftList indices x δ by rfl, ksShiftList_apply]
      have hcount :
          @List.count (Unit ⊕ Fin m) instBEqOfDecidableEq (Sum.inr i) indices = 1 := by
        rw [show indices = (List.finRange m).map
          (Sum.inr : Fin m → Unit ⊕ Fin m) by rfl]
        rw [@List.count_map_of_injective (Fin m) (Unit ⊕ Fin m)
          instBEqOfDecidableEq (by infer_instance) instBEqOfDecidableEq
          (by infer_instance) (List.finRange m)
          (Sum.inr : Fin m → Unit ⊕ Fin m) (by
            intro a b hab
            exact Sum.inr.inj hab) i, List.count_finRange]
      rw [hcount]
      simp [x, ksScalarPoint]
    let μ := mixedCharacteristicPolynomial A
    have hrooted : μ.IsRealRooted :=
      mixedCharacteristicPolynomial_isRealRooted_of_posSemidef A hA
    have hdegree : 0 < μ.natDegree := by
      rw [show μ = mixedCharacteristicPolynomial A by rfl,
        mixedCharacteristicPolynomial_natDegree]
      exact Fintype.card_pos
    have hmonic : μ.Monic := mixedCharacteristicPolynomial_monic A
    have hbound : t + δ = (1 + s) ^ 2 := by
      dsimp only [t, δ]
      rw [← hsquare]
      ring
    change μ.maxRealRoot ≤ (1 + s) ^ 2
    rw [← hbound]
    by_contra hnot
    have hmax_gt : t + δ < μ.maxRealRoot := lt_of_not_ge hnot
    have hroot : (μ.maxRealRoot : ℂ) ∈ μ.roots :=
      Polynomial.coe_maxRealRoot_mem_roots hrooted hdegree
    have hμzero : μ.eval (μ.maxRealRoot : ℂ) = 0 :=
      Polynomial.IsRoot.def.mp ((Polynomial.mem_roots hmonic.ne_zero).mp hroot)
    let r := μ.maxRealRoot
    let z : Unit ⊕ Fin m → ℝ :=
      Sum.elim (fun _ ↦ r - δ) (fun _ ↦ δ)
    have hyz : ∀ k, y k ≤ z k := by
      intro k
      rcases k with u | i
      · cases u
        rw [hyLeft]
        dsimp only [z, Sum.elim_inl, r]
        linarith
      · rw [hyRight]
        rfl
    have hpositive := hqAbove z hyz
    have hzPoint : (fun k ↦ (z k : ℂ)) =
        Sum.elim (fun _ ↦ ((r - δ : ℝ) : ℂ)) (fun _ ↦ (δ : ℂ)) := by
      funext k
      rcases k with u | i
      · cases u
        rfl
      · rfl
    have hqShift :
        eval (Sum.elim (fun _ ↦ ((r - δ : ℝ) : ℂ)) (fun _ ↦ (δ : ℂ))) q =
          eval (Sum.elim (fun _ ↦ ((r - δ : ℝ) : ℂ) + (δ : ℂ))
            (fun _ ↦ 0)) q := by
      simpa [q, p] using ksEval_mixedDifferential_diagonal_shift A hsum indices
        ((r - δ : ℝ) : ℂ) (δ : ℂ)
    have hradd : ((r - δ : ℝ) : ℂ) + (δ : ℂ) = (r : ℂ) := by
      push_cast
      ring
    have hchar : μ.eval (r : ℂ) =
        eval (Sum.elim (fun _ ↦ (r : ℂ)) (fun _ ↦ 0)) q := by
      simpa [μ, q, p, indices] using ksEval_mixedCharacteristicPolynomial A (r : ℂ)
    have hqzero : eval (fun k ↦ (z k : ℂ)) q = 0 := by
      calc
        eval (fun k ↦ (z k : ℂ)) q =
            eval (Sum.elim (fun _ ↦ ((r - δ : ℝ) : ℂ)) (fun _ ↦ (δ : ℂ))) q :=
          congrArg (fun w ↦ eval w q) hzPoint
        _ = eval (Sum.elim (fun _ ↦ (r : ℂ)) (fun _ ↦ 0)) q := by
          simpa only [hradd] using hqShift
        _ = μ.eval (r : ℂ) := hchar.symm
        _ = 0 := by simpa only [r] using hμzero
    rw [hqzero] at hpositive
    norm_num at hpositive

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger
