/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs

import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Nagell–Ljunggren cube equation when five divides the exponent

The geometric quotient in the Nagell–Ljunggren equation cannot be a cube when the
natural-number base is at least two and the positive exponent is divisible by five.

Splitting the quotient at one fifth of the exponent reduces the problem to ruling out
cubes and five times cubes among values of the fifth cyclotomic polynomial. In the
fifth cyclotomic field, unique factorization gives a cube up to a real unit and the
possible ramified factor. Comparing absolute values at the two complex places gives
a finite bound, and checking the remaining values finishes the proof.
-/

noncomputable section

open scoped NumberField ComplexConjugate
open NumberField IsCyclotomicExtension Finset

namespace MetaMathlibExt
namespace nagell_ljunggren_cube_of_five_dvd

private abbrev K := CyclotomicField 5 ℚ
private abbrev R := 𝓞 K
private instance cyclo : IsCyclotomicExtension {5} ℚ K := by
  let : NeZero ((5 : ℕ) : ℚ) := ⟨by norm_num⟩
  exact CyclotomicField.isCyclotomicExtension _ _
private instance pid : IsPrincipalIdealRing R := Rat.five_pid K
private instance cm : IsCMField K :=
  Rat.isCMField K (S := {5}) ⟨5, by simp, by decide⟩
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

private abbrev zeta := zeta_spec 5 ℚ K
private abbrev z : R := zeta.toInteger
private abbrev conjR := IsCMField.ringOfIntegersComplexConj K
private abbrev lam : R := z - 1
private abbrev delta : R := z - conjR z

private abbrev W := InfinitePlace K
private noncomputable def emb (w : W) : R →+* ℂ :=
  w.embedding.comp (algebraMap R K)

private theorem emb_injective (w : W) : Function.Injective (emb w) :=
  w.embedding.injective.comp RingOfIntegers.coe_injective

private theorem conj_emb (w : W) (v : R) : emb w (conjR v) = conj (emb w v) :=
  IsCMField.complexEmbedding_complexConj K w.embedding v

private theorem place_card : Fintype.card W = 2 := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add, Rat.finrank 5 K] at h
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add]
  change 2 * InfinitePlace.nrComplexPlaces K = 4 at h
  omega

private theorem norm_unit (u : Rˣ) :
    ∃ w₁ w₂ : W, ‖emb w₁ u‖ * ‖emb w₂ u‖ = 1 := by
  classical
  let e := Fintype.equivFinOfCardEq place_card
  have hn : ((Algebra.norm ℤ) (u : R)).natAbs = 1 :=
    Int.isUnit_iff_natAbs_eq.mp (u.isUnit.map (Algebra.norm ℤ))
  have h := InfinitePlace.prod_eq_abs_norm (u : K)
  have hm (w : W) : w.mult = 2 := by
    exact InfinitePlace.IsComplex.mult_eq_two (IsTotallyComplex.isComplex w)
  simp only [hm] at h
  rw [← Algebra.coe_norm_int (u : R), ← Int.cast_abs, ← Int.natCast_natAbs, hn,
    Nat.cast_one] at h
  norm_num at h
  have h' := Fintype.prod_equiv e (fun w : W => w (u : K) ^ 2)
    (fun i => e.symm i (u : K) ^ 2) (fun w => by rw [Equiv.symm_apply_apply])
  rw [Fin.prod_univ_two, h] at h'
  refine ⟨e.symm 0, e.symm 1, ?_⟩
  change ‖(e.symm 0).embedding (u : K)‖ * ‖(e.symm 1).embedding (u : K)‖ = 1
  simp only [InfinitePlace.norm_embedding_eq]
  have hnon : 0 ≤ e.symm 0 (u : K) * e.symm 1 (u : K) := by positivity
  have hsq : (e.symm 0 (u : K) * e.symm 1 (u : K)) ^ 2 = 1 := by
    rw [mul_pow, ← h']
  nlinarith

-- The quotient of a unit by its conjugate has order dividing ten.
-- It is therefore a cube, so the unit can be made real modulo cubes.
private theorem unit_real_cube (u : Rˣ) :
    ∃ v b : Rˣ, conjR (v : R) = v ∧ u = v * b ^ 3 := by
  let σ := IsCMField.unitsComplexConj K
  let η := IsCMField.unitsMulComplexConjInv K u
  have hη : (η : Rˣ) = u * (σ u)⁻¹ := rfl
  have hpow : (η : Rˣ) ^ 10 = 1 := by
    have h := NumberField.Units.pow_torsionOrder_eq_one K η.prop
    rwa [Rat.torsionOrder_eq (n := 5), ite_eq_right (by decide : ¬ Even 5)] at h
  refine ⟨(u * σ u) ^ 2, (η : Rˣ) ^ 14 * u⁻¹, ?_, ?_⟩
  · change (σ ((u * σ u) ^ 2) : R) = _
    congr 1
    have hinv : σ (σ u) = u := by
      apply Units.ext
      apply RingOfIntegers.coe_injective
      exact IsCMField.complexConj_apply_apply K (u : K)
    simp [map_mul, hinv, mul_comm]
  · simp only [mul_pow, ← pow_mul]
    rw [show 14 * 3 = 2 + 10 * 4 by decide, pow_add, pow_mul, hpow, one_pow,
      mul_one, hη]
    simp only [mul_pow]
    calc
      u = (u ^ 2 * u ^ 2 * (u⁻¹) ^ 3) * (σ u ^ 2 * ((σ u)⁻¹) ^ 2) := by
        simp only [inv_pow, mul_inv_cancel, mul_one]
        group
      _ = _ := by ac_rfl

-- The two absolute values of the unit are reciprocal. The equation at the
-- smaller one bounds the larger one above in terms of the base, while
-- the equation at the larger one bounds it below.
private theorem bound_of_two_places {x r₁ r₂ c₁ c₂ d₁ d₂ t₁ t₂ : ℝ}
    (hx : 2 ≤ x)
    (hc₁ : 1 / 2 ≤ c₁) (hc₂ : 1 / 2 ≤ c₂) (hc₁' : c₁ ≤ 1)
    (hr₁ : c₁ ≤ r₁) (hr₂ : c₂ ≤ r₂)
    (hd₁ : d₁ = |4 * c₁ ^ 2 - 3 * r₁ ^ 2|)
    (hd : d₁ * d₂ = 1) (hlarge : 1 ≤ d₁)
    (ht₁ : (x - 1) / 2 ≤ t₁) (ht₂ : t₂ ≤ x + 1)
    (he₁ : r₁ ^ 3 = d₁ * t₁) (he₂ : r₂ ^ 3 = d₂ * t₂) :
    x < 300 := by
  have hdp : 0 < d₁ := by linarith
  have hdl : 0 < d₂ := by
    by_contra! h
    linarith [mul_nonpos_of_nonneg_of_nonpos hdp.le h]
  have hs : r₁ ^ 2 ≤ 2 * d₁ := by
    have hprod := mul_nonneg (show 0 ≤ c₁ + 1 by linarith) (sub_nonneg.mpr hc₁')
    have hc : c₁ ^ 2 ≤ 1 := by nlinarith only [hprod]
    nlinarith [neg_le_abs (4 * c₁ ^ 2 - 3 * r₁ ^ 2)]
  have hxl : x - 1 ≤ 4 * r₁ := by
    have h1 := mul_le_mul_of_nonneg_left ht₁ hdp.le
    rw [← he₁] at h1
    have h2 := mul_le_mul_of_nonneg_right hs (show 0 ≤ (x - 1) / 2 by linarith)
    have h3 : r₁ ^ 2 * (x - 1) ≤ r₁ ^ 2 * (4 * r₁) := by linarith only [h1, h2]
    exact le_of_mul_le_mul_left h3 (pow_pos (by linarith) _)
  have hsmall : (1 / 8 : ℝ) ≤ r₂ ^ 3 := by
    have hr : (1 / 2 : ℝ) ^ 3 ≤ r₂ ^ 3 := by gcongr; linarith
    norm_num at hr
    exact hr
  have hupper : d₁ ≤ 8 * (x + 1) := by
    have h1 := mul_le_mul_of_nonneg_left ht₂ hdl.le
    rw [← he₂] at h1
    have h2 := mul_le_mul_of_nonneg_left (hsmall.trans h1) hdp.le
    rw [← mul_assoc, hd, one_mul] at h2
    linarith
  have hx2 : (x - 1) ^ 2 ≤ 256 * (x + 1) := by
    have h1 : (x - 1) ^ 2 ≤ (4 * r₁) ^ 2 := by gcongr; linarith
    nlinarith
  by_contra! h
  nlinarith [sq_nonneg (x - 300)]


private theorem conjR_conjR (a : R) : conjR (conjR a) = a :=
  RingOfIntegers.coe_injective (IsCMField.complexConj_apply_apply K (a : K))

private theorem hpz : IsPrimitiveRoot z 5 := zeta.toInteger_isPrimitiveRoot

private theorem norm_emb_z (w : W) : ‖emb w z‖ = 1 := by
  have hp := hpz.map_of_injective (emb_injective w)
  have h := congrArg norm hp.pow_eq_one
  rw [norm_pow, norm_one] at h
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : 5 ≠ 0)).mp (by simpa using h)

private theorem conjR_z : conjR z = z ^ 4 := by
  let w : W := (Fintype.equivFinOfCardEq place_card).symm 0
  apply (emb_injective w)
  rw [conj_emb, map_pow]
  have hp := hpz.map_of_injective (emb_injective w)
  apply mul_left_cancel₀ (hp.ne_zero (by decide))
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_emb_z, one_pow, Complex.ofReal_one,
    ← pow_succ', hp.pow_eq_one]

private theorem lam_prime : Prime lam := zeta.zeta_sub_one_prime'

private theorem delta_assoc : Associated delta lam := by
  rw [show delta = (z ^ 2 - 1) * z ^ 4 by
    change z - conjR z = _
    rw [conjR_z, sub_mul, one_mul, ← pow_add, show 2 + 4 = 5 + 1 by decide, pow_add,
      hpz.pow_eq_one, one_mul, pow_one]]
  exact (associated_mul_unit_left _ _ ((hpz.isUnit (by decide)).pow 4)).trans
    (hpz.associated_sub_one_pow_sub_one_of_coprime (by decide : Nat.Coprime 2 5)).symm

private theorem conj_delta : conjR delta = -delta := by
  simp [delta, conjR_conjR]

private theorem dvd_conj_diff (a : R) : delta ∣ a - conjR a := by
  let q : R →+* R ⧸ Ideal.span {delta} := Ideal.Quotient.mk _
  suffices h : q a = q (conjR a) by
    apply (Ideal.Quotient.eq_zero_iff_dvd _ _).mp
    change q (a - conjR a) = 0
    rw [map_sub, h, sub_self]
  let f : R →+* R ⧸ Ideal.span {delta} := q.comp conjR.toRingHom
  have htop : Algebra.adjoin ℤ ({z} : Set R) = ⊤ :=
    IsCyclotomicExtension.Rat.adjoin_singleton_eq_top (K := K) zeta
  have hx : a ∈ Algebra.adjoin ℤ ({z} : Set R) := by rw [htop]; trivial
  change q a = f a
  induction hx using Algebra.adjoin_induction with
  | mem b hb =>
    obtain rfl : b = z := Set.mem_singleton_iff.mp hb
    have hd := (Ideal.Quotient.eq_zero_iff_dvd delta delta).mpr dvd_rfl
    change q (z - conjR z) = 0 at hd
    change q z = q (conjR z)
    exact sub_eq_zero.mp (by simpa only [map_sub] using hd)
  | algebraMap i =>
    simp [f]
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]

private def quartic {A : Type*} [Semiring A] (a : A) : A :=
  a ^ 4 + a ^ 3 + a ^ 2 + a + 1

private theorem quartic_sum {A : Type*} [Semiring A] (a : A) :
    (∑ i ∈ range 5, a ^ i) = quartic a := by
  simp [quartic, Finset.sum_range_succ, add_assoc, add_comm, add_left_comm]

private theorem im_emb_z (w : W) : 1 / 2 ≤ |(emb w z).im| ∧ |(emb w z).im| ≤ 1 := by
  let u := emb w z
  have hp := hpz.map_of_injective (emb_injective w)
  have hn : ‖u‖ = 1 := norm_emb_z w
  have hconj : conj u = u ^ 4 := by
    change conj (emb w z) = _
    rw [← conj_emb, conjR_z, map_pow]
  have hsum : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 = 0 := by
    have h : Polynomial.eval u (Polynomial.cyclotomic 5 ℂ) = 0 :=
      Polynomial.isRoot_cyclotomic_iff.mpr hp
    rw [Polynomial.cyclotomic_prime, Polynomial.eval_finsetSum] at h
    simpa only [Polynomial.eval_pow, Polynomial.eval_X, quartic_sum, quartic] using h
  have hquad : (u + conj u) ^ 2 + (u + conj u) - 1 = 0 := by
    rw [hconj]
    have hp5 : u ^ 5 = 1 := hp.pow_eq_one
    linear_combination (2 + u ^ 3) * hp5 + hsum
  have hre : 4 * u.re ^ 2 + 2 * u.re - 1 = 0 := by
    have hr := congrArg Complex.re hquad
    simp only [pow_two, Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.conj_re,
      Complex.add_im, Complex.conj_im, add_neg_cancel, mul_zero, sub_zero, Complex.one_re,
      Complex.zero_re] at hr
    linear_combination hr
  have hi : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h := Complex.sq_norm u
    rw [hn, one_pow, Complex.normSq_apply] at h
    linear_combination -h
  have hb : |u.re + 1 / 4| ≤ 7 / 12 := by
    rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 7 / 12), sq_abs]
    nlinarith only [hre]
  have hr : |u.re| ≤ 5 / 6 := by
    rw [abs_le] at hb ⊢
    constructor <;> linarith [hb.1, hb.2]
  refine ⟨?_, (Complex.abs_im_le_norm _).trans hn.le⟩
  have hr2 := pow_le_pow_left₀ (abs_nonneg _) hr 2
  rw [sq_abs] at hr2
  rw [← sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (abs_nonneg _), sq_abs]
  nlinarith only [hi, hr2]

private theorem emb_sub_bounds (w : W) (x : ℕ) :
    (x : ℝ) - 1 ≤ ‖emb w ((x : R) - z)‖ ∧ ‖emb w ((x : R) - z)‖ ≤ x + 1 := by
  have hx : ‖(x : ℂ)‖ = (x : ℝ) := Complex.norm_natCast _
  simp only [map_sub, map_natCast]
  constructor
  · have h := norm_sub_norm_le (x : ℂ) (emb w z)
    rwa [hx, norm_emb_z] at h
  · have h := norm_sub_le (x : ℂ) (emb w z)
    rwa [hx, norm_emb_z] at h


private theorem delta_ne : delta ≠ 0 := delta_assoc.ne_zero_iff.mpr lam_prime.ne_zero

-- Compare the equation with its conjugate. In the unramified case the
-- difference of the cube root and its conjugate is a multiple of delta by
-- a unit. In the ramified case their sum is a unit. Dividing by that unit
-- fixes one coordinate at every complex place.
private theorem normalized_cube {x : ℕ} {g : R}
    (h : ∃ (v : Rˣ) (b : R), conjR (v : R) = v ∧ (x : R) - z = g * v * b ^ 3)
    (hg : g = 1 ∨ g = delta) :
    ∃ (t : R) (q : Rˣ), g * t ^ 3 = -((x : R) - z) * q ∧
      ((g = 1 ∧ t - conjR t = delta ∧ (q : R) = t ^ 2 + t * conjR t + conjR t ^ 2) ∨
       (g = delta ∧ t + conjR t = 1 ∧ (q : R) = t ^ 2 - t * conjR t + conjR t ^ 2)) := by
  obtain ⟨v, b, hv, he⟩ := h
  have hconj := congrArg conjR he
  simp only [map_sub, map_natCast, map_mul, map_pow, hv] at hconj
  rcases hg with rfl | rfl
  · simp only [one_mul] at he
    simp only [map_one, one_mul] at hconj
    obtain ⟨a, ha⟩ := dvd_conj_diff b
    have hav : IsUnit a := by
      have heq : delta * ((v : R) * a * (b ^ 2 + b * conjR b + conjR b ^ 2)) = delta * (-1) := by
        change _ = (z - conjR z) * (-1)
        linear_combination -he + hconj - (v : R) * (b ^ 2 + b * conjR b + conjR b ^ 2) * ha
      have hunit : IsUnit ((v : R) * a * (b ^ 2 + b * conjR b + conjR b ^ 2)) :=
        (mul_left_cancel₀ delta_ne heq).symm ▸ isUnit_neg_one
      exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hunit)
    have hac : conjR a = a := by
      have h' := congrArg conjR ha
      simp only [map_sub, map_mul, conjR_conjR] at h'
      apply mul_left_cancel₀ delta_ne
      linear_combination h' + ha
    obtain ⟨t, ht⟩ := (hav.dvd : a ∣ b)
    have htc := congrArg conjR ht
    simp only [map_mul, hac] at htc
    have hdiff : t - conjR t = delta := by
      apply mul_left_cancel₀ hav.ne_zero
      linear_combination ha - ht + htc
    rw [ht, mul_pow, ← mul_assoc] at he
    rw [htc, mul_pow, ← mul_assoc] at hconj
    let q : R := t ^ 2 + t * conjR t + conjR t ^ 2
    have hq : ((v : R) * a ^ 3) * q = -1 := by
      apply mul_left_cancel₀ delta_ne
      change _ = (z - conjR z) * (-1)
      dsimp only [q]
      linear_combination -he + hconj -
        ((v : R) * a ^ 3) * (t ^ 2 + t * conjR t + conjR t ^ 2) * hdiff
    have hqu : IsUnit q := isUnit_of_mul_isUnit_right (hq.symm ▸ isUnit_neg_one)
    refine ⟨t, hqu.unit, ?_, Or.inl ⟨rfl, hdiff, hqu.unit_spec⟩⟩
    rw [hqu.unit_spec, one_mul]
    linear_combination q * he + t ^ 3 * hq
  · rw [conj_delta] at hconj
    let a := b + conjR b
    have hav : IsUnit a := by
      have heq : delta * ((v : R) * a * (b ^ 2 - b * conjR b + conjR b ^ 2)) = delta * (-1) := by
        change _ = (z - conjR z) * (-1)
        dsimp only [a]
        linear_combination -he + hconj
      have hunit : IsUnit ((v : R) * a * (b ^ 2 - b * conjR b + conjR b ^ 2)) :=
        (mul_left_cancel₀ delta_ne heq).symm ▸ isUnit_neg_one
      exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hunit)
    have hac : conjR a = a := by simp [a, conjR_conjR, add_comm]
    obtain ⟨t, ht⟩ := (hav.dvd : a ∣ b)
    have htc := congrArg conjR ht
    simp only [map_mul, hac] at htc
    have hdiff : t + conjR t = 1 := by
      apply mul_left_cancel₀ hav.ne_zero
      rw [mul_add, mul_one, ← ht, ← htc]
    have he' : (x : R) - z = delta * ((v : R) * a ^ 3) * t ^ 3 := by
      rw [he, ht]
      ring
    have hc' : (x : R) - conjR z = -delta * ((v : R) * a ^ 3) * conjR t ^ 3 := by
      rw [hconj, htc]
      ring
    let q : R := t ^ 2 - t * conjR t + conjR t ^ 2
    have hq : ((v : R) * a ^ 3) * q = -1 := by
      apply mul_left_cancel₀ delta_ne
      change _ = (z - conjR z) * (-1)
      dsimp only [q]
      linear_combination -he' + hc' - delta * ((v : R) * a ^ 3) *
        (t ^ 2 - t * conjR t + conjR t ^ 2) * hdiff
    have hqu : IsUnit q := isUnit_of_mul_isUnit_right (hq.symm ▸ isUnit_neg_one)
    refine ⟨t, hqu.unit, ?_, Or.inr ⟨rfl, hdiff, hqu.unit_spec⟩⟩
    rw [hqu.unit_spec]
    linear_combination q * he' + delta * t ^ 3 * hq


private theorem norm_cube_coefficient_im (u : ℂ) :
    ‖u ^ 2 + u * conj u + (conj u) ^ 2‖ = |4 * u.im ^ 2 - 3 * ‖u‖ ^ 2| := by
  rw [show u ^ 2 + u * conj u + (conj u) ^ 2 = ((3 * ‖u‖ ^ 2 - 4 * u.im ^ 2 : ℝ) : ℂ) by
    apply Complex.ext <;> rw [Complex.sq_norm, Complex.normSq_apply] <;>
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        pow_two, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring,
    Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]

private theorem norm_cube_coefficient_re (u : ℂ) :
    ‖u ^ 2 - u * conj u + (conj u) ^ 2‖ = |4 * u.re ^ 2 - 3 * ‖u‖ ^ 2| := by
  rw [show u ^ 2 - u * conj u + (conj u) ^ 2 = ((4 * u.re ^ 2 - 3 * ‖u‖ ^ 2 : ℝ) : ℂ) by
    apply Complex.ext <;> rw [Complex.sq_norm, Complex.normSq_apply] <;>
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, pow_two, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im] <;> ring, Complex.norm_real, Real.norm_eq_abs]

private theorem norm_emb_delta (w : W) : ‖emb w delta‖ = 2 * |(emb w z).im| := by
  change ‖emb w (z - conjR z)‖ = _
  rw [map_sub, conj_emb]
  rw [show emb w z - conj (emb w z) = (↑(2 * (emb w z).im) : ℂ) * Complex.I by
    apply Complex.ext
    · simp
    · simp
      ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, abs_mul,
    abs_of_nonneg (by norm_num)]

private theorem bound_of_normalized_cube {x : ℕ} (hx : 2 ≤ x) {g t : R} {q : Rˣ}
    (he : g * t ^ 3 = -((x : R) - z) * q)
    (hcase : (g = 1 ∧ t - conjR t = delta ∧ (q : R) = t ^ 2 + t * conjR t + conjR t ^ 2) ∨
      (g = delta ∧ t + conjR t = 1 ∧ (q : R) = t ^ 2 - t * conjR t + conjR t ^ 2)) :
    x < 300 := by
  have hx' : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hw (w : W) : ∃ c s : ℝ, 1 / 2 ≤ c ∧ c ≤ 1 ∧ c ≤ ‖emb w t‖ ∧
      ‖emb w q‖ = |4 * c ^ 2 - 3 * ‖emb w t‖ ^ 2| ∧
      ((x : ℝ) - 1) / 2 ≤ s ∧ s ≤ x + 1 ∧ ‖emb w t‖ ^ 3 = ‖emb w q‖ * s := by
    have hs := emb_sub_bounds w x
    have hn := congrArg (fun v : R => ‖emb w v‖) he
    simp only [map_mul, map_pow, map_neg, norm_mul, norm_pow, norm_neg] at hn
    rcases hcase with ⟨rfl, hd, hq⟩ | ⟨rfl, hd, hq⟩
    · have hi := congrArg (fun a : R => (emb w a).im) hd
      change (emb w (t - conjR t)).im = (emb w (z - conjR z)).im at hi
      simp only [map_sub, conj_emb, Complex.sub_im, Complex.conj_im] at hi
      have hti : (emb w t).im = (emb w z).im := by linarith
      have hq' : ‖emb w q‖ = |4 * (emb w t).im ^ 2 - 3 * ‖emb w t‖ ^ 2| := by
        rw [hq]
        simpa only [map_add, map_mul, map_pow, conj_emb] using
          norm_cube_coefficient_im (emb w t)
      rw [map_one, norm_one, one_mul, mul_comm] at hn
      refine ⟨|(emb w z).im|, ‖emb w ((x : R) - z)‖, (im_emb_z w).1, (im_emb_z w).2,
        ?_, ?_, by linarith [hs.1], hs.2, hn⟩
      · rw [← hti]
        exact Complex.abs_im_le_norm _
      · rw [← hti, sq_abs]
        exact hq'
    · have hr := congrArg (fun a : R => (emb w a).re) hd
      simp only [map_add, map_one, conj_emb, Complex.add_re, Complex.conj_re, Complex.one_re] at hr
      have htr : (emb w t).re = 1 / 2 := by linarith
      have hq' : ‖emb w q‖ = |4 * (emb w t).re ^ 2 - 3 * ‖emb w t‖ ^ 2| := by
        rw [hq]
        simpa only [map_add, map_sub, map_mul, map_pow, conj_emb] using
          norm_cube_coefficient_re (emb w t)
      have hd₁ : 1 ≤ ‖emb w delta‖ := by rw [norm_emb_delta]; linarith [(im_emb_z w).1]
      have hd₂ : ‖emb w delta‖ ≤ 2 := by rw [norm_emb_delta]; linarith [(im_emb_z w).2]
      have hdp : 0 < ‖emb w delta‖ := by linarith
      refine ⟨1 / 2, ‖emb w ((x : R) - z)‖ / ‖emb w delta‖, le_rfl, by norm_num, ?_,
        htr ▸ hq', ?_, ?_, ?_⟩
      · simpa [htr] using Complex.abs_re_le_norm (emb w t)
      · rw [le_div_iff₀ hdp]
        exact (mul_le_mul_of_nonneg_left hd₂ (by linarith)).trans (by linarith [hs.1])
      · rw [div_le_iff₀ hdp]
        exact hs.2.trans (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hd₁ (show 0 ≤ (x : ℝ) + 1 by positivity))
      · rw [mul_div_assoc', eq_div_iff hdp.ne', mul_comm _ ‖emb w delta‖,
          mul_comm ‖emb w q‖]
        exact hn
  have finish (w₁ w₂ : W) (hd : ‖emb w₁ q‖ * ‖emb w₂ q‖ = 1) (hl : 1 ≤ ‖emb w₁ q‖) :
      (x : ℝ) < 300 := by
    obtain ⟨c₁, s₁, hc₁, hc₁', hr₁, hd₁, ht₁, -, he₁⟩ := hw w₁
    obtain ⟨c₂, s₂, hc₂, -, hr₂, -, -, ht₂, he₂⟩ := hw w₂
    exact bound_of_two_places hx' hc₁ hc₂ hc₁' hr₁ hr₂ hd₁ hd hl ht₁ ht₂ he₁ he₂
  obtain ⟨w₁, w₂, hd⟩ := norm_unit q
  suffices hh : (x : ℝ) < 300 by exact_mod_cast hh
  by_cases hl : 1 ≤ ‖emb w₁ q‖
  · exact finish w₁ w₂ hd hl
  · apply finish w₂ w₁ ((mul_comm _ _).trans hd)
    by_contra! hs
    have h' := mul_le_mul_of_nonneg_left hs.le (norm_nonneg (emb w₁ q))
    exact hl (by simpa only [hd, mul_one] using h')


private theorem quartic_prod (a : R) :
    (∏ i ∈ primitiveRoots 5 R, (a - i)) = quartic a := by
  have h := congrArg (Polynomial.eval a) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hpz)
  calc
    _ = Polynomial.eval a (Polynomial.cyclotomic 5 R) := by
      simpa only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C] using h.symm
    _ = _ := by
      rw [Polynomial.cyclotomic_prime, Polynomial.eval_finsetSum]
      simpa only [Polynomial.eval_pow, Polynomial.eval_X] using quartic_sum a

private theorem prime_root_diff {i : R} (hi : i ∈ primitiveRoots 5 R) (hne : i ≠ z) :
    Associated (z - i) lam := by
  have hip := isPrimitiveRoot_of_mem_primitiveRoots hi
  obtain ⟨k, hk, he⟩ := hpz.eq_pow_of_pow_eq_one hip.pow_eq_one
  have hk₀ : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at he
    exact hip.ne_one (by decide) he.symm
  have hk₁ : k ≠ 1 := by
    rintro rfl
    rw [pow_one] at he
    exact hne he.symm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk₀
  have hj : j ≤ 3 := by omega
  have hj₁ : 1 ≤ j := by omega
  have hcop : Nat.Coprime j 5 := by interval_cases j <;> decide
  have hunit := hpz.isUnit (by decide)
  rw [← he, pow_succ, ← one_sub_mul]
  apply (associated_mul_unit_left _ _ hunit).trans
  simpa only [neg_sub] using
    (hpz.associated_sub_one_pow_sub_one_of_coprime hcop).symm.neg_left

-- Once the possible ramified factor has been removed, the factor indexed
-- by z is coprime to the other three.
private theorem split_cube {x y c : ℕ} (he : quartic x = c * y ^ 3) {g : R}
    (hg : g ≠ 0) (hpow : Associated (g ^ 4) (c : R))
    (hdiv : ∀ i ∈ primitiveRoots 5 R, g ∣ (x : R) - i)
    (hndiv : ¬g * lam ∣ (x : R) - z) :
    ∃ (v : Rˣ) (b : R), conjR (v : R) = v ∧ (x : R) - z = g * v * b ^ 3 := by
  classical
  let s := primitiveRoots 5 R
  have hz : z ∈ s := (mem_primitiveRoots (by decide)).mpr hpz
  let f (i : R) := if h : i ∈ s then (hdiv i h).choose else 0
  have hf (i : R) (hi : i ∈ s) : (x : R) - i = g * f i := by
    simp only [f, dite_eq_left hi]
    exact (hdiv i hi).choose_spec
  have hprod : g ^ 4 * (∏ i ∈ s, f i) = (c : R) * (y : R) ^ 3 := by
    calc
      g ^ 4 * (∏ i ∈ s, f i) = ∏ i ∈ s, g * f i := by
        rw [prod_mul_distrib, prod_const, hpz.card_primitiveRoots]
        rfl
      _ = quartic (x : R) := by
        rw [← quartic_prod]
        exact prod_congr rfl (fun i hi => (hf i hi).symm)
      _ = (c : R) * (y : R) ^ 3 := by
        have hh := congrArg (fun n : ℕ => (n : R)) he
        simpa only [quartic, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one] using hh
  have ha : Associated ((y : R) ^ 3) (∏ i ∈ s, f i) := by
    apply Associated.of_mul_left (a := g ^ 4) (c := g ^ 4) _ (Associated.refl _)
      (pow_ne_zero _ hg)
    rw [hprod]
    exact hpow.mul_right _
  have hn : ¬lam ∣ f z := by
    rintro ⟨b, hb⟩
    exact hndiv ⟨b, by rw [hf z hz, hb, mul_assoc]⟩
  have hcp : IsCoprime (f z) (∏ i ∈ s.erase z, f i) := by
    refine IsCoprime.prod_right (fun i hi => ?_)
    have hne := (mem_erase.mp hi).1
    have his := (mem_erase.mp hi).2
    have hcz := (lam_prime.coprime_iff_not_dvd.mpr hn).symm.of_isCoprime_of_dvd_right
      (prime_root_diff his hne).dvd
    apply isCoprime_of_prime_dvd (fun h => hn (by rw [h.1]; exact dvd_zero _))
    intro p hp hpa hpi
    have hpi' := hpi.trans (show f i ∣ (x : R) - i by rw [hf i his]; exact dvd_mul_left _ _)
    have hpz' := hpa.trans (show f z ∣ (x : R) - z by rw [hf z hz]; exact dvd_mul_left _ _)
    have hdiff : p ∣ z - i := by
      convert dvd_sub hpi' hpz' using 1
      ring
    exact hp.not_isUnit (hcz.isUnit_of_dvd' hpa hdiff)
  rw [← prod_erase_mul _ _ hz, mul_comm] at ha
  obtain ⟨b, u, hu⟩ := exists_associated_pow_of_associated_pow_mul hcp ha
  obtain ⟨v, a, hv, hunit⟩ := unit_real_cube u
  refine ⟨v, (a : R) * b, hv, ?_⟩
  rw [hf z hz, ← hu, hunit, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

-- The decision procedure evaluates the two candidate integer cube roots
-- for each base in the range.
private theorem no_small_quartic_cube {x y c : ℕ} (hx : 2 ≤ x) (hb : x < 300)
    (hc : c = 1 ∨ c = 5) (he : quartic x = c * y ^ 3) : False := by
  have hcheck : ∀ a : Fin 300, 2 ≤ a.val →
      (Nat.nthRoot 3 (quartic a.val)) ^ 3 ≠ quartic a.val ∧
      5 * (Nat.nthRoot 3 (quartic a.val / 5)) ^ 3 ≠ quartic a.val := by decide +kernel
  have hh := hcheck ⟨x, hb⟩ hx
  change (Nat.nthRoot 3 (quartic x)) ^ 3 ≠ quartic x ∧
    5 * (Nat.nthRoot 3 (quartic x / 5)) ^ 3 ≠ quartic x at hh
  rcases hc with rfl | rfl
  · rw [one_mul] at he
    exact hh.1 (by rw [he, Nat.nthRoot_pow (by decide : 3 ≠ 0)])
  · have hd : quartic x / 5 = y ^ 3 := by rw [he, Nat.mul_div_cancel_left _ (by decide)]
    exact hh.2 (by rw [hd, Nat.nthRoot_pow (by decide : 3 ≠ 0), he])

private theorem five_dvd_quartic (x : ℕ) : 5 ∣ quartic x ↔ (5 : ℤ) ∣ (x : ℤ) - 1 := by
  change 5 ∣ quartic x ↔ ((5 : ℕ) : ℤ) ∣ (x : ℤ) - 1
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [quartic, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Int.cast_sub, Int.cast_natCast,
    Int.cast_one]
  exact (by decide : ∀ a : ZMod 5, quartic a = 0 ↔ a - 1 = 0) (x : ZMod 5)

private theorem not_square_five_dvd_quartic (x : ℕ) : ¬25 ∣ quartic x := by
  rw [← ZMod.natCast_eq_zero_iff]
  simpa only [quartic, Nat.cast_add, Nat.cast_pow, Nat.cast_one] using
    (by decide : ∀ a : ZMod 25, quartic a ≠ 0) (x : ZMod 25)

private theorem lam_dvd_sub_root (x : ℕ) {i : R} (hi : i ∈ primitiveRoots 5 R) :
    lam ∣ (x : R) - i ↔ (5 : ℤ) ∣ (x : ℤ) - 1 := by
  have hi' := (isPrimitiveRoot_of_mem_primitiveRoots hi).map_of_injective
    RingOfIntegers.coe_injective
  have hassoc : Associated lam (i - 1) :=
    Rat.associated_sub_one_of_isPrimitiveRoot 5 zeta hi'
  have hdiff : lam ∣ ((x : R) - i) - ((x : R) - 1) := by
    convert dvd_neg.mpr hassoc.dvd using 1
    ring
  rw [dvd_iff_dvd_of_dvd_sub hdiff]
  have hh := Rat.zeta_sub_one_dvd_intCast_iff' 5 zeta (n := (x : ℤ) - 1)
  simpa using hh

private theorem no_quartic_cube {x y c : ℕ} (hx : 2 ≤ x)
    (hc : c = 1 ∨ c = 5) (he : quartic x = c * y ^ 3) : False := by
  have hz : z ∈ primitiveRoots 5 R := (mem_primitiveRoots (by decide)).mpr hpz
  have hfive : Associated (lam ^ 4) (5 : R) := Rat.associated_zeta_sub_one_pow_prime 5 zeta
  have bound : x < 300 := by
    rcases hc with rfl | rfl
    · have hndiv : ¬lam ∣ (x : R) - z := by
        intro hd
        have h₅ := (five_dvd_quartic x).mpr ((lam_dvd_sub_root x hz).mp hd)
        rw [he, one_mul] at h₅
        have hy := Nat.prime_five.dvd_of_dvd_pow h₅
        apply not_square_five_dvd_quartic x
        rw [he, one_mul]
        exact dvd_trans (by decide : 25 ∣ 5 ^ 3) (pow_dvd_pow_of_dvd hy 3)
      obtain ⟨t, q, hq, hcase⟩ := normalized_cube
        (split_cube he one_ne_zero (by simp) (fun _ _ => one_dvd _) (by simpa using hndiv))
        (Or.inl rfl)
      exact bound_of_normalized_cube hx hq hcase
    · have hdiv : (5 : ℤ) ∣ (x : ℤ) - 1 :=
        (five_dvd_quartic x).mp (he ▸ dvd_mul_right _ _)
      have hh (i : R) (hi : i ∈ primitiveRoots 5 R) : delta ∣ (x : R) - i :=
        delta_assoc.dvd.trans ((lam_dvd_sub_root x hi).mpr hdiv)
      have hpow : Associated (delta ^ 4) (5 : R) := delta_assoc.pow_pow.trans hfive
      have hndiv : ¬delta * lam ∣ (x : R) - z := by
        intro hd
        have hl : lam ^ 2 ∣ (x : R) - z :=
          (pow_two lam ▸ ((delta_assoc.mul_right lam).dvd_iff_dvd_left).mp hd)
        have hf : (5 : R) ∣ (x : R) - 1 := by
          obtain ⟨j, hj⟩ := hdiv
          refine ⟨(j : R), ?_⟩
          simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_one, Int.cast_mul, Int.cast_ofNat]
            using congrArg (fun i : ℤ => (i : R)) hj
        have hl' : lam ^ 2 ∣ (x : R) - 1 :=
          (pow_dvd_pow _ (by decide : 2 ≤ 4)).trans (hfive.dvd.trans hf)
        have hll : lam ^ 2 ∣ lam := by
          change lam ^ 2 ∣ z - 1
          convert dvd_sub hl' hl using 1
          ring
        obtain ⟨j, hj⟩ := hll
        apply lam_prime.not_isUnit
        apply isUnit_of_dvd_one
        refine ⟨j, mul_left_cancel₀ lam_prime.ne_zero ?_⟩
        simpa only [mul_one, ← mul_assoc, ← pow_two] using hj
      obtain ⟨t, q, hq, hcase⟩ :=
        normalized_cube (split_cube he delta_ne hpow hh hndiv) (Or.inr rfl)
      exact bound_of_normalized_cube hx hq hcase
  exact no_small_quartic_cube hx bound hc he

private theorem coprime_of_gcd_dvd_five {a b : ℕ} (h : Nat.gcd b a ∣ 5)
    (hn : ¬5 ∣ b) : Nat.Coprime b a := by
  rcases (Nat.dvd_prime Nat.prime_five).mp h with he | he
  · exact he
  · exact False.elim (hn (he ▸ Nat.gcd_dvd_left b a))

private theorem quartic_of_geom_cube {x y k : ℕ} (hx : 2 ≤ x)
    (he : (x ^ (5 * k) - 1) / (x - 1) = y ^ 3) :
    ∃ c b : ℕ, (c = 1 ∨ c = 5) ∧ quartic (x ^ k) = c * b ^ 3 := by
  let X := x ^ k
  let a := ∑ i ∈ range k, x ^ i
  let Q := quartic X
  have hxp : 1 ≤ x := by omega
  have hXp : 1 ≤ X := one_le_pow₀ hxp
  have ha : a * (x - 1) = X - 1 := geom_sum_mul_of_one_le hxp k
  have hQ : Q * (X - 1) = X ^ 5 - 1 := by
    rw [show Q = ∑ i ∈ range 5, X ^ i from (quartic_sum X).symm]
    exact geom_sum_mul_of_one_le hXp 5
  have hfact : Q * a = y ^ 3 := by
    rw [mul_comm 5 k, pow_mul] at he
    change (X ^ 5 - 1) / (x - 1) = y ^ 3 at he
    rwa [← hQ, ← ha, ← mul_assoc, Nat.mul_div_cancel _ (by omega : 0 < x - 1)] at he
  have hgcd : Nat.gcd Q a ∣ 5 := by
    let d := Nat.gcd Q a
    have ha' : (a : ZMod d) = 0 :=
      (ZMod.natCast_eq_zero_iff a d).mpr (Nat.gcd_dvd_right _ _)
    have hQ' : (Q : ZMod d) = 0 :=
      (ZMod.natCast_eq_zero_iff Q d).mpr (Nat.gcd_dvd_left _ _)
    have hX : X = a * (x - 1) + 1 := by omega
    have hX' : (X : ZMod d) = 1 := by
      rw [hX, Nat.cast_add, Nat.cast_mul, ha', zero_mul, zero_add, Nat.cast_one]
    change ((quartic X : ℕ) : ZMod d) = 0 at hQ'
    simp only [quartic, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hX', one_pow] at hQ'
    exact (ZMod.natCast_eq_zero_iff 5 d).mp (by
      convert hQ' using 1
      norm_num)
  have extract {q a : ℕ} (hcp : Nat.Coprime q a) (h : q * a = y ^ 3) :
      ∃ b : ℕ, q = b ^ 3 :=
    exists_eq_pow_of_mul_eq_pow (by rw [gcd_eq_nat_gcd, hcp.gcd_eq_one]; exact isUnit_one) h
  by_cases h₅ : 5 ∣ Q
  · obtain ⟨q, hq⟩ := h₅
    have hn : ¬5 ∣ q := by
      rintro ⟨v, hv⟩
      exact not_square_five_dvd_quartic X ⟨v, by change Q = _; rw [hq, hv]; ring⟩
    have hgc : Nat.gcd q a ∣ 5 :=
      (Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans ⟨5, by rw [hq, mul_comm]⟩)
        (Nat.gcd_dvd_right _ _)).trans hgcd
    have hcp := (coprime_of_gcd_dvd_five hgc hn).mul_right
      (Nat.prime_five.coprime_iff_not_dvd.mpr hn).symm
    obtain ⟨b, hb⟩ := extract hcp (by rw [← hfact, hq]; ring)
    exact ⟨5, b, Or.inr rfl, hq.trans (by rw [hb])⟩
  · obtain ⟨b, hb⟩ := extract (coprime_of_gcd_dvd_five hgcd h₅) hfact
    exact ⟨1, b, Or.inl rfl, by simpa only [one_mul] using hb⟩

end nagell_ljunggren_cube_of_five_dvd

set_option linter.unusedVariables false in
/-- **The Nagell–Ljunggren cube equation when $5 \mid n$.** There are no natural numbers
$x \ge 2$, $y \ge 2$ and $n \ge 3$ with $5 \mid n$ such that $(x^n - 1)/(x - 1) = y^3$.

Source: Tran Duc Son, *On the Nagell--Ljunggren Equation \frac{x^{5}-1}{x-1}=y^{3}*,
INTEGERS 26 (2026), Article A44, Corollary 1 (`integers-2026-A44-cor-1`). -/
public theorem nagell_ljunggren_cube_of_five_dvd (x y n : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hn : 3 ≤ n) (h5 : 5 ∣ n) : (x ^ n - 1) / (x - 1) ≠ y ^ 3 := by
  open nagell_ljunggren_cube_of_five_dvd in
  intro he
  obtain ⟨k, rfl⟩ := h5
  have hk : 0 < k := by omega
  have hxk : 2 ≤ x ^ k := hx.trans (Nat.le_pow hk)
  obtain ⟨c, b, hc, hb⟩ := quartic_of_geom_cube hx he
  exact no_quartic_cube hxk hc hb

end MetaMathlibExt
