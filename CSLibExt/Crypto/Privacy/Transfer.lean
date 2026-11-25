/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Crypto.Privacy.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Moments.Basic

/-!
# Transfer theorem for adaptive data analysis

Pure differential privacy gives a two-sided generalization bound for a jointly measurable
family of queries with values in `[0, 1]`. The proof bounds the exponential moment of the
centered sample sum by integrating out one sample row at a time. The lower tail follows
by applying the upper-tail bound to the complementary query.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Cslib.Crypto.Privacy

namespace differentiallyPrivate_transfer

variable {𝒳 Q : Type*} [MeasurableSpace 𝒳] [MeasurableSpace Q]

private theorem integrable_bounded {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

private theorem integral_mem_Icc {P : Measure 𝒳} [IsProbabilityMeasure P] {f : 𝒳 → ℝ}
    (hf : Measurable f) (h : ∀ x, f x ∈ Icc (0 : ℝ) 1) : (∫ x, f x ∂P) ∈ Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg fun x ↦ (h x).1, ?_⟩
  have hi := integrable_bounded (μ := P) hf fun x ↦ by
    rw [abs_of_nonneg (h x).1]
    exact (h x).2
  simpa using integral_mono hi (integrable_const (1 : ℝ)) fun x ↦ (h x).2

private theorem integral_one_sub {P : Measure 𝒳} [IsProbabilityMeasure P] {f : 𝒳 → ℝ}
    (hf : Integrable f P) : (∫ z, 1 - f z ∂P) = 1 - ∫ z, f z ∂P := by
  simpa [integral_const, measureReal_def] using
    (integral_sub (f := fun _ : 𝒳 ↦ (1 : ℝ)) (integrable_const _) hf)

private theorem exp_le_quadratic {x : ℝ} (hx : |x| ≤ 1 / 3) :
    Real.exp x ≤ 1 + x + (3 / 4) * x ^ 2 := by
  have h := (abs_le.mp (Real.exp_bound (hx.trans (by norm_num)) (n := 3) (by decide))).2
  norm_num [Finset.sum_range_succ] at h
  have hc := mul_le_mul_of_nonneg_right hx (sq_nonneg |x|)
  rw [sq_abs] at *
  have he : |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ', sq_abs]
  rw [he] at h
  nlinarith [sq_nonneg x]

/-- The joint law dominates a multiple of the product of its marginals when the output
laws for every pair of possible values of one row satisfy the privacy bound. -/
private theorem indep_le_joint {P : Measure 𝒳} [IsProbabilityMeasure P]
    (B : Kernel 𝒳 Q) [IsMarkovKernel B] {ε : ℝ}
    (hB : ∀ x y, B y ≤ ENNReal.ofReal (Real.exp ε) • B x) :
    ENNReal.ofReal (Real.exp (-ε)) • P.prod (B ∘ₘ P) ≤ P ⊗ₘ B := by
  refine Measure.le_iff.mpr fun s hs ↦ ?_
  rw [← Measure.compProd_const, smul_apply, Measure.compProd_apply hs,
    Measure.compProd_apply hs, smul_eq_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x ↦ ?_
  simp only [Kernel.const_apply]
  have ht : MeasurableSet (Prod.mk x ⁻¹' s) := measurable_prodMk_left hs
  have hle : (B ∘ₘ P) (Prod.mk x ⁻¹' s) ≤
      ENNReal.ofReal (Real.exp ε) * B x (Prod.mk x ⁻¹' s) := by
    rw [Measure.bind_apply ht B.aemeasurable]
    simpa only [lintegral_const, measure_univ, mul_one, smul_apply, smul_eq_mul] using
      lintegral_mono (μ := P) (fun y ↦ (Measure.le_iff.mp (hB x y)) _ ht)
  apply (mul_le_mul_right hle _).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]

private theorem row_moment_le {P : Measure 𝒳} [IsProbabilityMeasure P]
    (B : Kernel 𝒳 Q) [IsMarkovKernel B] {φ : Q → 𝒳 → ℝ}
    (hφ : Measurable (Function.uncurry φ)) (hφ01 : ∀ q z, φ q z ∈ Icc (0 : ℝ) 1)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht' : t ≤ 1 / 3)
    (hB : ∀ x y, B y ≤ ENNReal.ofReal (Real.exp ε) • B x)
    {g : Q → ℝ} (hg : Measurable g) (hg₀ : ∀ q, 0 ≤ g q) {C : ℝ} (hgC : ∀ q, g q ≤ C) :
    let m q := ∫ z, φ q z ∂P
    (∫ p, g p.2 * Real.exp (t * (φ p.2 p.1 - m p.2)) ∂(P ⊗ₘ B)) ≤
      Real.exp (t * ε + (3 / 4) * t ^ 2) * ∫ p, g p.2 ∂(P ⊗ₘ B) := by
  classical
  let m q := ∫ z, φ q z ∂P
  let μ := P ⊗ₘ B
  let ν := B ∘ₘ P
  let f (p : 𝒳 × Q) := φ p.2 p.1
  let G (p : 𝒳 × Q) := g p.2
  let D (p : 𝒳 × Q) := f p - m p.2
  let L (q : Q) := g q * (1 - m q)
  let H (p : 𝒳 × Q) := G p * (1 - f p)
  change (∫ p, G p * Real.exp (t * D p) ∂μ) ≤
    Real.exp (t * ε + (3 / 4) * t ^ 2) * ∫ p, G p ∂μ
  have hφq q : Measurable (φ q) := hφ.comp (measurable_prodMk_left (x := q))
  have hm : Measurable m := hφ.stronglyMeasurable.integral_prod_right'.measurable
  have hm01 q : m q ∈ Icc (0 : ℝ) 1 := integral_mem_Icc (hφq q) (hφ01 q)
  have hfm : Measurable f := hφ.comp measurable_swap
  have hf01 p : f p ∈ Icc (0 : ℝ) 1 := hφ01 _ _
  have hGm : Measurable G := hg.comp measurable_snd
  have hDm : Measurable D := hfm.sub (hm.comp measurable_snd)
  have hLm : Measurable L := hg.mul (measurable_const.sub hm)
  have hHm : Measurable H := hGm.mul (measurable_const.sub hfm)
  have hG₀ p : 0 ≤ G p := hg₀ _
  have hD p : |D p| ≤ 1 := abs_le.mpr ⟨by linarith [(hf01 p).1, (hm01 p.2).2],
    by linarith [(hf01 p).2, (hm01 p.2).1]⟩
  have hH₀ p : 0 ≤ H p := mul_nonneg (hG₀ p) (sub_nonneg.mpr (hf01 p).2)
  have hH p : |H p| ≤ C := by
    rw [abs_of_nonneg (hH₀ p)]
    exact (mul_le_of_le_one_right (hG₀ p) (by linarith [(hf01 p).1])).trans (hgC _)
  have hL₀ q : 0 ≤ L q := mul_nonneg (hg₀ q) (sub_nonneg.mpr (hm01 q).2)
  have hLG q : L q ≤ g q := mul_le_of_le_one_right (hg₀ q) (by linarith [(hm01 q).1])
  have iG : Integrable G μ :=
    integrable_bounded hGm fun p ↦ (abs_of_nonneg (hG₀ p)).le.trans (hgC _)
  have iD : Integrable (fun p ↦ G p * D p) μ := integrable_bounded (hGm.mul hDm) fun p ↦ by
    rw [abs_mul, abs_of_nonneg (hG₀ p)]
    exact (mul_le_of_le_one_right (hG₀ p) (hD p)).trans (hgC _)
  have iL : Integrable (fun p : 𝒳 × Q ↦ L p.2) μ :=
    integrable_bounded (hLm.comp measurable_snd) fun p ↦ by
      rw [abs_of_nonneg (hL₀ p.2)]
      exact (hLG p.2).trans (hgC _)
  have iH : Integrable H μ := integrable_bounded hHm hH
  have hi : Integrable (fun p ↦ G p * Real.exp (t * D p)) μ :=
    integrable_bounded (hGm.mul ((measurable_const.mul hDm).exp)) fun p ↦ by
      rw [abs_of_nonneg (mul_nonneg (hG₀ p) (Real.exp_pos _).le)]
      exact mul_le_mul (hgC _) (Real.exp_le_exp.mpr
        (mul_le_of_le_one_right ht (le_of_abs_le (hD p)))) (Real.exp_pos _).le
        ((hG₀ p).trans (hgC _))
  -- Under independent resampling, the mean of the complementary score is `1 - m q`.
  have hindep : (∫ p, H p ∂(P.prod ν)) = ∫ p : 𝒳 × Q, L p.2 ∂μ := by
    rw [integral_prod_symm _ (integrable_bounded hHm hH)]
    have hmarg : μ.map Prod.snd = ν := Measure.snd_compProd P B
    rw [← integral_map_of_stronglyMeasurable measurable_snd hLm.stronglyMeasurable, hmarg]
    apply integral_congr_ae
    filter_upwards with q
    have hφi : Integrable (φ q) P := integrable_bounded (hφq q) fun x ↦ by
      rw [abs_of_nonneg (hφ01 q x).1]
      exact (hφ01 q x).2
    change (∫ x, g q * (1 - φ q x) ∂P) = L q
    rw [integral_const_mul, integral_one_sub hφi]
  have hcomp := integral_mono_measure (indep_le_joint B hB)
    (Filter.Eventually.of_forall hH₀) iH
  rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul,
    hindep] at hcomp
  have hdiff : (∫ p, G p * D p ∂μ) = (∫ p : 𝒳 × Q, L p.2 ∂μ) - ∫ p, H p ∂μ := by
    rw [← integral_sub iL iH]
    apply integral_congr_ae
    filter_upwards with p
    dsimp [D, L, H, G]
    ring
  -- Privacy bounds the increase in the centered score after weighting by the output.
  have hshift : (∫ p, G p * D p ∂μ) ≤ ε * ∫ p, G p ∂μ := by
    rw [hdiff]
    calc
      _ ≤ (1 - Real.exp (-ε)) * ∫ p : 𝒳 × Q, L p.2 ∂μ := by linarith
      _ ≤ ε * ∫ p, G p ∂μ := by
        refine mul_le_mul ?_ (integral_mono iL iG fun p ↦ hLG p.2)
          (integral_nonneg fun p ↦ hL₀ p.2) hε
        linarith [Real.add_one_le_exp (-ε)]
  have hpoint p : Real.exp (t * D p) ≤ 1 + t * D p + (3 / 4) * t ^ 2 := by
    have ha : |t * D p| ≤ t := by
      rw [abs_mul, abs_of_nonneg ht]
      exact mul_le_of_le_one_right ht (hD p)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) ha 2
    rw [sq_abs] at hsq
    linarith [exp_le_quadratic (ha.trans ht')]
  calc
    _ ≤ ∫ p, ((1 + (3 / 4) * t ^ 2) * G p + t * (G p * D p)) ∂μ := by
      refine integral_mono hi ((iG.const_mul _).add (iD.const_mul _)) fun p ↦ ?_
      calc
        _ ≤ G p * (1 + t * D p + (3 / 4) * t ^ 2) :=
          mul_le_mul_of_nonneg_left (hpoint p) (hG₀ p)
        _ = _ := by ring
    _ = (1 + (3 / 4) * t ^ 2) * (∫ p, G p ∂μ) + t * ∫ p, G p * D p ∂μ := by
      rw [integral_add (iG.const_mul _) (iD.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ (1 + (t * ε + (3 / 4) * t ^ 2)) * ∫ p, G p ∂μ := by
      have := mul_le_mul_of_nonneg_left hshift ht
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by simpa only [add_comm] using Real.add_one_le_exp (t * ε + (3 / 4) * t ^ 2))
      (integral_nonneg hG₀)

/-- Separate one row from the other rows in the expectation over the data and the mechanism. -/
private theorem integral_split_row {P : Measure 𝒳} [IsProbabilityMeasure P] {n : ℕ}
    (A : Kernel (Fin (n + 1) → 𝒳) Q) [IsMarkovKernel A] (i : Fin (n + 1))
    {F : (Fin (n + 1) → 𝒳) × Q → ℝ} (hF : Measurable F) {C : ℝ}
    (hFC : ∀ p, |F p| ≤ C) :
    let J R := ∫ x, ∫ q, F (i.insertNth x R, q) ∂(A (i.insertNth x R)) ∂P
    let ν := Measure.pi fun _ : Fin n ↦ P
    (∫ p, F p ∂((Measure.pi fun _ : Fin (n + 1) ↦ P) ⊗ₘ A)) = (∫ R, J R ∂ν) ∧
      Integrable J ν := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ 𝒳) i
  let J (S : Fin (n + 1) → 𝒳) := ∫ q, F (S, q) ∂(A S)
  have hJ : Measurable J := hF.stronglyMeasurable.integral_kernel_prod_right'.measurable
  let ν := Measure.pi fun _ : Fin n ↦ P
  have hJint : Integrable (J ∘ e.symm) (P.prod ν) :=
    integrable_bounded (hJ.comp e.symm.measurable) fun p ↦ by
      simpa [Function.comp_apply, J, Real.norm_eq_abs, measureReal_def]
        using norm_integral_le_of_norm_le_const (μ := A (e.symm p))
          (f := fun q ↦ F (e.symm p, q)) (C := C)
          (Filter.Eventually.of_forall fun q ↦ by rw [Real.norm_eq_abs]; exact hFC (e.symm p, q))
  refine ⟨?_, hJint.integral_prod_right⟩
  rw [Measure.integral_compProd (integrable_bounded hF hFC)]
  change (∫ S, J S ∂(Measure.pi fun _ : Fin (n + 1) ↦ P)) = _
  have he : MeasurePreserving e.symm (P.prod ν) (Measure.pi fun _ : Fin (n + 1) ↦ P) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ P) i).symm e
  rw [← he.integral_comp' J]
  exact integral_prod_symm _ hJint

private theorem exponential_sum_bound {P : Measure 𝒳} [IsProbabilityMeasure P] {n : ℕ}
    (A : Kernel (Fin (n + 1) → 𝒳) Q) [IsMarkovKernel A] {φ : Q → 𝒳 → ℝ}
    (hφ : Measurable (Function.uncurry φ)) (hφ01 : ∀ q z, φ q z ∈ Icc (0 : ℝ) 1)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht' : t ≤ 1 / 3)
    (hA : DifferentiallyPrivate hammingAdj (fun S ↦ A S) ε 0) (s : Finset (Fin (n + 1))) :
    let F (p : (Fin (n + 1) → 𝒳) × Q) :=
      Real.exp (t * ∑ i ∈ s, (φ p.2 (p.1 i) - ∫ z, φ p.2 z ∂P))
    let μ := (Measure.pi fun _ : Fin (n + 1) ↦ P) ⊗ₘ A
    Integrable F μ ∧ (∫ p, F p ∂μ) ≤ Real.exp ((s.card : ℝ) * (t * ε + (3 / 4) * t ^ 2)) := by
  classical
  let μ := (Measure.pi fun _ : Fin (n + 1) ↦ P) ⊗ₘ A
  let m q := ∫ z, φ q z ∂P
  let D (i : Fin (n + 1)) (p : (Fin (n + 1) → 𝒳) × Q) := φ p.2 (p.1 i) - m p.2
  let F (s : Finset (Fin (n + 1))) (p : (Fin (n + 1) → 𝒳) × Q) :=
    Real.exp (t * ∑ i ∈ s, D i p)
  let c := t * ε + (3 / 4) * t ^ 2
  have hm : Measurable m := hφ.stronglyMeasurable.integral_prod_right'.measurable
  have hm01 q : m q ∈ Icc (0 : ℝ) 1 :=
    integral_mem_Icc (hφ.comp (measurable_prodMk_left (x := q))) (hφ01 q)
  have hDm i : Measurable (D i) :=
    (hφ.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))).sub
      (hm.comp measurable_snd)
  have hFm s : Measurable (F s) :=
    (measurable_const.mul (Finset.measurable_sum s fun i _ ↦ hDm i)).exp
  have hFpos s p : 0 < F s p := Real.exp_pos _
  have hFC s p : |F s p| ≤ Real.exp (t * s.card) := by
    rw [abs_of_pos (hFpos s p)]
    apply Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ ht)
    calc
      _ ≤ ∑ _i ∈ s, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        dsimp [D]
        linarith [(hφ01 p.2 (p.1 i)).2, (hm01 p.2).1]
      _ = _ := by simp
  refine ⟨integrable_bounded (hFm s) (hFC s), ?_⟩
  change (∫ p, F s p ∂μ) ≤ Real.exp ((s.card : ℝ) * c)
  induction s using Finset.induction_on with
  | empty => simp [F]
  | insert i s his ih =>
    suffices hstep : (∫ p, F (insert i s) p ∂μ) ≤ Real.exp c * ∫ p, F s p ∂μ by
      apply hstep.trans
      rw [Finset.card_insert_of_notMem his, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        Real.exp_add ((s.card : ℝ) * c) c, mul_comm (Real.exp ((s.card : ℝ) * c))]
      exact mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
    obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P
    have hnew := integral_split_row (P := P) A i (hFm (insert i s)) (hFC (insert i s))
    have hold := integral_split_row (P := P) A i (hFm s) (hFC s)
    rw [hnew.1, hold.1, ← integral_const_mul]
    -- After fixing the other rows, the remaining factors depend only on the query.
    have hrow (R : Fin n → 𝒳) :
        (∫ x, ∫ q, F (insert i s) (i.insertNth x R, q) ∂(A (i.insertNth x R)) ∂P) ≤
          Real.exp c * ∫ x, ∫ q, F s (i.insertNth x R, q) ∂(A (i.insertNth x R)) ∂P := by
      let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ 𝒳) i).symm
      have he : Measurable (fun x : 𝒳 ↦ i.insertNth (α := fun _ ↦ 𝒳) x R) :=
        e.measurable.comp (measurable_id.prodMk (measurable_const (a := R)))
      let B := A.comap _ he
      let g q := F s (i.insertNth x₀ R, q)
      have hg : Measurable g := (hFm s).comp (measurable_prodMk_left (x := e (x₀, R)))
      have hB x y : B y ≤ ENNReal.ofReal (Real.exp ε) • B x := by
        apply differentiallyPrivate_zero_iff_le_smul.mp hA
        refine Or.inr ⟨i, fun j hj ↦ ?_⟩
        obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
        simp
      have hrest (x : 𝒳) q : F s (i.insertNth x R, q) = g q := by
        apply congrArg Real.exp
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := fun e ↦ his (e ▸ hj)
        obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
        simp [D]
      have hinsert (x : 𝒳) q :
          F (insert i s) (i.insertNth x R, q) = g q * Real.exp (t * (φ q x - m q)) := by
        rw [show F (insert i s) (i.insertNth x R, q) =
          Real.exp (t * ∑ j ∈ insert i s, D j (i.insertNth x R, q)) from rfl,
          Finset.sum_insert his, mul_add, Real.exp_add, mul_comm, ← hrest x q]
        simp [F, D]
      have hmoment := row_moment_le (P := P) B hφ hφ01 hε ht ht' hB hg
        (fun q ↦ (hFpos _ _).le) (fun q ↦ le_of_abs_le (hFC s (i.insertNth x₀ R, q)))
      dsimp only at hmoment
      have hgprod : Measurable (fun p : 𝒳 × Q ↦ g p.2 * Real.exp (t * (φ p.2 p.1 - m p.2))) :=
        (hg.comp measurable_snd).mul
          ((measurable_const.mul ((hφ.comp measurable_swap).sub (hm.comp measurable_snd))).exp)
      have i₁ : Integrable (fun p : 𝒳 × Q ↦ g p.2 * Real.exp (t * (φ p.2 p.1 - m p.2)))
          (P ⊗ₘ B) := integrable_bounded hgprod fun p ↦ by
        rw [← hinsert]
        exact hFC _ _
      have i₀ : Integrable (fun p : 𝒳 × Q ↦ g p.2) (P ⊗ₘ B) :=
        integrable_bounded (hg.comp measurable_snd) fun p ↦ hFC _ _
      rw [Measure.integral_compProd i₁, Measure.integral_compProd i₀] at hmoment
      simpa only [B, Kernel.comap_apply, c, hinsert, hrest] using hmoment
    exact integral_mono hnew.2 (hold.2.const_mul _) hrow

private theorem upper_tail {P : Measure 𝒳} [IsProbabilityMeasure P] {n : ℕ}
    (A : Kernel (Fin (n + 1) → 𝒳) Q) [IsMarkovKernel A] {φ : Q → 𝒳 → ℝ}
    (hφ : Measurable (Function.uncurry φ)) (hφ01 : ∀ q z, φ q z ∈ Icc (0 : ℝ) 1)
    {ε β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) (hτ' : τ ≤ 1)
    (hn : 12 * Real.log (4 / β) / τ ^ 2 ≤ ((n + 1 : ℕ) : ℝ))
    (hε₀ : 0 ≤ ε) (hε : ε ≤ τ / 2) (hA : DifferentiallyPrivate hammingAdj (fun S ↦ A S) ε 0) :
    ((Measure.pi fun _ : Fin (n + 1) ↦ P) ⊗ₘ A)
      {p | ((n + 1 : ℕ) : ℝ) * τ ≤ ∑ i, (φ p.2 (p.1 i) - ∫ z, φ p.2 z ∂P)} ≤
      ENNReal.ofReal (β / 4) := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let μ := (Measure.pi fun _ : Fin (n + 1) ↦ P) ⊗ₘ A
  let X (p : (Fin (n + 1) → 𝒳) × Q) := ∑ i, (φ p.2 (p.1 i) - ∫ z, φ p.2 z ∂P)
  let t := τ / 3
  have ht : 0 ≤ t := by positivity
  have ht' : t ≤ 1 / 3 := by dsimp [t]; linarith
  have hM := exponential_sum_bound (P := P) A hφ hφ01 hε₀ ht ht' hA Finset.univ
  have hMg : mgf X μ t ≤ Real.exp (N * (t * ε + (3 / 4) * t ^ 2)) := by
    simpa only [mgf, X, N, μ, Finset.card_univ, Fintype.card_fin] using hM.2
  have hchernoff := measure_ge_le_exp_mul_mgf (X := X) (μ := μ) (N * τ) ht hM.1
  rw [← ofReal_measureReal (μ := μ) (s := {p | N * τ ≤ X p})]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.exp (-t * (N * τ)) * mgf X μ t := hchernoff
    _ ≤ Real.exp (-t * (N * τ)) * Real.exp (N * (t * ε + (3 / 4) * t ^ 2)) :=
      mul_le_mul_of_nonneg_left hMg (Real.exp_pos _).le
    _ ≤ Real.exp (-(N * τ ^ 2) / 12) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have h : -t * τ + (t * ε + (3 / 4) * t ^ 2) ≤ -τ ^ 2 / 12 := by
        dsimp [t]
        nlinarith [mul_le_mul_of_nonneg_left hε hτ.le]
      calc
        _ = N * (-t * τ + (t * ε + (3 / 4) * t ^ 2)) := by ring
        _ ≤ N * (-τ ^ 2 / 12) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = _ := by ring
    _ ≤ Real.exp (-Real.log (4 / β)) := by
      apply Real.exp_le_exp.mpr
      have hs := (div_le_iff₀ (sq_pos_of_pos hτ)).mp hn
      change 12 * Real.log (4 / β) ≤ N * τ ^ 2 at hs
      linarith
    _ = β / 4 := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]

end differentiallyPrivate_transfer

-- Preserve the universe parameter names of the original wanted declaration.
open differentiallyPrivate_transfer in
/-- **Transfer theorem for adaptive data analysis.** Let `P` be a probability distribution on
`𝒳`, let the data set `S` consist of `n` independent samples from `P`, and let the analyst's
algorithm `A`, a Markov kernel from data sets to a space `Q` of queries `φ q : 𝒳 → [0, 1]`, be
`ε`-differentially private for data sets differing in one element. If `β, τ > 0`,
`n ≥ 12 ln (4 / β) / τ ^ 2` and `0 ≤ ε ≤ τ / 2`, then the selected query `q ~ A(S)` satisfies
`|E_P[φ q] - (1/n) ∑ i, φ q (S i)| ≤ τ` except with probability at most `β`, over both `S` and
the randomness of `A` (Dwork, Feldman, Hardt, Pitassi, Reingold and Roth, *Preserving
Statistical Validity in Adaptive Data Analysis*, arXiv:1411.2664v3, identical in v2, Theorem 9;
preliminary version in STOC 2015). Taking the queries from a measurable space `Q`, with `φ`
jointly measurable, is this formalization's choice; the source lets the algorithm output any
function from `𝒳` to `[0, 1]`. -/
theorem differentiallyPrivate_transfer.{u_2, u_3} {𝒳 : Type u_2} {Q : Type u_3}
    [MeasurableSpace 𝒳] [MeasurableSpace Q] {P : Measure 𝒳} [IsProbabilityMeasure P] {n : ℕ}
    (A : Kernel (Fin n → 𝒳) Q) [IsMarkovKernel A] (φ : Q → 𝒳 → ℝ)
    (hφ : Measurable (Function.uncurry φ)) (hφ01 : ∀ q z, φ q z ∈ Set.Icc (0 : ℝ) 1)
    {ε β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) (hn : 12 * Real.log (4 / β) / τ ^ 2 ≤ n)
    (hε₀ : 0 ≤ ε) (hε : ε ≤ τ / 2) (hA : DifferentiallyPrivate hammingAdj (fun S ↦ A S) ε 0) :
    ((Measure.pi fun _ : Fin n ↦ P) ⊗ₘ A)
        {p | τ < |∫ z, φ p.2 z ∂P - (1 / n : ℝ) * ∑ i, φ p.2 (p.1 i)|} ≤ ENNReal.ofReal β := by
  by_cases hβ' : 1 ≤ β
  · refine (measure_mono (subset_univ _)).trans ?_
    simpa only [measure_univ, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hβ'
  have hn' : 0 < n := by
    have hlog : 0 < Real.log (4 / β) := Real.log_pos ((one_lt_div₀ hβ).mpr (by linarith))
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 12 * Real.log (4 / β) / τ ^ 2) hn)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn'.ne'
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN : 0 < N := by positivity
  let μ := (Measure.pi fun _ : Fin (n + 1) ↦ P) ⊗ₘ A
  let m q := ∫ z, φ q z ∂P
  let X (p : (Fin (n + 1) → 𝒳) × Q) := ∑ i, (φ p.2 (p.1 i) - m p.2)
  have hEq (p : (Fin (n + 1) → 𝒳) × Q) :
      m p.2 - (1 / N) * ∑ i, φ p.2 (p.1 i) = -X p / N := by
    simp only [X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    change m p.2 - (1 / N) * ∑ i, φ p.2 (p.1 i) =
      -(∑ i, φ p.2 (p.1 i) - N * m p.2) / N
    field_simp
    ring
  change μ {p | τ < |m p.2 - (1 / N) * ∑ i, φ p.2 (p.1 i)|} ≤ ENNReal.ofReal β
  simp only [hEq, abs_div, abs_neg, abs_of_pos hN]
  by_cases hτ' : τ ≤ 1
  · have hup := upper_tail (P := P) A hφ hφ01 hβ hτ hτ' hn hε₀ hε hA
    let ψ (q : Q) (z : 𝒳) := 1 - φ q z
    have hψ : Measurable (Function.uncurry ψ) := measurable_const.sub hφ
    have hψ01 q z : ψ q z ∈ Icc (0 : ℝ) 1 :=
      ⟨sub_nonneg.mpr (hφ01 q z).2, by dsimp [ψ]; linarith [(hφ01 q z).1]⟩
    have hneg (p : (Fin (n + 1) → 𝒳) × Q) :
        (∑ i, (ψ p.2 (p.1 i) - ∫ z, ψ p.2 z ∂P)) = -X p := by
      have hφi : Integrable (φ p.2) P :=
        integrable_bounded (hφ.comp (measurable_prodMk_left (x := p.2))) fun z ↦ by
          rw [abs_of_nonneg (hφ01 p.2 z).1]
          exact (hφ01 p.2 z).2
      have hmean : (∫ z, ψ p.2 z ∂P) = 1 - m p.2 := integral_one_sub hφi
      dsimp only [X]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hmean]
      dsimp [ψ]
      ring
    have hlo : μ {p | N * τ ≤ -X p} ≤ ENNReal.ofReal (β / 4) := by
      simpa only [hneg] using upper_tail (P := P) A hψ hψ01 hβ hτ hτ' hn hε₀ hε hA
    have hsub : {p | τ < |X p| / N} ⊆ {p | N * τ ≤ X p} ∪ {p | N * τ ≤ -X p} := by
      intro p hp
      have hlt : N * τ < |X p| := by simpa only [mul_comm N] using (lt_div_iff₀ hN).mp hp
      rcases lt_abs.mp hlt with h | h
      · exact Or.inl h.le
      · exact Or.inr h.le
    calc
      _ ≤ μ ({p | N * τ ≤ X p} ∪ {p | N * τ ≤ -X p}) := measure_mono hsub
      _ ≤ μ {p | N * τ ≤ X p} + μ {p | N * τ ≤ -X p} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (β / 4) + ENNReal.ofReal (β / 4) := add_le_add hup hlo
      _ ≤ _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
  · have hempty : {p | τ < |X p| / N} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hm : m p.2 ∈ Icc (0 : ℝ) 1 :=
        integral_mem_Icc (hφ.comp (measurable_prodMk_left (x := p.2))) (hφ01 p.2)
      have hX : |X p| ≤ N := calc
        _ ≤ ∑ i, |φ p.2 (p.1 i) - m p.2| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin (n + 1), (1 : ℝ) := Finset.sum_le_sum fun i _ ↦
          abs_le.mpr ⟨by linarith [(hφ01 p.2 (p.1 i)).1, hm.2],
            by linarith [(hφ01 p.2 (p.1 i)).2, hm.1]⟩
        _ = _ := by simp [N]
      have hle : |X p| / N ≤ 1 := (div_le_iff₀ hN).mpr (by simpa using hX)
      exact hτ' (hp.trans_le hle).le
    simp [hempty]

end Cslib.Crypto.Privacy
