/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Instances.Real
public import MathlibExt.Geometry.Manifold.MorseTheory
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

section
/-!
# Morse lemma

Wishlist Morse lemma at the origin of `ℝⁿ`: a `C^∞` function with critical
point `0` and nondegenerate Hessian is locally `f 0 + Q_k ∘ φ` for a
`C^∞` local diffeomorphism `φ` fixing `0`.
-/

noncomputable section

open scoped Manifold ContDiff Interval RealInnerProductSpace RightActions
open Set Filter Topology

namespace MathlibExt.Geometry.Manifold.MorseLemmaWanted

open MathlibExt.Geometry.Manifold.MorseTheoryWanted

/-- Standard basis vector of Euclidean space. -/
private abbrev eVec {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  PiLp.single 2 i (1 : ℝ)

/-- Coordinate projection as a continuous linear map. -/
private abbrev coordProj {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin n => ℝ) i

/-- Coordinate expansion in Euclidean space. -/
private lemma coord_expansion {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    x = ∑ i, (x i) • eVec i := by
  conv_lhs => rw [← (PiLp.basisFun 2 ℝ (Fin n)).sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.basisFun_repr, PiLp.basisFun_apply, eVec]

/-- The `i`-th coordinate projection as a continuous linear map. -/
private lemma proj_apply_eq {n : ℕ} (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    coordProj i x = x i := rfl

/-- A continuous linear functional applied to a vector, in coordinates. -/
private lemma clm_apply_expansion {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    L v = ∑ i, (v i) * L (eVec i) := by
  conv_lhs => rw [coord_expansion v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  exact smul_eq_mul _ _

/-- A finset of `Fin n` can be moved to an initial segment by a permutation. -/
private lemma perm_initial_segment {n : ℕ} (s : Finset (Fin n)) :
    ∃ (p : Fin n ≃ Fin n) (k : ℕ),
      s.card = k ∧ ∀ i, p i ∈ s ↔ (i : ℕ) < k := by
  classical
  have hle : s.card ≤ n := by simpa using Finset.card_le_univ s
  have hsum : s.card + (n - s.card) = n := Nat.add_sub_cancel' hle
  have hscompl : sᶜ.card = n - s.card := by simp [Finset.card_compl]
  let e₁ : Fin s.card ≃o { x : Fin n // x ∈ s } := Finset.orderIsoOfFin s rfl
  let e₂ : Fin (n - s.card) ≃o { x : Fin n // x ∈ sᶜ } := Finset.orderIsoOfFin sᶜ hscompl
  let cEquiv : { x : Fin n // x ∉ s } ≃ { x : Fin n // x ∈ sᶜ } :=
    Equiv.subtypeEquivRight (fun x => Finset.mem_compl.symm)
  let eMid : { x : Fin n // x ∈ s } ⊕ { x : Fin n // x ∉ s } ≃ Fin s.card ⊕ Fin (n - s.card) :=
    Equiv.sumCongr e₁.symm.toEquiv (cEquiv.trans e₂.symm.toEquiv)
  let e : Fin n ≃ Fin n :=
    (Equiv.sumCompl (· ∈ s)).symm.trans
      (eMid.trans (finSumFinEquiv.trans (finCongr hsum)))
  refine ⟨e.symm, s.card, rfl, fun i => ?_⟩
  have key : ∀ j : Fin n, (e j : ℕ) < s.card ↔ j ∈ s := by
    intro j
    by_cases hj : j ∈ s
    · have h1 : (Equiv.sumCompl (· ∈ s)).symm j = Sum.inl (⟨j, hj⟩ : { x : Fin n // x ∈ s }) :=
        Equiv.sumCompl_symm_apply_of_pos hj
      simp only [e, Equiv.trans_apply, h1, eMid, Equiv.sumCongr_apply, Sum.map_inl,
        finSumFinEquiv_apply_left, hj, iff_true]
      have hval : ((finCongr hsum) (Fin.castAdd (n - s.card) (e₁.symm.toEquiv ⟨j, hj⟩)) : ℕ)
          = ((e₁.symm.toEquiv ⟨j, hj⟩ : Fin s.card) : ℕ) := rfl
      rw [hval]
      exact Fin.is_lt _
    · have h1 : (Equiv.sumCompl (· ∈ s)).symm j = Sum.inr (⟨j, hj⟩ : { x // x ∉ s }) :=
        Equiv.sumCompl_symm_apply_of_neg hj
      simp only [e, Equiv.trans_apply, h1, eMid, Equiv.sumCongr_apply, Sum.map_inr,
        finSumFinEquiv_apply_right, hj, iff_false]
      have hval : ((finCongr hsum) (Fin.natAdd s.card
            (e₂.symm.toEquiv (cEquiv ⟨j, hj⟩))) : ℕ)
          = s.card + (((e₂.symm.toEquiv (cEquiv ⟨j, hj⟩)) : Fin (n - s.card)) : ℕ) := rfl
      rw [hval]
      omega
  rw [← key (e.symm i), e.apply_symm_apply]

/-- The top smoothness order is nonzero. -/
private lemma top_order_ne_zero : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0 := by simp

/-- The unit interval `Ι 0 1` lies in `Icc 0 1`. -/
private lemma uIoc01_subset_Icc01 : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := by
  rw [Set.uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  exact Set.Ioc_subset_Icc_self

/-- Local uniform bound for a continuous integrand on `[0,1] × ball`. -/
private lemma parametric_bound {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {J : ℝ × EuclideanSpace ℝ (Fin n) → F} (hJ : Continuous J)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ C, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Metric.ball x₀ 1, ‖J (t, x)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod
    (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn hJ.continuousOn
  exact ⟨C, fun t ht x hx =>
    hC (t, x) ⟨ht, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx))⟩⟩

/-- Finite-order smoothness of a parametric interval integral over `[0,1]`. -/
private theorem contDiffAt_parametric_aux {n : ℕ} :
    ∀ (m : ℕ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {H : ℝ × EuclideanSpace ℝ (Fin n) → F} (_ : ContDiff ℝ (⊤ : ℕ∞) H)
    (x₀ : EuclideanSpace ℝ (Fin n)),
    ContDiffAt ℝ (m : ℕ∞ω) (fun x => ∫ t in (0 : ℝ)..1, H (t, x)) x₀ := by
  intro m
  induction m with
  | zero =>
    intro F iN iS iC H hH x₀
    have hcast : ((0 : ℕ) : ℕ∞ω) = 0 := by simp
    rw [hcast, contDiffAt_zero]
    refine ⟨Metric.ball x₀ 1, Metric.ball_mem_nhds x₀ (by norm_num),
      fun x₁ _ => ?_⟩
    obtain ⟨C, hC⟩ := parametric_bound hH.continuous x₁
    have hmem : Metric.ball x₁ (1 : ℝ) ∈ 𝓝 x₁ :=
      Metric.ball_mem_nhds _ (by norm_num)
    have hAt : ContinuousAt (fun x => ∫ t in (0 : ℝ)..1, H (t, x)) x₁ := by
      refine intervalIntegral.continuousAt_of_dominated_interval
        (F := fun x t => H (t, x)) (x₀ := x₁) (bound := fun _ => C)
        (a := 0) (b := 1) (μ := MeasureTheory.volume) ?_ ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun x =>
          (hH.continuous.comp
            (continuous_id.prodMk continuous_const)).stronglyMeasurable.aestronglyMeasurable
      · refine Filter.eventually_of_mem hmem fun x hx => ?_
        exact Filter.Eventually.of_forall fun t ht =>
          hC t (uIoc01_subset_Icc01 ht) x hx
      · exact intervalIntegrable_const
      · exact Filter.Eventually.of_forall fun t _ =>
          hH.continuous.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
    exact hAt.continuousWithinAt
  | succ m ih =>
    intro F iN iS iC H hH x₀
    have hcast : ((m + 1 : ℕ) : ℕ∞ω) = (m : ℕ∞ω) + 1 := by simp
    rw [hcast, contDiffAt_succ_iff_hasFDerivAt]
    have hinner : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : (ℝ × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) =>
          (q.1.1, q.2)) :=
      (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
    have hf2 : ContDiff ℝ (⊤ : ℕ∞)
        (Function.uncurry (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          fun x' : EuclideanSpace ℝ (Fin n) => H (p.1, x'))) :=
      hH.comp hinner
    have hle : ((⊤ : ℕ∞) : ℕ∞ω) + 1 ≤ (⊤ : ℕ∞) := by simp
    have hD2 : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          fderiv ℝ (fun x' : EuclideanSpace ℝ (Fin n) => H (p.1, x')) p.2) :=
      ContDiff.fderiv hf2 contDiff_snd hle
    have hG' : ContDiffAt ℝ (m : ℕ∞ω)
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ∫ t in (0 : ℝ)..1,
            fderiv ℝ (fun x' : EuclideanSpace ℝ (Fin n) => H (t, x')) x) x₀ :=
      ih hD2 x₀
    refine ⟨fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun x' : EuclideanSpace ℝ (Fin n) => H (t, x')) x,
      ⟨Metric.ball x₀ 1, Metric.ball_mem_nhds x₀ (by norm_num), fun x₁ hx₁ => ?_⟩,
      hG'⟩
    obtain ⟨C, hC⟩ := parametric_bound hD2.continuous x₀
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun x t => H (t, x))
      (F' := fun x t => fderiv ℝ (fun x' : EuclideanSpace ℝ (Fin n) => H (t, x')) x)
      (x₀ := x₁) (s := Metric.ball x₀ 1) (bound := fun _ => C)
      (a := 0) (b := 1) (μ := MeasureTheory.volume) (𝕜 := ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact Metric.isOpen_ball.mem_nhds hx₁
    · exact Filter.Eventually.of_forall fun x =>
        (hH.continuous.comp
          (continuous_id.prodMk continuous_const)).stronglyMeasurable.aestronglyMeasurable
    · exact (hH.continuous.comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    · exact (hD2.continuous.comp
        (continuous_id.prodMk continuous_const)).stronglyMeasurable.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t ht x hx =>
        hC t (uIoc01_subset_Icc01 ht) x hx
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun t _ x _ => ?_
      have hdiff : DifferentiableAt ℝ
          (fun x : EuclideanSpace ℝ (Fin n) => H (t, x)) x :=
        DifferentiableAt.comp x (hH.contDiffAt.differentiableAt top_order_ne_zero)
          ((differentiableAt_const t).prodMk differentiableAt_id)
      exact hdiff.hasFDerivAt

/-- A parametric interval integral of a smooth integrand over `[0,1]` is smooth. -/
private theorem contDiff_parametric_intervalIntegral {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (H : ℝ × EuclideanSpace ℝ (Fin n) → F) (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ t in (0 : ℝ)..1, H (t, x)) := by
  refine contDiff_infty.mpr fun m => ?_
  rw [contDiff_iff_contDiffAt]
  intro x₀
  exact contDiffAt_parametric_aux m hH x₀

/-- Smoothness order arithmetic. -/
private lemma top_succ_le : ((⊤ : ℕ∞) : ℕ∞ω) + 1 ≤ (⊤ : ℕ∞) := by simp

/-- `ContDiffOn` on a set from pointwise `ContDiffAt`. -/
private lemma contDiffOn_of_contDiffAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {V : Set E}
    {f : E → F}
    (h : ∀ x ∈ V, ContDiffAt ℝ (⊤ : ℕ∞) f x) : ContDiffOn ℝ (⊤ : ℕ∞) f V := by
  intro x hx
  exact (h x hx).contDiffWithinAt

/-- `ContDiffAt` from `ContDiffOn` on an open set. -/
private lemma contDiffAt_of_contDiffOn_of_mem_open {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : Set E} (hV : IsOpen V)
    {f : E → F} (h : ContDiffOn ℝ (⊤ : ℕ∞) f V)
    {x : E} (hx : x ∈ V) : ContDiffAt ℝ (⊤ : ℕ∞) f x :=
  (h x hx).contDiffAt (hV.mem_nhds hx)

/-- Coefficient matrix for the second-order Taylor expansion with integral
remainder. Each entry is a scalar parameter integral. -/
private noncomputable def morseCoeff {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Fin n → Fin n → ℝ :=
  fun i j => ∫ t in (0 : ℝ)..1,
    (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i)

/-- Taylor formula with integral remainder at a critical point. -/
private lemma morse_coeff_form {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcrit : fderiv ℝ f (0 : EuclideanSpace ℝ (Fin n)) = 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    f x = f 0 + ∑ i, ∑ j, (x i) * (x j) * morseCoeff f x i j := by
  have hDf : ∀ y : EuclideanSpace ℝ (Fin n), HasFDerivAt f (fderiv ℝ f y) y :=
    fun y => (hf.contDiffAt.differentiableAt top_order_ne_zero).hasFDerivAt
  have hD1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right top_succ_le
  have hDDf : ∀ y : EuclideanSpace ℝ (Fin n),
      HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) y :=
    fun y => (hD1.contDiffAt.differentiableAt top_order_ne_zero).hasFDerivAt
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hD1.fderiv_right top_succ_le).continuous
  have hc : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t • x) x t := by
    intro t
    simpa using (hasDerivAt_id t).smul_const x
  have hh : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (s • x)) (fderiv ℝ f (t • x) x) t :=
    fun t => (hDf (t • x)).comp_hasDerivAt t (hc t)
  have hClm : ∀ y : EuclideanSpace ℝ (Fin n),
      HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => fderiv ℝ f z x)
        ((fderiv ℝ (fderiv ℝ f) y).flip x) y := by
    intro y
    simpa using (hDDf y).clm_apply (hasFDerivAt_const x y)
  have hk : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => fderiv ℝ f (s • x) x)
        (fderiv ℝ (fderiv ℝ f) (t • x) x x) t := by
    intro t
    exact (hClm (t • x)).comp_hasDerivAt t (hc t)
  have hPhi : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => (1 - s) * fderiv ℝ f (s • x) x + f (s • x))
      ((1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x) t := by
    intro t
    have hc1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      have h := (hasDerivAt_id t).const_sub (1 : ℝ)
      simpa using h
    have hmul := hc1.mul (hk t)
    have hadd := hmul.add (hh t)
    have hring : (-1 : ℝ) * fderiv ℝ f (t • x) x
        + (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x + fderiv ℝ f (t • x) x
        = (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x := by ring
    rw [hring] at hadd
    exact hadd
  have hint : IntervalIntegrable
      (fun t : ℝ => (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.sub continuous_id).mul
      (((hD2c.comp (continuous_id.smul continuous_const)).clm_apply
        continuous_const).clm_apply continuous_const)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hPhi t) hint
  have hk0' : fderiv ℝ f (0 : EuclideanSpace ℝ (Fin n)) x = 0 := by
    rw [hcrit]
    rfl
  have hexpand : ∀ y : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fderiv ℝ f) y x x
        = ∑ i, ∑ j, (x i) * (x j) * fderiv ℝ (fderiv ℝ f) y (eVec j) (eVec i) := by
    intro y
    have e1 := clm_apply_expansion (fderiv ℝ (fderiv ℝ f) y x) x
    have e2 : ∀ i : Fin n, fderiv ℝ (fderiv ℝ f) y x (eVec i)
        = ∑ j, (x j) * fderiv ℝ (fderiv ℝ f) y (eVec j) (eVec i) := by
      intro i
      have e := clm_apply_expansion
        ((fderiv ℝ (fderiv ℝ f) y).flip (eVec i)) x
      simpa only [ContinuousLinearMap.flip_apply] using e
    rw [e1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e2 i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hcont_entry : ∀ i : Fin n, ∀ j : Fin n, Continuous (fun t : ℝ =>
      (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i)) := by
    intro i j
    exact (continuous_const.sub continuous_id).mul
      (((hD2c.comp (continuous_id.smul continuous_const)).clm_apply
        continuous_const).clm_apply continuous_const)
  have hmove : (∫ t in (0 : ℝ)..1,
        (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x)
      = ∑ i, ∑ j, (x i) * (x j) * morseCoeff f x i j := by
    have hInt : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ j ∈ Finset.univ,
        IntervalIntegrable (fun t : ℝ => (1 - t) *
          fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i))
          MeasureTheory.volume 0 1 := by
      intro i _ j _
      exact (hcont_entry i j).intervalIntegrable 0 1
    have hstep1 : (∫ t in (0 : ℝ)..1,
          (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x)
        = ∫ t in (0 : ℝ)..1, ∑ i, ∑ j, ((x i) * (x j)) *
          ((1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i)) := by
      refine intervalIntegral.integral_congr_ae
        (Filter.Eventually.of_forall fun t _ => ?_)
      rw [hexpand (t • x)]
      simp only [Finset.mul_sum]
      ring_nf
    have hInt_outer : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        IntervalIntegrable
          ((fun (i : Fin n) (t : ℝ) => ∑ j, ((x i) * (x j)) *
            ((1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i))) i)
          MeasureTheory.volume 0 1 := by
      intro i _
      have hcsum : Continuous (fun t : ℝ => ∑ j, ((x i) * (x j)) *
          ((1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i))) :=
        continuous_finsetSum Finset.univ
          (fun j _ => continuous_const.mul (hcont_entry i j))
      exact hcsum.intervalIntegrable 0 1
    have hpull_outer : (∫ t in (0 : ℝ)..1, ∑ i, ∑ j, ((x i) * (x j)) *
          ((1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i)))
        = ∑ i, ∫ t in (0 : ℝ)..1, ∑ j, ((x i) * (x j)) *
          ((1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i)) :=
      intervalIntegral.integral_finsetSum
        (f := fun (i : Fin n) (t : ℝ) => ∑ j, ((x i) * (x j)) *
          ((1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i)))
        (fun i hi => hInt_outer i hi)
    calc (∫ t in (0 : ℝ)..1,
            (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x)
        = ∫ t in (0 : ℝ)..1, ∑ i, ∑ j, ((x i) * (x j)) *
            ((1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i)) :=
          hstep1
      _ = ∑ i, ∫ t in (0 : ℝ)..1, ∑ j, ((x i) * (x j)) *
            ((1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i)) :=
          hpull_outer
      _ = ∑ i, ∑ j, (x i) * (x j) * morseCoeff f x i j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hpull_inner : (∫ t in (0 : ℝ)..1, ∑ j, ((x i) * (x j)) *
              ((1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i)))
              = ∑ j, ∫ t in (0 : ℝ)..1, ((x i) * (x j)) *
                ((1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i)) :=
            intervalIntegral.integral_finsetSum
              (f := fun (j : Fin n) (t : ℝ) => ((x i) * (x j)) *
                ((1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i)))
              (fun j hj => (hInt i (Finset.mem_univ i) j hj).const_mul _)
          rw [hpull_inner]
          refine Finset.sum_congr rfl fun j _ => ?_
          exact intervalIntegral.integral_const_mul ((x i) * (x j))
            (fun t : ℝ => (1 - t) *
              fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i))
  rw [← hmove, hFTC]
  simp only [one_smul, zero_smul, hk0', sub_self, zero_mul, zero_add, sub_zero,
    one_mul]
  ring

/-- The coefficient matrix field is smooth. -/
private lemma morse_coeff_smooth {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (morseCoeff f) := by
  have hD2 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right top_succ_le).fderiv_right top_succ_le
  have hsm : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => p.1 • p.2) :=
    contDiff_fst.smul contDiff_snd
  have hscal : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        (1 - p.1) * (fderiv ℝ (fderiv ℝ f)) (p.1 • p.2) (eVec j) (eVec i)) := by
    intro i j
    have hmid : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          (fderiv ℝ (fderiv ℝ f)) (p.1 • p.2) (eVec j) (eVec i)) :=
      ((hD2.comp hsm).clm_apply contDiff_const).clm_apply contDiff_const
    exact (contDiff_const.sub contDiff_fst).mul hmid
  have hcoeff : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin n) => morseCoeff f x i j) := by
    intro i j
    have htmp := contDiff_parametric_intervalIntegral
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        (1 - p.1) * (fderiv ℝ (fderiv ℝ f)) (p.1 • p.2) (eVec j) (eVec i))
      (hscal i j)
    simpa [morseCoeff] using htmp
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  exact hcoeff i j

/-- The scalar integral `∫₀¹ (1 - t) dt = 1 / 2`. -/
private lemma morse_scalar_half :
    (∫ t in (0 : ℝ)..1, (1 - t)) = 1 / 2 := by
  have hF : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => t - t ^ 2 / 2) (1 - t) t := by
    intro t _
    have h4 := (hasDerivAt_id t).sub
      (((hasDerivAt_id t).mul (hasDerivAt_id t)).div_const (2 : ℝ))
    have e1 : (fun t : ℝ => t - t ^ 2 / 2)
        = id - (fun x : ℝ => id x * id x / 2) := by
      funext x
      simp only [id_eq, Pi.sub_apply]
      ring
    have e2 : (1 : ℝ) - t = 1 - (1 * t + t * 1) / 2 := by ring
    rw [e1, e2]
    exact h4
  have hint : IntervalIntegrable (fun t : ℝ => 1 - t) MeasureTheory.volume 0 1 :=
    (continuous_const.sub continuous_id).intervalIntegrable 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
  have hval : (fun t : ℝ => t - t ^ 2 / 2) (1 : ℝ)
      - (fun t : ℝ => t - t ^ 2 / 2) (0 : ℝ) = 1 / 2 := by norm_num
  rw [hFTC]
  exact hval

/-- The coefficient matrix at the critical point is half the Hessian matrix. -/
private lemma morse_coeff_zero {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (i j : Fin n) :
    morseCoeff f 0 i j
      = (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 (eVec j) (eVec i) := by
  have hzero : ∀ t : ℝ, (1 - t) *
      fderiv ℝ (fderiv ℝ f) (t • (0 : EuclideanSpace ℝ (Fin n))) (eVec j) (eVec i)
      = (1 - t) * fderiv ℝ (fderiv ℝ f) 0 (eVec j) (eVec i) := by
    intro t
    rw [smul_zero]
  simp only [morseCoeff]
  simp_rw [hzero, intervalIntegral.integral_mul_const, morse_scalar_half]

/-- The coefficient matrix is symmetric. -/
private lemma morse_coeff_symm {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    morseCoeff f x i j = morseCoeff f x j i := by
  have hsym : ∀ t : ℝ, fderiv ℝ (fderiv ℝ f) (t • x) (eVec j) (eVec i)
      = fderiv ℝ (fderiv ℝ f) (t • x) (eVec i) (eVec j) := by
    intro t
    exact ((hf.contDiffAt).isSymmSndFDerivAt (by simp)).eq _ _
  unfold morseCoeff
  refine intervalIntegral.integral_congr_ae
    (Filter.Eventually.of_forall fun t _ => ?_)
  rw [hsym t]

/-- Operator assembly from the Taylor coefficient matrix, as a sum of
constant rank-one operators with smooth scalar coefficients. -/
private noncomputable def morseOp {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ∑ i, ∑ j, (morseCoeff f x i j) • (coordProj j).smulRight (eVec i)

/-- The operator assembly is smooth in the base point. -/
private lemma morse_op_smooth {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (morseOp f) := by
  have hcoeff : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin n) => morseCoeff f x i j) := by
    intro i j
    have htmp := morse_coeff_smooth hf
    have h1 := (contDiff_pi.mp htmp) i
    exact (contDiff_pi.mp h1) j
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j,
      (morseCoeff f x i j) • (coordProj j).smulRight (eVec i))
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact (hcoeff i j).smul contDiff_const

/-- Expansion of the assembled operator applied to a vector, in coordinates. -/
private lemma morse_op_apply {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) :
    morseOp f x v = ∑ i, ∑ j, (morseCoeff f x i j) • ((v j) • eVec i) := by
  change ((∑ i, ∑ j, (morseCoeff f x i j) • (coordProj j).smulRight (eVec i)) v) = _
  simp [ContinuousLinearMap.smulRight_apply]

/-- Expansion of the operator quadratic form in coordinates. -/
private lemma morse_op_inner {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v w : EuclideanSpace ℝ (Fin n)) :
    ⟪morseOp f x v, w⟫ = ∑ i, ∑ j, (morseCoeff f x i j) * (v j) * (w i) := by
  have heVec : ∀ i : Fin n, ⟪eVec i, w⟫ = w i := by
    intro i
    have h2 : ⟪eVec i, w⟫ = (starRingEnd ℝ) (1 : ℝ) * w.ofLp i :=
      EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ) w
    simpa using h2
  rw [morse_op_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_left, heVec]
  simp only [starRingEnd_apply, star_trivial]
  ring

/-- The assembled operator at the origin is half the Hessian. -/
private lemma morse_op_half {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (v w : EuclideanSpace ℝ (Fin n)) :
    ⟪morseOp f 0 v, w⟫
      = (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ f) 0 v) w := by
  have e1 := clm_apply_expansion (fderiv ℝ (fderiv ℝ f) 0 v) w
  have e2 : ∀ i : Fin n, (fderiv ℝ (fderiv ℝ f)) 0 v (eVec i)
      = ∑ j, (v j) * (fderiv ℝ (fderiv ℝ f)) 0 (eVec j) (eVec i) := by
    intro i
    have e := clm_apply_expansion
      ((fderiv ℝ (fderiv ℝ f) 0).flip (eVec i)) v
    simpa only [ContinuousLinearMap.flip_apply] using e
  rw [morse_op_inner]
  conv_rhs => rw [e1]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [e2 i, ← mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [morse_coeff_zero]
  ring

/-- Self-adjoint operator form of the second-order remainder. -/
private theorem morse_operator_form {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcrit : fderiv ℝ f (0 : EuclideanSpace ℝ (Fin n)) = 0)
    (hHess : ∀ v : EuclideanSpace ℝ (Fin n),
      (∀ w : EuclideanSpace ℝ (Fin n),
        (fderiv ℝ (fderiv ℝ f) (0 : EuclideanSpace ℝ (Fin n)) v) w = 0) → v = 0) :
    ∃ Bop : EuclideanSpace ℝ (Fin n) →
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ (⊤ : ℕ∞) Bop ∧
      (∀ x, star (Bop x) = Bop x) ∧
      (∀ x, f x = f 0 + ⟪Bop x x, x⟫) ∧
      (∀ v w, ⟪Bop 0 v, w⟫ =
        (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ f) 0 v) w) ∧
      Function.Injective (Bop 0) := by
  refine ⟨morseOp f, morse_op_smooth hf, ?_, ?_, fun v w => morse_op_half f v w, ?_⟩
  · intro x
    have hsym : ((morseOp f x : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric := by
      intro v w
      change ⟪morseOp f x v, w⟫ = ⟪v, morseOp f x w⟫
      have e1 := morse_op_inner f x v w
      have e2 := morse_op_inner f x w v
      rw [e1]
      conv_rhs => rw [real_inner_comm]
      rw [e2]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [morse_coeff_symm hf x j i]
      ring
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hsym
  · intro x
    have hform := morse_coeff_form hf hcrit x
    rw [hform, morse_op_inner]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · intro a b hab
    have hsub : morseOp f 0 (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h0 : a - b = 0 := by
      apply hHess
      intro w
      have h1 := morse_op_half f (a - b) w
      rw [hsub, inner_zero_left] at h1
      linarith
    exact sub_eq_zero.mp h0

private abbrev morseSignMat (k n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i : Fin n => (if (i : ℕ) < k then (-1 : ℝ) else 1)

private abbrev morseSignOp (k n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (morseSignMat k n)

private theorem morse_sign_props (k n : ℕ) :
    star (morseSignOp k n) = morseSignOp k n ∧
    morseSignOp k n * morseSignOp k n = 1 ∧
    ∀ z : EuclideanSpace ℝ (Fin n),
      ⟪morseSignOp k n z, z⟫ = morseQuadratic k n z := by
  refine ⟨?_, ?_, ?_⟩
  · have hM : star (morseSignMat k n) = morseSignMat k n := by
      rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      ext i j
      simp only [morseSignMat, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        by_cases hk : ((i : ℕ) < k) <;> simp [hk]
      · simp [hij]
    change star ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (morseSignMat k n)) = _
    rw [← map_star, hM]
  · have hsq : morseSignMat k n * morseSignMat k n = 1 := by
      have hdd : (fun i : Fin n => (if (i : ℕ) < k then (-1 : ℝ) else 1) *
          (if (i : ℕ) < k then (-1 : ℝ) else 1)) = 1 := by
        funext i
        by_cases hk : ((i : ℕ) < k) <;> simp [hk]
      rw [morseSignMat, Matrix.diagonal_mul_diagonal, hdd]
      exact Matrix.diagonal_one
    change (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (morseSignMat k n) *
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (morseSignMat k n) = _
    rw [← map_mul, hsq, map_one]
  · intro z
    rw [real_inner_comm]
    change ⟪z, (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))
      (morseSignMat k n) z⟫ = _
    rw [Matrix.inner_toEuclideanCLM]
    rw [morseSignMat]
    unfold morseQuadratic dotProduct
    simp only [Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- A nondegenerate self-adjoint operator is congruent to a sign operator. -/
private theorem morse_exists_diagonalizing {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hself : star A = A) (hinj : Function.Injective A) :
    ∃ (k : ℕ) (_ : k ≤ n) (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n)),
      ∀ v w, ⟪A v, w⟫ = ⟪morseSignOp k n (L v), L w⟫ := by
  classical
  have hsa : IsSelfAdjoint A := hself
  have hsym : (↑A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n)).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
    finrank_euclideanSpace_fin
  have happly : ∀ i : Fin n, (↑A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n)) ((hsym.eigenvectorBasis hn) i)
      = (hsym.eigenvalues hn i) • (hsym.eigenvectorBasis hn) i :=
    fun i => hsym.apply_eigenvectorBasis hn i
  have hspec : ∃ (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
      (lam : Fin n → ℝ),
      (∀ i, A (b i) = lam i • b i) ∧
      (∀ x, x = ∑ i, ⟪b i, x⟫ • b i) ∧
      (∀ i j, ⟪b i, b j⟫ = (if i = j then (1 : ℝ) else 0)) ∧
      ∀ m, lam m ≠ 0 := by
    refine ⟨hsym.eigenvectorBasis hn, hsym.eigenvalues hn, ?_, ?_, ?_, ?_⟩
    · intro i
      exact happly i
    · intro x
      have h := (hsym.eigenvectorBasis hn).sum_repr x
      have hr : ∀ i : Fin n, (((hsym.eigenvectorBasis hn).repr x).ofLp i)
          = ⟪(hsym.eigenvectorBasis hn) i, x⟫ :=
        fun i => (hsym.eigenvectorBasis hn).repr_apply_apply x i
      calc x = ∑ i, ((((hsym.eigenvectorBasis hn).repr x).ofLp i))
          • (hsym.eigenvectorBasis hn) i := h.symm
        _ = ∑ i, ⟪(hsym.eigenvectorBasis hn) i, x⟫
            • (hsym.eigenvectorBasis hn) i :=
            Finset.sum_congr rfl fun i _ => by rw [hr i]
    · intro i j
      exact (orthonormal_iff_ite.mp (hsym.eigenvectorBasis hn).orthonormal) i j
    · intro m hm
      have hA0 : (↑A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin n)) ((hsym.eigenvectorBasis hn) m) = 0 := by
        rw [happly m, hm, zero_smul]
      have h0 : A ((hsym.eigenvectorBasis hn) m) = 0 := hA0
      have hbm : (hsym.eigenvectorBasis hn) m = 0 := hinj (by rw [h0, map_zero])
      exact (hsym.eigenvectorBasis hn).orthonormal.ne_zero m hbm
  obtain ⟨b, lam, hAb, hexpand, hborth, hne⟩ := hspec
  obtain ⟨p, k, hkcard, hpmem⟩ := perm_initial_segment
    (Finset.univ.filter (fun m : Fin n => lam m < 0))
  have hk : k ≤ n := by
    rw [← hkcard]
    simpa using Finset.card_le_univ
      (Finset.univ.filter (fun m : Fin n => lam m < 0))
  have hSiff : ∀ m : Fin n, m ∈ Finset.univ.filter (fun m : Fin n => lam m < 0)
      ↔ lam m < 0 := by
    intro m
    rw [Finset.mem_filter]
    simp
  have hspos : ∀ i : Fin n, 0 < Real.sqrt |lam (p i)| := by
    intro i
    rw [Real.sqrt_pos]
    exact abs_pos.mpr (hne (p i))
  have hsign : ∀ i : Fin n, (if (i : ℕ) < k then (-1 : ℝ) else 1)
      * (Real.sqrt |lam (p i)| * Real.sqrt |lam (p i)|) = lam (p i) := by
    intro i
    have hsq : Real.sqrt |lam (p i)| * Real.sqrt |lam (p i)| = |lam (p i)| := by
      rw [← pow_two]
      exact Real.sq_sqrt (abs_nonneg _)
    rw [hsq]
    by_cases hneg : lam (p i) < 0
    · have hmem := (hSiff (p i)).mpr hneg
      have hlt : (i : ℕ) < k := (hpmem i).mp hmem
      simp only [hlt, ite_true, abs_of_neg hneg]
      ring
    · have hle : 0 ≤ lam (p i) := not_lt.mp hneg
      have hpos : 0 < lam (p i) :=
        lt_of_le_of_ne hle (fun h => hne (p i) h.symm)
      have hnpos : ¬ (i : ℕ) < k := by
        intro hlt
        have hmem := (hpmem i).mpr hlt
        have hlt' := (hSiff (p i)).mp hmem
        linarith
      simp only [hnpos, ite_false, abs_of_pos hpos, one_mul]
  have hinner_expand : ∀ (c d : Fin n → ℝ),
      ⟪∑ i, (c i) • b i, ∑ j, (d j) • b j⟫ = ∑ i, c i * d i := by
    intro c d
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    have e : ∀ j : Fin n, ⟪(c i) • b i, (d j) • b j⟫
        = (if i = j then c i * d j else 0) := by
      intro j
      rw [inner_smul_left, inner_smul_right, hborth i j]
      simp only [starRingEnd_apply, star_trivial]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    simp only [e]
    exact Fintype.sum_ite_eq i (fun j => c i * d j)
  have hA_expand : ∀ v w : EuclideanSpace ℝ (Fin n),
      ⟪A v, w⟫ = ∑ m, lam m * ⟪b m, v⟫ * ⟪b m, w⟫ := by
    intro v w
    have eAv : A v = ∑ m, (lam m * ⟪b m, v⟫) • b m := by
      conv_lhs => rw [hexpand v]
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_smul, hAb m, mul_smul, smul_comm]
    rw [eAv]
    conv_lhs => rw [hexpand w]
    exact hinner_expand (fun m => lam m * ⟪b m, v⟫) (fun i => ⟪b i, w⟫)
  have heVec_apply : ∀ (i j : Fin n),
      (eVec j) i = (if j = i then (1 : ℝ) else 0) := by
    intro i j
    have h : (eVec j).ofLp i = (if j = i then (1 : ℝ) else 0) := by
      change ((PiLp.single 2 j (1 : ℝ) : EuclideanSpace ℝ (Fin n))).ofLp i = _
      by_cases hij : j = i
      · simp only [hij, ite_true, PiLp.single_eq_same]
      · simp only [hij, ite_false]
        exact PiLp.single_eq_of_ne (β := fun _ => ℝ) 2 (Ne.symm hij) (1 : ℝ)
    simpa using h
  have hLcoord : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      (∑ j, (Real.sqrt |lam (p j)| * ⟪b (p j), x⟫) • eVec j) i
        = Real.sqrt |lam (p i)| * ⟪b (p i), x⟫ := by
    intro x i
    change coordProj i
        (∑ j, (Real.sqrt |lam (p j)| * ⟪b (p j), x⟫) • eVec j) = _
    rw [map_sum]
    simp only [map_smul, proj_apply_eq, heVec_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    exact Fintype.sum_ite_eq' i
      (fun j => Real.sqrt |lam (p j)| * ⟪b (p j), x⟫)
  have hexpand_p : ∀ x : EuclideanSpace ℝ (Fin n),
      x = ∑ i, ⟪b (p i), x⟫ • b (p i) := by
    intro x
    calc x = ∑ m, ⟪b m, x⟫ • b m := hexpand x
      _ = ∑ i, ⟪b (p i), x⟫ • b (p i) :=
          (Equiv.sum_comp p (fun m => ⟪b m, x⟫ • b m)).symm
  have hcomp1 : ∀ y : EuclideanSpace ℝ (Fin n),
      (∑ i, (Real.sqrt |lam (p i)| * ⟪b (p i),
        ∑ j, ((Real.sqrt |lam (p j)|)⁻¹ * y j) • b (p j)⟫) • eVec i) = y := by
    intro y
    have estep : ∀ i : Fin n, (Real.sqrt |lam (p i)| * ⟪b (p i),
        ∑ j, ((Real.sqrt |lam (p j)|)⁻¹ * y j) • b (p j)⟫) = y i := by
      intro i
      have e1 : ⟪b (p i), ∑ j, ((Real.sqrt |lam (p j)|)⁻¹ * y j) • b (p j)⟫
          = ∑ j, (if i = j then ((Real.sqrt |lam (p j)|)⁻¹ * y j) else 0) := by
        rw [inner_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [inner_smul_right, hborth (p i) (p j)]
        simp only [p.injective.eq_iff, mul_ite, mul_one, mul_zero]
      rw [e1]
      have hcol : (∑ j, (if i = j then
          ((Real.sqrt |lam (p j)|)⁻¹ * y j) else 0))
          = (Real.sqrt |lam (p i)|)⁻¹ * y i :=
        Fintype.sum_ite_eq i (fun j => (Real.sqrt |lam (p j)|)⁻¹ * y j)
      rw [hcol, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hspos i)), one_mul]
    calc (∑ i, (Real.sqrt |lam (p i)| * ⟪b (p i),
          ∑ j, ((Real.sqrt |lam (p j)|)⁻¹ * y j) • b (p j)⟫) • eVec i)
        = ∑ i, (y i) • eVec i :=
          Finset.sum_congr rfl fun i _ => by rw [estep i]
      _ = y := (coord_expansion y).symm
  have hcomp2 : ∀ x : EuclideanSpace ℝ (Fin n),
      (∑ i, ((Real.sqrt |lam (p i)|)⁻¹ *
        ((∑ j, (Real.sqrt |lam (p j)| * ⟪b (p j), x⟫) • eVec j) i)) • b (p i))
        = x := by
    intro x
    have estep : ∀ i : Fin n, ((Real.sqrt |lam (p i)|)⁻¹ *
        ((∑ j, (Real.sqrt |lam (p j)| * ⟪b (p j), x⟫) • eVec j) i))
        = ⟪b (p i), x⟫ := by
      intro i
      rw [hLcoord x i, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hspos i)),
        one_mul]
    calc (∑ i, ((Real.sqrt |lam (p i)|)⁻¹ *
          ((∑ j, (Real.sqrt |lam (p j)| * ⟪b (p j), x⟫) • eVec j) i)) • b (p i))
        = ∑ i, ⟪b (p i), x⟫ • b (p i) :=
          Finset.sum_congr rfl fun i _ => by rw [estep i]
      _ = x := (hexpand_p x).symm
  have hLadd : ∀ (x y : EuclideanSpace ℝ (Fin n)),
      (∑ i, (Real.sqrt |lam (p i)| * ⟪b (p i), x + y⟫) • eVec i)
        = (∑ i, (Real.sqrt |lam (p i)| * ⟪b (p i), x⟫) • eVec i)
          + (∑ i, (Real.sqrt |lam (p i)| * ⟪b (p i), y⟫) • eVec i) := by
    intro x y
    have e : ∀ i : Fin n, (Real.sqrt |lam (p i)| * ⟪b (p i), x + y⟫) • eVec i
        = (Real.sqrt |lam (p i)| * ⟪b (p i), x⟫) • eVec i
          + (Real.sqrt |lam (p i)| * ⟪b (p i), y⟫) • eVec i := by
      intro i
      rw [inner_add_right, mul_add, add_smul]
    calc (∑ i, (Real.sqrt |lam (p i)| * ⟪b (p i), x + y⟫) • eVec i)
        = ∑ i, ((Real.sqrt |lam (p i)| * ⟪b (p i), x⟫) • eVec i
          + (Real.sqrt |lam (p i)| * ⟪b (p i), y⟫) • eVec i) :=
          Finset.sum_congr rfl fun i _ => e i
      _ = (∑ i, (Real.sqrt |lam (p i)| * ⟪b (p i), x⟫) • eVec i)
          + (∑ i, (Real.sqrt |lam (p i)| * ⟪b (p i), y⟫) • eVec i) :=
          Finset.sum_add_distrib
  have hLsmul : ∀ (c : ℝ) (x : EuclideanSpace ℝ (Fin n)),
      (∑ i, (Real.sqrt |lam (p i)| * ⟪b (p i), c • x⟫) • eVec i)
        = c • (∑ i, (Real.sqrt |lam (p i)| * ⟪b (p i), x⟫) • eVec i) := by
    intro c x
    have e : ∀ i : Fin n, (Real.sqrt |lam (p i)| * ⟪b (p i), c • x⟫) • eVec i
        = c • ((Real.sqrt |lam (p i)| * ⟪b (p i), x⟫) • eVec i) := by
      intro i
      rw [inner_smul_right]
      simp only [mul_smul]
      exact smul_comm _ _ _
    calc (∑ i, (Real.sqrt |lam (p i)| * ⟪b (p i), c • x⟫) • eVec i)
        = ∑ i, c • ((Real.sqrt |lam (p i)| * ⟪b (p i), x⟫) • eVec i) :=
          Finset.sum_congr rfl fun i _ => e i
      _ = c • (∑ i, (Real.sqrt |lam (p i)| * ⟪b (p i), x⟫) • eVec i) :=
          (Finset.smul_sum).symm
  have hsign_inner : ∀ (x y : EuclideanSpace ℝ (Fin n)),
      ⟪morseSignOp k n x, y⟫
        = ∑ i : Fin n, (if (i : ℕ) < k then (-1 : ℝ) else 1) * (x i) * (y i) := by
    intro x y
    rw [real_inner_comm]
    change ⟪y, (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))
      (morseSignMat k n) x⟫ = _
    rw [Matrix.inner_toEuclideanCLM, morseSignMat]
    unfold dotProduct
    simp only [Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hre : ∀ (v w : EuclideanSpace ℝ (Fin n)),
      (∑ m, lam m * ⟪b m, v⟫ * ⟪b m, w⟫)
        = ∑ i, lam (p i) * ⟪b (p i), v⟫ * ⟪b (p i), w⟫ := by
    intro v w
    exact (Equiv.sum_comp p (fun m => lam m * ⟪b m, v⟫ * ⟪b m, w⟫)).symm
  let hLin : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) :=
    { toFun := fun x => ∑ i,
        (Real.sqrt |lam (p i)| * ⟪b (p i), x⟫) • eVec i,
      invFun := fun y => ∑ i, ((Real.sqrt |lam (p i)|)⁻¹ * y i) • b (p i),
      left_inv := fun x => hcomp2 x,
      right_inv := fun y => hcomp1 y,
      map_add' := fun x y => hLadd x y,
      map_smul' := fun c x => hLsmul c x }
  obtain ⟨L, hL⟩ : ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n),
      ∀ x, ⇑L x
        = ∑ i, (Real.sqrt |lam (p i)| * ⟪b (p i), x⟫) • eVec i :=
    ⟨hLin.toContinuousLinearEquiv, fun x => rfl⟩
  refine ⟨k, hk, L, ?_⟩
  intro v w
  rw [hA_expand v w, hsign_inner, hL v, hL w]
  simp only [hLcoord]
  rw [hre v w]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsg := hsign i
  conv_lhs => rw [← hsg]
  by_cases hik : (i : ℕ) < k
  · simp only [hik, ite_true]
    ring
  · simp only [hik, ite_false]
    ring

/-- The inverse function theorem as a smooth partial homeomorphism: around a
point with invertible derivative, `g` coincides with a partial homeomorphism
whose inverse is smooth on its whole target. -/
private theorem morse_ift_homeomorph {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [CompleteSpace F₁]
    {g : F₁ → F₂} {U : Set F₁} {a : F₁} {g' : F₁ ≃L[ℝ] F₂}
    (hU : IsOpen U) (ha : a ∈ U) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hderiv : HasFDerivAt g (g' : F₁ →L[ℝ] F₂) a) :
    ∃ h : OpenPartialHomeomorph F₁ F₂, a ∈ h.source ∧ h.source ⊆ U ∧
      ⇑h = g ∧ ContDiffOn ℝ (⊤ : ℕ∞) g h.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) h.symm h.target := by
  have hga : ContDiffAt ℝ (⊤ : ℕ∞) g a :=
    contDiffAt_of_contDiffOn_of_mem_open hU hg ha
  have hcont : ContinuousOn (fderiv ℝ g) U :=
    hg.continuousOn_fderiv_of_isOpen hU (by simp)
  have ha_range : fderiv ℝ g a
      ∈ Set.range ContinuousLinearEquiv.toContinuousLinearMap :=
    ⟨g', hderiv.fderiv.symm⟩
  have hWopen : IsOpen {x ∈ U |
      fderiv ℝ g x ∈ Set.range ContinuousLinearEquiv.toContinuousLinearMap} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨hxU, hxr⟩ := hx
    have hcat : ContinuousAt (fderiv ℝ g) x :=
      hcont.continuousAt (hU.mem_nhds hxU)
    have hmem : (fderiv ℝ g) ⁻¹'
        (Set.range ContinuousLinearEquiv.toContinuousLinearMap) ∈ 𝓝 x :=
      hcat.preimage_mem_nhds (ContinuousLinearEquiv.isOpen.mem_nhds hxr)
    have hinter := Filter.inter_mem (hU.mem_nhds hxU) hmem
    refine mem_of_superset hinter ?_
    rintro y ⟨hyU, hyP⟩
    exact ⟨hyU, hyP⟩
  have haW : a ∈ {x ∈ U |
      fderiv ℝ g x ∈ Set.range ContinuousLinearEquiv.toContinuousLinearMap} :=
    ⟨ha, ha_range⟩
  set h0 := hga.toOpenPartialHomeomorph g hderiv top_order_ne_zero with hh0def
  have hcoe : ⇑h0 = g :=
    ContDiffAt.toOpenPartialHomeomorph_coe hga hderiv top_order_ne_zero
  have hmem : a ∈ h0.source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source hga hderiv top_order_ne_zero
  set h := h0.restrOpen _ hWopen with hhdef
  have hcoeh : ⇑h = g := by
    rw [hhdef, OpenPartialHomeomorph.coe_restrOpen]
    exact hcoe
  have hsource : h.source = h0.source ∩ {x ∈ U |
      fderiv ℝ g x ∈ Set.range ContinuousLinearEquiv.toContinuousLinearMap} := by
    rw [hhdef]
    exact OpenPartialHomeomorph.restrOpen_source h0 _ hWopen
  refine ⟨h, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsource]
    exact ⟨hmem, haW⟩
  · intro x hx
    rw [hsource] at hx
    exact hx.2.1
  · exact hcoeh
  · apply hg.mono
    intro x hx
    rw [hsource] at hx
    exact hx.2.1
  · apply contDiffOn_of_contDiffAt
    intro y hy
    have hxy : ⇑h.symm y ∈ h0.source ∩ {x ∈ U |
        fderiv ℝ g x ∈ Set.range ContinuousLinearEquiv.toContinuousLinearMap} := by
      have hbase : ⇑h.symm y ∈ h.source := h.map_target hy
      rwa [hsource] at hbase
    obtain ⟨-, hxU, hxrange⟩ := hxy
    obtain ⟨e, he⟩ := hxrange
    have hAt : ContDiffAt ℝ (⊤ : ℕ∞) g (⇑h.symm y) :=
      contDiffAt_of_contDiffOn_of_mem_open hU hg hxU
    have hdiff : DifferentiableAt ℝ g (⇑h.symm y) :=
      hAt.differentiableAt top_order_ne_zero
    have hfx : fderiv ℝ g (⇑h.symm y) = (e : F₁ →L[ℝ] F₂) := he.symm
    have hHas : HasFDerivAt g (e : F₁ →L[ℝ] F₂) (⇑h.symm y) := by
      have hbase := hdiff.hasFDerivAt
      rwa [hfx] at hbase
    have hHas' : HasFDerivAt ⇑h (e : F₁ →L[ℝ] F₂) (⇑h.symm y) := by
      rw [hcoeh]
      exact hHas
    have hAt' : ContDiffAt ℝ (⊤ : ℕ∞) ⇑h (⇑h.symm y) := by
      rw [hcoeh]
      exact hAt
    exact OpenPartialHomeomorph.contDiffAt_symm h hy hHas' hAt'

/-- An invertible derivative gives a smooth local diffeomorphism: the missing
bridge from `HasFDerivAt` with a linear equivalence to `IsLocalDiffeomorphAt`. -/
private theorem morse_isLocalDiffeomorphAt {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} {a : EuclideanSpace ℝ (Fin n)}
    {g' : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hU : IsOpen U) (ha : a ∈ U) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hderiv : HasFDerivAt g (g' : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) a) :
    IsLocalDiffeomorphAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) g a := by
  obtain ⟨h, hamem, -, hEq, hgS, hsymmS⟩ :=
    morse_ift_homeomorph hU ha hg hderiv
  have hmd : ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) h h.source := by
    rw [contMDiffOn_iff_contDiffOn]
    exact ContDiffOn.congr hgS (fun x _ => congrFun hEq x)
  have hmds : ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) h.symm h.target := by
    rw [contMDiffOn_iff_contDiffOn]
    exact hsymmS
  set Φ : PartialDiffeomorph (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) (⊤ : ℕ∞) :=
      PartialDiffeomorph.mk h.toPartialEquiv h.open_source h.open_target
        hmd hmds with hΦdef
  have hfun : ⇑Φ.toPartialEquiv = g := hEq
  have hmemΦ : a ∈ Φ.source := hamem
  have base := PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Φ hmemΦ
  rw [hfun] at base
  exact base

set_option synthInstance.maxHeartbeats 100000 in
-- Raising the synthesis heartbeat budget: the algebra-scalar instance
-- for the derivative of squaring needs a deeper search than the default
-- budget allows (verified to succeed at 50000).
/-- Smooth square root near the identity in the endomorphism algebra, with a
uniqueness set and equivariance under adjoints and fixed symmetries. -/
private theorem morse_sqrt_near_one {n : ℕ} :
    ∃ (V : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      (R : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))),
      IsOpen V ∧
      (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∈ V ∧
      ContDiffOn ℝ (⊤ : ℕ∞) R V ∧ R 1 = 1 ∧
      (∀ X ∈ V, R X * R X = X) ∧
      (∃ S : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
        IsOpen S ∧
        (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∈ S ∧
        R '' V ⊆ S ∧
        ∀ X ∈ V, ∀ Y ∈ S, Y * Y = X → Y = R X) ∧
      ∀ J : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        star J = J → J * J = 1 →
        ∀ᶠ X in 𝓝 (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)),
          X ∈ V ∧ R (star X) = star (R X) ∧
            R (J * X * J) = J * R X * J := by
  have hcomp : CompleteSpace
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    FiniteDimensional.complete ℝ _
  have hq_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun X : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) => X * X) :=
    contDiff_mul.comp (contDiff_id.prodMk contDiff_id)
  set e : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    (LinearEquiv.smulOfNeZero ℝ _ 2 two_ne_zero).toContinuousLinearEquiv with hedef
  have h2id : (id (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) •
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) +
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) <•
        id (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)))
      = (2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) := by
    ext Y
    simp
    ring
  have heq : ((e : (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))) =
      (2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) := by
    simp only [hedef]
    ext Y
    simp [LinearEquiv.smulOfNeZero_apply]
  have hderiv : HasFDerivAt
      (fun X : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) => X * X)
      ((e : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))) 1 := by
    have hbase := HasFDerivAt.mul'
      (hasFDerivAt_id (𝕜 := ℝ) (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)))
      (hasFDerivAt_id (𝕜 := ℝ) (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)))
    have hD : (id (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) •
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n)) +
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n)) <•
          id (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n)))
        = (((e : (EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) →L[ℝ]
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))))) :=
      h2id.trans heq.symm
    have htest : HasFDerivAt (fun X : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) => X * X)
        (id (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) •
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n)) +
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n)) <•
          id (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n))) 1 := hbase
    rw [hD] at htest
    exact htest
  obtain ⟨h, hamem, -, hcoeh, _hgS, hsymmS⟩ :=
    morse_ift_homeomorph isOpen_univ (Set.mem_univ 1) hq_smooth.contDiffOn
      hderiv
  have h11 : (h 1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) = 1 := by simp [hcoeh]
  have hmem1 : (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) ∈ h.target := by
    have hbase := h.map_source hamem
    rwa [h11] at hbase
  have hR1 : (h.symm 1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) = 1 := by
    have hbase := h.left_inv hamem
    rwa [h11] at hbase
  have hsq : ∀ X ∈ h.target,
      (h.symm X : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) *
      (h.symm X : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) = X := by
    intro X hX
    have hbase := h.right_inv hX
    have hqX : (h (h.symm X) : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) =
        (h.symm X : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) *
        (h.symm X : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) := congrFun hcoeh _
    rw [hqX] at hbase
    exact hbase
  refine ⟨h.target, h.symm, h.open_target, hmem1, hsymmS, hR1, hsq, ?_, ?_⟩
  · refine ⟨h.source, h.open_source, hamem, ?_, ?_⟩
    · intro Y hY
      obtain ⟨X, hX, rfl⟩ := hY
      exact h.map_target hX
    · intro X hX Y hY hYY
      have hqY : (h Y : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) = Y * Y := by simp [hcoeh]
      have hYX : (h Y : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) = X := by
        rw [hqY]
        exact hYY
      have hbase := h.left_inv hY
      rw [hYX] at hbase
      exact hbase.symm
  · intro J _ hJJ
    have hunique : ∀ X ∈ h.target, ∀ Y ∈ h.source, Y * Y = X → Y = h.symm X := by
      intro X hX Y hY hYY
      have hqY : (h Y : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) = Y * Y := by simp [hcoeh]
      have hYX : (h Y : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) = X := by rw [hqY]; exact hYY
      have hbase := h.left_inv hY
      rw [hYX] at hbase
      exact hbase.symm
    have hstar_cont : Continuous (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) => star A) := by
      have h2 : (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) => star A) =
          ⇑(ContinuousLinearMap.adjoint :
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≃ₗᵢ⋆[ℝ]
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) := by
        funext A
        exact ContinuousLinearMap.star_eq_adjoint A
      rw [h2]
      exact LinearIsometryEquiv.continuous _
    have hR_cont : ContinuousAt ⇑h.symm (1 :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
      h.continuousOn_symm.continuousAt (h.open_target.mem_nhds hmem1)
    have hJ1 : J * (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) * J = 1 := by rw [mul_one, hJJ]
    have eV : ∀ᶠ X in 𝓝 (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)), X ∈ h.target :=
      h.open_target.mem_nhds hmem1
    have eSV : ∀ᶠ X in 𝓝 (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)), star X ∈ h.target :=
      hstar_cont.continuousAt.preimage_mem_nhds (by
        show h.target ∈ 𝓝 (star (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)))
        rw [star_one]
        exact eV)
    have hstarS : (star ⁻¹' h.source) ∈ 𝓝 (1 :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
      apply hstar_cont.continuousAt.preimage_mem_nhds
      rw [star_one]
      exact h.open_source.mem_nhds hamem
    have eSS : ∀ᶠ X in 𝓝 (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)), star (h.symm X) ∈ h.source := by
      have hmem : (star ⁻¹' h.source) ∈ 𝓝 (h.symm (1 :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) := by
        rwa [hR1]
      exact hR_cont.preimage_mem_nhds hmem
    have hJ_cont : Continuous (fun X : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) => J * X * J) :=
      (continuous_const.mul continuous_id).mul continuous_const
    have eJV : ∀ᶠ X in 𝓝 (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)), J * X * J ∈ h.target := by
      apply hJ_cont.continuousAt.preimage_mem_nhds
      show h.target ∈ 𝓝 (J * (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) * J)
      rwa [hJ1]
    have hKJpre : ((fun Y : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) => J * Y * J) ⁻¹' h.source) ∈ 𝓝 (1 :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
      apply hJ_cont.continuousAt.preimage_mem_nhds
      show h.source ∈ 𝓝 (J * (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) * J)
      rw [hJ1]
      exact h.open_source.mem_nhds hamem
    have eJS : ∀ᶠ X in 𝓝 (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)), J * h.symm X * J ∈ h.source := by
      have hmem : ((fun Y : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) => J * Y * J) ⁻¹' h.source) ∈
          𝓝 (h.symm (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n))) := by
        rwa [hR1]
      exact hR_cont.preimage_mem_nhds hmem
    filter_upwards [eV, eSV, eSS, eJV, eJS] with X hXV hstarV hstarS_mem hJXV hJS_mem
    refine ⟨hXV, ?_, ?_⟩
    · have hY1 : star (h.symm X) * star (h.symm X) = star X := by
        rw [← star_mul, hsq X hXV]
      exact (hunique (star X) hstarV (star (h.symm X)) hstarS_mem hY1).symm
    · have hsqX : h.symm X * h.symm X = X := hsq X hXV
      have hY2 : (J * h.symm X * J) * (J * h.symm X * J) = J * X * J := by
        calc (J * h.symm X * J) * (J * h.symm X * J)
            = J * (h.symm X * ((J * J) * h.symm X)) * J := by
              simp only [mul_assoc]
          _ = J * (h.symm X * h.symm X) * J := by rw [hJJ, one_mul]
          _ = J * X * J := by rw [hsqX]
      exact (hunique (J * X * J) hJXV (J * h.symm X * J) hJS_mem hY2).symm

set_option maxHeartbeats 800000 in
-- Elaborator budget: the normal-form construction layers several
-- operator-valued rewrites that exceed the default heartbeat budget.
/-- Normal form near zero: conjugating the operator field by the square root
gives coordinates in which the remainder is exactly quadratic. -/
private theorem morse_normal_form_near_zero {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {𝓑 : EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))}
    (h𝓑smooth : ContDiff ℝ (⊤ : ℕ∞) 𝓑)
    (h𝓑self : ∀ x, star (𝓑 x) = 𝓑 x)
    (h𝓑form : ∀ x, f x = f 0 + ⟪𝓑 x x, x⟫)
    {k : ℕ} {L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hdiag : ∀ v w : EuclideanSpace ℝ (Fin n),
      ⟪𝓑 0 v, w⟫ = ⟪morseSignOp k n (L v), L w⟫)
    (V : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (R : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hVopen : IsOpen V)
    (h1V : (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∈ V)
    (hRsmooth : ContDiffOn ℝ (⊤ : ℕ∞) R V)
    (hR1 : R 1 = 1)
    (hsq : ∀ X ∈ V, R X * R X = X)
    (hequiv : ∀ J : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      star J = J → J * J = 1 →
      ∀ᶠ X in 𝓝 (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)),
        X ∈ V ∧ R (star X) = star (R X) ∧
          R (J * X * J) = J * R X * J) :
    ∃ (O : Set (EuclideanSpace ℝ (Fin n)))
      (ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      IsOpen O ∧ (0 : EuclideanSpace ℝ (Fin n)) ∈ O ∧
      ContDiffOn ℝ (⊤ : ℕ∞) ψ O ∧ ψ 0 = 0 ∧
      HasFDerivAt ψ (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) 0 ∧
      ∀ y ∈ O, f (L.symm y)
        = f 0 + ⟪morseSignOp k n (ψ y), ψ y⟫ := by
  obtain ⟨hJstar, hJJ, _⟩ := morse_sign_props k n
  let Linv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := ↑L.symm
  have hLinvapp : ∀ y : EuclideanSpace ℝ (Fin n), Linv y = L.symm y :=
    fun y => rfl
  have hLLinv : ∀ u : EuclideanSpace ℝ (Fin n), L (Linv u) = u :=
    fun u => L.apply_symm_apply u
  have hCinner : ∀ (y u w : EuclideanSpace ℝ (Fin n)),
      ⟪(star Linv * 𝓑 (Linv y) * Linv) u, w⟫
        = ⟪𝓑 (Linv y) (Linv u), Linv w⟫ := by
    intro y u w
    change ⟪star Linv (𝓑 (Linv y) (Linv u)), w⟫ = _
    rw [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  have hCself : ∀ y : EuclideanSpace ℝ (Fin n),
      star (star Linv * 𝓑 (Linv y) * Linv)
        = star Linv * 𝓑 (Linv y) * Linv := by
    intro y
    simp only [star_mul, h𝓑self, star_star, mul_assoc]
  have hstarM : ∀ y : EuclideanSpace ℝ (Fin n),
      star (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
        = (star Linv * 𝓑 (Linv y) * Linv) * morseSignOp k n := by
    intro y
    rw [star_mul, hCself y, hJstar]
  have hJMJ : ∀ y : EuclideanSpace ℝ (Fin n),
      morseSignOp k n * (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
        * morseSignOp k n
        = (star Linv * 𝓑 (Linv y) * Linv) * morseSignOp k n := by
    intro y
    calc morseSignOp k n * (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
          * morseSignOp k n
        = ((morseSignOp k n * morseSignOp k n)
            * (star Linv * 𝓑 (Linv y) * Linv)) * morseSignOp k n := by
          simp only [mul_assoc]
      _ = (star Linv * 𝓑 (Linv y) * Linv) * morseSignOp k n := by
          rw [hJJ, one_mul]
  have hC0 : star Linv * 𝓑 (Linv 0) * Linv = morseSignOp k n := by
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right ℝ
    intro w
    rw [hCinner]
    have eL0 : Linv (0 : EuclideanSpace ℝ (Fin n)) = 0 := map_zero Linv
    rw [eL0, hdiag, hLLinv u, hLLinv w]
  have hM0 : morseSignOp k n * (star Linv * 𝓑 (Linv 0) * Linv) = 1 := by
    rw [hC0, hJJ]
  have hM : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin n) =>
      morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) := by
    have hLinvC : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin n) => Linv y) := Linv.contDiff
    have hB : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin n) => 𝓑 (Linv y)) :=
      h𝓑smooth.comp hLinvC
    have hC : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin n) =>
        star Linv * 𝓑 (Linv y) * Linv) :=
      (contDiff_const.mul hB).mul contDiff_const
    exact contDiff_const.mul hC
  have hev := hequiv (morseSignOp k n) hJstar hJJ
  have hOmem : (fun y : EuclideanSpace ℝ (Fin n) =>
      morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) ⁻¹'
      {X | X ∈ V ∧ R (star X) = star (R X)
        ∧ R (morseSignOp k n * X * morseSignOp k n)
          = morseSignOp k n * R X * morseSignOp k n}
      ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)) := by
    apply hM.continuous.continuousAt.preimage_mem_nhds
    rw [hM0]
    exact hev
  obtain ⟨O, hOsub, hOopen, h0O⟩ := mem_nhds_iff.mp hOmem
  have hOmem2 : ∀ y ∈ O,
      morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv) ∈ V
      ∧ R (star (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)))
        = star (R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)))
      ∧ R (morseSignOp k n * (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
          * morseSignOp k n)
        = morseSignOp k n
          * R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
          * morseSignOp k n :=
    fun y hyO => hOsub hyO
  have hPO : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin n) =>
        R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))) O := by
    apply hRsmooth.comp hM.contDiffOn
    intro y hyO
    exact (hOmem2 y hyO).1
  have hψsmooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin n) =>
        R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) y) O :=
    hPO.clm_apply contDiff_id.contDiffOn
  have hψ0 : (fun y : EuclideanSpace ℝ (Fin n) =>
      R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) y)
      (0 : EuclideanSpace ℝ (Fin n)) = 0 :=
    map_zero _
  obtain ⟨P', hPderiv⟩ : ∃ P' : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) =>
        R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))) P' 0 := by
    have hRderiv : HasFDerivAt R (fderiv ℝ R 1) 1 :=
      ((contDiffAt_of_contDiffOn_of_mem_open hVopen hRsmooth h1V).differentiableAt
        top_order_ne_zero).hasFDerivAt
    have hMderiv : HasFDerivAt
        (fun y : EuclideanSpace ℝ (Fin n) =>
          morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
          morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) 0) 0 :=
      (hM.contDiffAt.differentiableAt top_order_ne_zero).hasFDerivAt
    have hRderiv0 : HasFDerivAt R (fderiv ℝ R 1)
        ((fun y : EuclideanSpace ℝ (Fin n) =>
          morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) 0) := by
      change HasFDerivAt R (fderiv ℝ R 1)
        (morseSignOp k n * (star Linv * 𝓑 (Linv 0) * Linv))
      rwa [hM0]
    exact ⟨_, hRderiv0.comp 0 hMderiv⟩
  have eP0 : (fun y : EuclideanSpace ℝ (Fin n) =>
      R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))) 0 = 1 := by
    change R (morseSignOp k n * (star Linv * 𝓑 (Linv 0) * Linv)) = 1
    rw [hM0, hR1]
  have hψderiv : HasFDerivAt
      (fun y : EuclideanSpace ℝ (Fin n) =>
        R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) y)
      (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) 0 := by
    have hclm := HasFDerivAt.clm_apply hPderiv (hasFDerivAt_id (0 : EuclideanSpace ℝ (Fin n)))
    have hD : (fun y : EuclideanSpace ℝ (Fin n) =>
          R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))) 0 ∘SL
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))
        + P'.flip (id (0 : EuclideanSpace ℝ (Fin n))) = 1 := by
      rw [eP0]
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        Function.id_def, map_zero, add_zero]
    rw [hD] at hclm
    exact hclm
  refine ⟨O, (fun y : EuclideanSpace ℝ (Fin n) =>
    R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) y),
    hOopen, h0O, hψsmooth, hψ0, hψderiv, ?_⟩
  intro y hyO
  obtain ⟨hMVy, hstarY, hJconjY⟩ := hOmem2 y hyO
  rw [← hLinvapp y]
  change f (Linv y) = f 0 + ⟪morseSignOp k n
    (R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) y),
    R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) y⟫
  have eSTAR : star (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
      = morseSignOp k n * (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
        * morseSignOp k n := by
    rw [hstarM y, hJMJ y]
  have ePstar : star (R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)))
      = morseSignOp k n * R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
        * morseSignOp k n := by
    rw [← hstarY, ← hJconjY, eSTAR]
  have hPP : R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
        * R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
      = morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv) :=
    hsq _ hMVy
  have hop : star (R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)))
        * morseSignOp k n
        * R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
      = star Linv * 𝓑 (Linv y) * Linv := by
    calc star (R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)))
          * morseSignOp k n
          * R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
        = (morseSignOp k n * R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
            * morseSignOp k n) * morseSignOp k n
            * R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) := by
          rw [ePstar]
      _ = (morseSignOp k n * R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
            * (morseSignOp k n * morseSignOp k n))
          * R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) := by
          simp only [mul_assoc]
      _ = morseSignOp k n
          * (R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))
            * R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))) := by
          rw [hJJ, mul_one, mul_assoc]
      _ = morseSignOp k n * (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) := by
          rw [hPP]
      _ = star Linv * 𝓑 (Linv y) * Linv := by
          rw [← mul_assoc, hJJ, one_mul]
  have key : ⟪morseSignOp k n
        (R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) y),
        R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) y⟫
      = ⟪(star Linv * 𝓑 (Linv y) * Linv) y, y⟫ := by
    conv_rhs => rw [← hop]
    have e : ⟪(star (R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)))
          * morseSignOp k n
          * R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv))) y, y⟫
        = ⟪morseSignOp k n
          (R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) y),
          R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) y⟫ := by
      change ⟪star (R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)))
        (morseSignOp k n (R (morseSignOp k n * (star Linv * 𝓑 (Linv y) * Linv)) y)),
        y⟫ = _
      rw [ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    exact e.symm
  have h2 : ⟪𝓑 (Linv y) (Linv y), Linv y⟫
      = ⟪(star Linv * 𝓑 (Linv y) * Linv) y, y⟫ := (hCinner y y y).symm
  rw [h𝓑form (Linv y), h2, key]

/--
**Morse lemma.** Let $f \colon \mathbb{R}^n \to \mathbb{R}$ be a $C^\infty$ function with
$Df(0) = 0$ whose Hessian at $0$ is nondegenerate: if $v \in \mathbb{R}^n$ satisfies
$D^2 f(0)(v, w) = 0$ for all $w \in \mathbb{R}^n$, then $v = 0$. Then there exist an integer
$0 \le k \le n$, a map $\varphi \colon \mathbb{R}^n \to \mathbb{R}^n$ that is a local $C^\infty$
diffeomorphism at $0$ with $\varphi(0) = 0$, and an open set $U$ containing $0$ such that
$f(x) = f(0) + Q_k(\varphi(x))$ for all $x \in U$. Here $Q_k$ is the Morse quadratic form
$Q_k(y) = -y_1^2 - \dots - y_k^2 + y_{k+1}^2 + \dots + y_n^2$ on $\mathbb{R}^n$.

Proves `Wanted` entry `morse_lemma`.

Source: J. Milnor, Morse Theory,
Ann. of Math. Studies 51 (1963) Lemma 2.2; M. Hirsch, Differential Topology; J. Lee, Intro to
Smooth Manifolds, 2nd ed., Morse lemma; Lean states Euclidean origin finite-dimensional
specialization with corrected nondegeneracy grouping `(∀ w, (fderiv (fderiv f) 0 v) w = 0) → v =
0`.
-/
theorem morse_lemma
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcrit : fderiv ℝ f (0 : EuclideanSpace ℝ (Fin n)) = 0)
    (hHess : ∀ v : EuclideanSpace ℝ (Fin n),
      (∀ w : EuclideanSpace ℝ (Fin n),
        (fderiv ℝ (fderiv ℝ f) (0 : EuclideanSpace ℝ (Fin n)) v) w = 0) → v = 0) :
    ∃ (k : ℕ) (_hk : k ≤ n) (φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      IsLocalDiffeomorphAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) φ (0 : EuclideanSpace ℝ (Fin n)) ∧
      φ (0 : EuclideanSpace ℝ (Fin n)) = 0 ∧
      ∃ (U : Set (EuclideanSpace ℝ (Fin n))) (_hU_open : IsOpen U)
        (_hU_mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ U),
        ∀ x ∈ U, f x = f (0 : EuclideanSpace ℝ (Fin n)) + morseQuadratic k n (φ x) := by
  obtain ⟨𝓑, h𝓑smooth, h𝓑self, h𝓑form, _, h𝓑inj⟩ :=
    morse_operator_form hf hcrit hHess
  obtain ⟨k, hk, L, hdiag⟩ := morse_exists_diagonalizing (𝓑 0) (h𝓑self 0) h𝓑inj
  obtain ⟨V, R, hVopen, h1V, hRsmooth, hR1, hsq, _, hequiv⟩ :=
    morse_sqrt_near_one (n := n)
  obtain ⟨O, ψ, hOopen, h0O, hψsmooth, hψ0, hψderiv, hψform⟩ :=
    morse_normal_form_near_zero h𝓑smooth h𝓑self h𝓑form hdiag V R hVopen h1V
      hRsmooth hR1 hsq hequiv
  obtain ⟨_, _, hJquad⟩ := morse_sign_props k n
  refine ⟨k, hk, fun x => ψ (L x), ?_, ?_,
    (L : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) ⁻¹' O, ?_, ?_, ?_⟩
  · have hφsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ψ (L x))
        ((L : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) ⁻¹' O) :=
      hψsmooth.comp
        ((L : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)).contDiff.contDiffOn)
        (fun x hx => hx)
    have hLderiv : HasFDerivAt
        (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) 0 :=
      (L : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)).hasFDerivAt
    have hψ0 : HasFDerivAt ψ
        (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        ((L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) 0) := by
      rw [map_zero]
      exact hψderiv
    have hφderiv : HasFDerivAt (fun x => ψ (L x))
        ((L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) 0 := by
      have hcomp := hψ0.comp 0 hLderiv
      have heq : (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)).comp
          (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          = (L : EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n)) := by
        rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
      rw [heq] at hcomp
      exact hcomp
    exact morse_isLocalDiffeomorphAt (hOopen.preimage L.continuous)
      (by simpa using h0O) hφsmooth hφderiv
  · simp [hψ0]
  · exact hOopen.preimage L.continuous
  · simpa using h0O
  · intro x hx
    have hLx : L.symm (L x) = x := L.symm_apply_apply x
    have hform := hψform (L x) hx
    rw [hLx, hJquad] at hform
    exact hform

end MathlibExt.Geometry.Manifold.MorseLemmaWanted
end
end
