/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# C² polynomial approximation on compact sets and the simplex

A function that is `C²` on an open neighbourhood of a compact subset of
`ℝⁿ` can be approximated uniformly on that compact set by a multivariate
polynomial together with all first and second partial derivatives. The
simplex form is the case
`Δ_{K-1} = {x ∈ ℝ^{K-1} | xᵢ ≥ 0, ∑ xᵢ ≤ 1}` used for multi-allele
diffusion test functions (`n = K - 1`).

Derivative convention: for `f : (Fin n → ℝ) → ℝ`,
`∂ᵢ f x = fderiv ℝ f x (Pi.single i 1)` and
`∂ᵢ∂ⱼ f x = fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1)`;
on the polynomial side the algebraic partial derivatives
`MvPolynomial.pderiv` are used.

## Main results

* `Diffusion.hasFDerivAt_mvPolynomial_eval`: the derivative of a polynomial
  function is given by algebraic partial derivatives.
* `Diffusion.exists_mvPolynomial_near_contDiffOn_two`: `C²` polynomial
  approximation on a compact set.
* `Diffusion.exists_mvPolynomial_near_contDiffOn_two_simplex`: the simplex
  form.

## References

* A. Pinkus, "Approximation theory of the MLP model in neural networks",
  *Acta Numerica* (1999), 143–195.
-/

@[expose] public section

open MvPolynomial

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- The derivative of a polynomial function is given by the algebraic partial derivatives. -/
theorem hasFDerivAt_mvPolynomial_eval {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (fun y => eval y p)
      (∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)
      x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [pderiv_C, map_zero, zero_smul, Finset.sum_const_zero]
    simp only [eval_C]
    exact hasFDerivAt_const a x
  | add p q hp hq =>
    have hpd : ∀ i : Fin n, pderiv i (p + q) = pderiv i p + pderiv i q := fun i => map_add _ _ _
    simp only [hpd, map_add]
    have hsum : (∑ i, (eval x (pderiv i p) + eval x (pderiv i q)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)
        = (∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)
        + (∑ i, eval x (pderiv i q) •
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact add_smul _ _ _
    rw [hsum]
    exact HasFDerivAt.add hp hq
  | mul_X p k hp =>
    have hX : HasFDerivAt (fun y : Fin n → ℝ => eval y (MvPolynomial.X k : MvPolynomial (Fin n) ℝ))
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k) x := by
      have hfun : (fun y : Fin n → ℝ => eval y (MvPolynomial.X k : MvPolynomial (Fin n) ℝ))
          = ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k) := by
        funext y
        simp [eval_X]
      rw [hfun]
      exact ContinuousLinearMap.hasFDerivAt _
    have hmul := HasFDerivAt.mul hp hX
    simp only [eval_X] at hmul
    have hfun_eq : (fun y => eval y (p * MvPolynomial.X k))
        = (fun y => eval y p) * (fun y : Fin n → ℝ => y k) := by
      funext y
      simp [eval_mul, eval_X, Pi.mul_apply]
    rw [hfun_eq]
    have hpdX : ∀ i : Fin n, eval x (pderiv i (MvPolynomial.X k : MvPolynomial (Fin n) ℝ))
        = if i = k then 1 else 0 := by
      intro i
      by_cases h : i = k
      · subst h
        simp
      · have hk : k ≠ i := Ne.symm h
        simp [pderiv_X_of_ne hk, h]
    have hexpand : ∀ i : Fin n, eval x (pderiv i (p * MvPolynomial.X k))
        = eval x (pderiv i p) * x k + eval x p * (if i = k then 1 else 0) := by
      intro i
      rw [pderiv_mul, map_add, map_mul, map_mul, eval_X, hpdX i]
    have hsum_eq : (∑ i, eval x (pderiv i (p * MvPolynomial.X k)) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)
        = ∑ i, ((eval x (pderiv i p) * x k + eval x p * (if i = k then 1 else 0)) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hexpand i]
    have hderiv : (∑ i, eval x (pderiv i (p * MvPolynomial.X k)) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)
        = eval x p • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k
          + x k • (∑ i, eval x (pderiv i p) •
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) := by
      rw [hsum_eq]
      have hsplit : (∑ i, ((eval x (pderiv i p) * x k + eval x p * (if i = k then 1 else 0)) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i))
          = (∑ i, (eval x (pderiv i p) * x k) •
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)
            + (∑ i, (eval x p * (if i = k then 1 else 0)) •
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        exact add_smul _ _ _
      rw [hsplit]
      have hfirst : (∑ i, (eval x (pderiv i p) * x k) •
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)
          = x k • (∑ i, eval x (pderiv i p) •
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) := by
        have hpoint : ∀ i : Fin n, (eval x (pderiv i p) * x k) •
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i
            = x k • (eval x (pderiv i p) •
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) := by
          intro i
          rw [mul_comm, mul_smul]
        simp only [hpoint]
        exact (Finset.smul_sum).symm
      have hsecond : (∑ i, (eval x p * (if i = k then (1 : ℝ) else 0)) •
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)
          = eval x p • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k := by
        have h0 : ∀ i : Fin n, i ≠ k →
            (eval x p * (if i = k then (1 : ℝ) else 0)) •
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i = 0 := by
          intro i hi
          simp [hi]
        have hk : (eval x p * (if k = k then (1 : ℝ) else 0)) •
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k
            = eval x p • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k := by
          simp
        rw [Finset.sum_eq_single k (fun i _ hi => h0 i hi) (by simp)]
        exact hk
      rw [hfirst, hsecond, add_comm]
    rw [hderiv]
    exact hmul

section

open MeasureTheory Filter Topology
open scoped Convolution

/-- The `i`-th coordinate function as a continuous map. -/
private def coordContinuousMap (n : ℕ) (i : Fin n) : C((Fin n → ℝ), ℝ) :=
  ⟨fun x => x i, continuous_apply i⟩

private theorem aeval_coordContinuousMap_apply {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    (aeval (R := ℝ) (coordContinuousMap n) p) x = eval x p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [_root_.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, coordContinuousMap]

private theorem separatesPoints_range_aeval_coordContinuousMap (n : ℕ) :
    ((aeval (R := ℝ) (coordContinuousMap n)).range).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  refine ⟨_, ⟨coordContinuousMap n i, ⟨X i, by simp⟩, rfl⟩, ?_⟩
  simpa [coordContinuousMap] using hi

/-- A continuous function is uniformly approximated on a compact set by a polynomial. -/
private theorem exists_mvPolynomial_near_continuous {n : ℕ} {φ : (Fin n → ℝ) → ℝ}
    (hφ : Continuous φ) {B : Set (Fin n → ℝ)} (hB : IsCompact B) {η : ℝ} (hη : 0 < η) :
    ∃ Q : MvPolynomial (Fin n) ℝ, ∀ y ∈ B, |eval y Q - φ y| < η := by
  obtain ⟨g, hgA, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (separatesPoints_range_aeval_coordContinuousMap n) ⟨φ, hφ⟩ hB hη
  obtain ⟨Q, rfl⟩ := AlgHom.mem_range _ |>.mp hgA
  refine ⟨Q, fun y hy => ?_⟩
  simpa [aeval_coordContinuousMap_apply, Real.norm_eq_abs] using hg y hy

private theorem integrable_eval_sub_mul {n : ℕ} (Q : MvPolynomial (Fin n) ℝ)
    {h : (Fin n → ℝ) → ℝ} (hc : Continuous h) (hs : HasCompactSupport h) (x : Fin n → ℝ) :
    Integrable (fun t => eval (x - t) Q * h t) :=
  Continuous.integrable_of_hasCompactSupport
    (((continuous_eval Q).comp (continuous_const.sub continuous_id)).mul hc) hs.mul_left

/-- Convolving a compactly supported continuous function with a polynomial gives a polynomial. -/
private theorem exists_eval_eq_integral {n : ℕ} (Q : MvPolynomial (Fin n) ℝ) :
    ∀ h : (Fin n → ℝ) → ℝ, Continuous h → HasCompactSupport h →
      ∃ P : MvPolynomial (Fin n) ℝ, ∀ x, ∫ t, eval (x - t) Q * h t = eval x P := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    intro h _ _
    exact ⟨C (a * ∫ t, h t), fun x => by simp [integral_const_mul]⟩
  | add Q₁ Q₂ ih₁ ih₂ =>
    intro h hc hs
    obtain ⟨P₁, hP₁⟩ := ih₁ h hc hs
    obtain ⟨P₂, hP₂⟩ := ih₂ h hc hs
    refine ⟨P₁ + P₂, fun x => ?_⟩
    simp only [eval_add, add_mul]
    rw [integral_add (integrable_eval_sub_mul Q₁ hc hs x) (integrable_eval_sub_mul Q₂ hc hs x),
      hP₁, hP₂]
  | mul_X Q k ih =>
    intro h hc hs
    have hc' : Continuous fun t : Fin n → ℝ => t k * h t := (continuous_apply k).mul hc
    have hs' : HasCompactSupport fun t : Fin n → ℝ => t k * h t := hs.mul_left
    obtain ⟨P₁, hP₁⟩ := ih h hc hs
    obtain ⟨P₂, hP₂⟩ := ih _ hc' hs'
    refine ⟨X k * P₁ - P₂, fun x => ?_⟩
    have e : ∀ t, eval (x - t) (Q * X k) * h t
        = x k * (eval (x - t) Q * h t) - eval (x - t) Q * (t k * h t) := by
      intro t
      simp only [eval_mul, eval_X, Pi.sub_apply]
      ring
    simp_rw [e]
    rw [integral_sub ((integrable_eval_sub_mul Q hc hs x).const_mul _)
      (integrable_eval_sub_mul Q hc' hs' x), integral_const_mul, hP₁, hP₂]
    simp

/-- If `eval · P` is the convolution of `eval · Q` with a compactly supported `C¹` function `h`,
then `eval · (pderiv j P)` is the convolution of `eval · Q` with `∂ⱼ h`. -/
private theorem eval_pderiv_eq_convolution {n : ℕ} {Q P : MvPolynomial (Fin n) ℝ}
    {h : (Fin n → ℝ) → ℝ} (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h)
    (hP : ∀ x, eval x P = ((fun y => eval y Q) ⋆ h) x) (j : Fin n) (x : Fin n → ℝ) :
    eval x (pderiv j P) = ((fun y => eval y Q) ⋆ fun y => fderiv ℝ h y (Pi.single j 1)) x := by
  have hq : LocallyIntegrable (fun y => eval y Q) volume := (continuous_eval Q).locallyIntegrable
  have h1 := hs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hq hh x
  have hfun : ((fun y => eval y Q) ⋆ h) = fun y => eval y P := funext fun y => (hP y).symm
  rw [hfun] at h1
  have h2 := congrArg (fun L => L (Pi.single j 1)) (h1.unique (hasFDerivAt_mvPolynomial_eval P x))
  rw [convolution_precompR_apply _ hq (hs.fderiv ℝ)
    (hh.continuous_fderiv one_ne_zero)] at h2
  rw [h2]
  simp [Pi.single_apply]

/-- Replacing the kernel `φ` by a kernel `q` that is `η`-close to it on the points `x - t` with
`h t ≠ 0` changes the convolution at `x` by at most `η * ∫ |h|`. -/
private theorem abs_convolution_sub_le {n : ℕ} {q φ h : (Fin n → ℝ) → ℝ} (hq : Continuous q)
    (hφ : Continuous φ) (hc : Continuous h) (hs : HasCompactSupport h) {x : Fin n → ℝ}
    {B : Set (Fin n → ℝ)} {η : ℝ} (hB : ∀ t, h t ≠ 0 → x - t ∈ B)
    (hqφ : ∀ y ∈ B, |q y - φ y| ≤ η) :
    |(q ⋆ h) x - (φ ⋆ h) x| ≤ η * ∫ t, |h t| := by
  have hi : ∀ ψ : (Fin n → ℝ) → ℝ, Continuous ψ → Integrable fun t => ψ (x - t) * h t :=
    fun ψ hψ => Continuous.integrable_of_hasCompactSupport
      ((hψ.comp (continuous_const.sub continuous_id)).mul hc) hs.mul_left
  rw [convolution_eq_swap, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub (hi q hq) (hi φ hφ), ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le
    ((hc.integrable_of_hasCompactSupport hs).abs.const_mul η) (Eventually.of_forall fun t => ?_)
  rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases ht : h t = 0
  · simp [ht]
  · exact mul_le_mul_of_nonneg_right (hqφ _ (hB t ht)) (abs_nonneg _)

/-- One polynomial kernel approximates finitely many compactly supported continuous functions
uniformly on a compact set: mollify with a normed bump function, then replace the bump function by
a polynomial that is uniformly close to it on a large compact set. -/
private theorem exists_mvPolynomial_convolution_near {n : ℕ} {ι : Type*} [Finite ι]
    (h : ι → (Fin n → ℝ) → ℝ) (hc : ∀ i, Continuous (h i)) (hs : ∀ i, HasCompactSupport (h i))
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : MvPolynomial (Fin n) ℝ, ∀ i, ∀ x ∈ K, |((fun y => eval y Q) ⋆ h i) x - h i x| ≤ ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  have hδ_ev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, ∀ x y, dist x y < δ → dist (h i x) (h i y) ≤ ε / 2 := by
    rw [eventually_all]
    intro i
    obtain ⟨δ₀, hδ₀, H⟩ := Metric.uniformContinuous_iff.mp
      ((hs i).uniformContinuous_of_continuous (hc i)) (ε / 2) hε2
    filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ x y hxy
    exact (H (hxy.trans hδ.2)).le
  obtain ⟨δ, hδ, hδ0 : 0 < δ⟩ := (hδ_ev.and self_mem_nhdsWithin).exists
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨δ / 2, δ, half_pos hδ0, half_lt_self hδ0⟩
  have hφ : ∀ i x, |((b.normed volume) ⋆ h i) x - h i x| ≤ ε / 2 := by
    intro i x
    rw [← Real.dist_eq]
    exact dist_convolution_le (R := δ) hε2.le b.support_normed_eq.subset b.nonneg_normed
      b.integral_normed (hc i).aestronglyMeasurable fun y hy => hδ i y x hy
  have hB : IsCompact
      ((fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 - p.2) '' (K ×ˢ ⋃ i, tsupport (h i))) :=
    (hK.prod (isCompact_iUnion hs)).image (continuous_fst.sub continuous_snd)
  have hη_ev : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i, η * ∫ t, |h i t| < ε / 2 := by
    rw [eventually_all]
    intro i
    have ht : Tendsto (fun η : ℝ => η * ∫ t, |h i t|) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (∫ t, |h i t|)
    exact nhdsWithin_le_nhds (ht.eventually (eventually_lt_nhds hε2))
  obtain ⟨η, hη, hη0 : 0 < η⟩ := (hη_ev.and self_mem_nhdsWithin).exists
  obtain ⟨Q, hQ⟩ := exists_mvPolynomial_near_continuous (b.continuous_normed (μ := volume)) hB hη0
  refine ⟨Q, fun i x hx => ?_⟩
  have h1 := abs_convolution_sub_le (continuous_eval Q) b.continuous_normed (hc i) (hs i)
    (B := (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 - p.2) '' (K ×ˢ ⋃ i, tsupport (h i)))
    (fun t ht => ⟨(x, t), ⟨hx, Set.mem_iUnion.2 ⟨i, subset_tsupport _ ht⟩⟩, rfl⟩)
    (fun y hy => (hQ y hy).le)
  calc |((fun y => eval y Q) ⋆ h i) x - h i x|
      ≤ |((fun y => eval y Q) ⋆ h i) x - ((b.normed volume) ⋆ h i) x|
        + |((b.normed volume) ⋆ h i) x - h i x| := abs_sub_le _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (h1.trans (hη i).le) (hφ i x)
    _ = ε := add_halves ε

/-- The compact-set theorem for a `C²` function with compact support on all of `ℝⁿ`. -/
private theorem exists_mvPolynomial_near_of_hasCompactSupport {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) {g : (Fin n → ℝ) → ℝ} (hg : ContDiff ℝ 2 g) (hgs : HasCompactSupport g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ, ∀ x ∈ K,
      |eval x p - g x| ≤ ε ∧
      (∀ i, |eval x (pderiv i p) - fderiv ℝ g x (Pi.single i 1)| ≤ ε) ∧
      ∀ i j, |eval x (pderiv i (pderiv j p)) -
        fderiv ℝ (fun y => fderiv ℝ g y (Pi.single j 1)) x (Pi.single i 1)| ≤ ε := by
  have hd : ∀ j : Fin n, ContDiff ℝ 1 fun y => fderiv ℝ g y (Pi.single j 1) := fun j =>
    (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hds : ∀ j : Fin n, HasCompactSupport fun y => fderiv ℝ g y (Pi.single j 1) := fun j =>
    hgs.fderiv_apply (𝕜 := ℝ) (Pi.single j 1)
  let H : Option (Fin n ⊕ Fin n × Fin n) → (Fin n → ℝ) → ℝ := fun k =>
    k.elim g (Sum.elim (fun j y => fderiv ℝ g y (Pi.single j 1))
      fun ij y => fderiv ℝ (fun z => fderiv ℝ g z (Pi.single ij.2 1)) y (Pi.single ij.1 1))
  have hHc : ∀ k, Continuous (H k) := by
    rintro (_ | j | ⟨i, j⟩)
    · exact hg.continuous
    · exact (hd j).continuous
    · exact ((hd j).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hHs : ∀ k, HasCompactSupport (H k) := by
    rintro (_ | j | ⟨i, j⟩)
    · exact hgs
    · exact hds j
    · exact (hds j).fderiv_apply (𝕜 := ℝ) (Pi.single i 1)
  obtain ⟨Q, hQ⟩ := exists_mvPolynomial_convolution_near H hHc hHs hK hε
  obtain ⟨P, hP⟩ := exists_eval_eq_integral Q g hg.continuous hgs
  have hP0 : ∀ x, eval x P = ((fun y => eval y Q) ⋆ g) x := fun x => by
    rw [convolution_eq_swap, ← hP x]
    simp
  have hP1 : ∀ j x, eval x (pderiv j P)
      = ((fun y => eval y Q) ⋆ fun y => fderiv ℝ g y (Pi.single j 1)) x :=
    fun j => eval_pderiv_eq_convolution (hg.of_le (by norm_num)) hgs hP0 j
  have hP2 : ∀ i j x, eval x (pderiv i (pderiv j P)) = ((fun y => eval y Q) ⋆
      fun y => fderiv ℝ (fun z => fderiv ℝ g z (Pi.single j 1)) y (Pi.single i 1)) x :=
    fun i j => eval_pderiv_eq_convolution (hd j) (hds j) (hP1 j) i
  refine ⟨P, fun x hx => ⟨?_, fun i => ?_, fun i j => ?_⟩⟩
  · rw [hP0 x]
    exact hQ none x hx
  · rw [hP1 i x]
    exact hQ (some (Sum.inl i)) x hx
  · rw [hP2 i j x]
    exact hQ (some (Sum.inr (i, j))) x hx

end

/- The analysis imports above make `NormedSpace ℝ ℝ` resolve through `InnerProductSpace`. Prefer
the instance found with only the header imports, so that the statements below elaborate to the same
terms as in that environment. -/
attribute [local instance high] NormedField.toNormedSpace

/-- **`C²` polynomial approximation on a compact set.** A function that is `C²` on an open
neighbourhood `U` of a compact `K ⊆ ℝⁿ` is approximated uniformly on `K` by a polynomial together
with all its first and second partial derivatives. -/
theorem exists_mvPolynomial_near_contDiffOn_two {n : ℕ} {K U : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ 2 f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ, ∀ x ∈ K,
      |eval x p - f x| ≤ ε ∧
      (∀ i, |eval x (pderiv i p) - fderiv ℝ f x (Pi.single i 1)| ≤ ε) ∧
      ∀ i j, |eval x (pderiv i (pderiv j p)) -
        fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1)| ≤ ε := by
  obtain ⟨V₂, hV₂o, hKV₂, hV₂U, hV₂c⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨V₁, hV₁o, hKV₁, hV₁V₂, -⟩ := exists_open_between_and_isCompact_closure hK hV₂o hKV₂
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 2) hV₂o isClosed_closure hV₁V₂
  have hχ2 : ContDiff ℝ 2 χ := by exact_mod_cast hχ
  have htχ : tsupport χ = closure V₂ := by rw [tsupport, hχs]
  set g : (Fin n → ℝ) → ℝ := fun x => χ x * f x with hg_def
  have hgs : HasCompactSupport g := by
    have : HasCompactSupport χ := by
      rw [HasCompactSupport, htχ]
      exact hV₂c
    exact this.mul_right
  have hg : ContDiff ℝ 2 g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact hχ2.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
    · have hxχ : x ∉ tsupport χ := fun h => hx (hV₂U (htχ ▸ h))
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
      simp [hg_def, hy]
  have hfg : ∀ y ∈ V₁, g y = f y := fun y hy => by
    simp only [hg_def, (hχ1 y).mp (subset_closure hy), one_mul]
  have hev : ∀ y ∈ V₁, g =ᶠ[nhds y] f := fun y hy => Filter.eventually_of_mem (hV₁o.mem_nhds hy) hfg
  obtain ⟨p, hp⟩ := exists_mvPolynomial_near_of_hasCompactSupport hK hg hgs hε
  refine ⟨p, fun x hx => ?_⟩
  have hxV : x ∈ V₁ := hKV₁ hx
  obtain ⟨h0, h1, h2⟩ := hp x hx
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · rw [← hfg x hxV]
    exact h0
  · rw [← (hev x hxV).fderiv_eq]
    exact h1 i
  · have hd : (fun y => fderiv ℝ g y (Pi.single j 1)) =ᶠ[nhds x]
        fun y => fderiv ℝ f y (Pi.single j 1) :=
      Filter.eventually_of_mem (hV₁o.mem_nhds hxV) fun y hy => by simp only [(hev y hy).fderiv_eq]
    rw [← hd.fderiv_eq]
    exact h2 i j

private theorem isCompact_simplex {n : ℕ} :
    IsCompact {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
  have hcube : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hclosed : IsClosed {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
    have h1 : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
      have hEq : {x : Fin n → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x | 0 ≤ x i} := by
        ext x
        simp
      rw [hEq]
      apply isClosed_iInter
      intro i
      have hcont : Continuous (fun x : Fin n → ℝ => x i) := continuous_apply i
      have hclosedIci : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
      have hpre : {x : Fin n → ℝ | 0 ≤ x i} = (fun x : Fin n → ℝ => x i) ⁻¹' (Set.Ici 0) := rfl
      rw [hpre]
      exact hclosedIci.preimage hcont
    have h2 : IsClosed {x : Fin n → ℝ | ∑ i, x i ≤ 1} := by
      have hcont : Continuous (fun x : Fin n → ℝ => ∑ i, x i) := by
        apply continuous_finsetSum
        intro i _
        exact continuous_apply i
      have hclosedIic : IsClosed (Set.Iic (1 : ℝ)) := isClosed_Iic
      have hpre : {x : Fin n → ℝ | ∑ i, x i ≤ 1}
          = (fun x : Fin n → ℝ => ∑ i, x i) ⁻¹' (Set.Iic 1) := rfl
      rw [hpre]
      exact hclosedIic.preimage hcont
    have hEq : {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}
        = {x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩ {x : Fin n → ℝ | ∑ i, x i ≤ 1} := by
      ext x
      simp
    rw [hEq]
    exact h1.inter h2
  have hsub : {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}
      ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
    intro x hx i _
    simp only [Set.mem_Icc]
    obtain ⟨h0, hsum⟩ := hx
    constructor
    · exact h0 i
    · calc x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
        _ ≤ 1 := hsum
  exact hcube.of_isClosed_subset hclosed hsub

/-- **`C²` polynomial approximation on the simplex** `Δ_{K-1} = {x ∈ ℝ^{K-1} | xᵢ ≥ 0, ∑ xᵢ ≤ 1}`
(record shape, `n = K - 1`). -/
theorem exists_mvPolynomial_near_contDiffOn_two_simplex {n : ℕ} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hΔU : {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} ⊆ U)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ 2 f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ, ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → ∑ i, x i ≤ 1 →
      |eval x p - f x| ≤ ε ∧
      (∀ i, |eval x (pderiv i p) - fderiv ℝ f x (Pi.single i 1)| ≤ ε) ∧
      ∀ i j, |eval x (pderiv i (pderiv j p)) -
        fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1)| ≤ ε := by
  obtain ⟨p, hp⟩ := exists_mvPolynomial_near_contDiffOn_two isCompact_simplex hU hΔU hf hε
  exact ⟨p, fun x hx0 hsum => hp x ⟨hx0, hsum⟩⟩

end MathlibExt.Biology.PopulationGenetics.Diffusion
