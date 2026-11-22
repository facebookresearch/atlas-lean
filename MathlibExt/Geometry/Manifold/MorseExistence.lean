/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.MorseFunction
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.LinearAlgebra.Dual.Lemmas
import MathlibExt.Geometry.Manifold.MorseLemma
import MathlibExt.Geometry.Manifold.Sard
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

open scoped Manifold ContDiff Topology

namespace MathlibExt.Geometry.Manifold.MorseExistenceWanted

open MathlibExt.Geometry.Manifold.ReebSphereWanted
open MathlibExt.Geometry.Manifold.MorseTheoryWanted
open MathlibExt.Geometry.Manifold.MorseLemmaWanted
open MathlibExt.Geometry.Manifold.SardWanted

open Set

universe uM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
variable [T2Space M] [SecondCountableTopology M]

/-- Chart-critical: the derivative of `g` in the chart at `c` vanishes at `y`. -/
private def mfe_crit (g : M → ℝ) (c y : M) : Prop :=
  fderiv ℝ (g ∘ (extChartAt I c).symm) ((extChartAt I c) y) = 0

/-- Chart-nondegenerate: the chart Hessian of `g` at `y` has trivial kernel. -/
private def mfe_nondeg (g : M → ℝ) (c y : M) : Prop :=
  ∀ v : E, (∀ w : E, fderiv ℝ (fderiv ℝ (g ∘ (extChartAt I c).symm))
    ((extChartAt I c) y) v w = 0) → v = 0

omit [FiniteDimensional ℝ E] [T2Space M] [SecondCountableTopology M] in
/-- Manifold critical points are chart-critical. -/
private lemma mfe_crit_of_mfderiv {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (c p : M) (hp : p ∈ (extChartAt I c).source)
    (h : mfderiv I 𝓘(ℝ, ℝ) g p = 0) : mfe_crit (I := I) g c p := by
  have hxsrc' : p ∈ (chartAt H c).source := by
    rw [← extChartAt_source I c]
    exact hp
  have he_mdiff : MDiffAt (⇑(extChartAt I c)) p :=
    mdifferentiableAt_extChartAt hxsrc'
  have he_has : HasMFDerivAt I 𝓘(ℝ, E) (⇑(extChartAt I c)) p
      (mfderiv I 𝓘(ℝ, E) (⇑(extChartAt I c)) p) :=
    MDifferentiableAt.hasMFDerivAt he_mdiff
  have hmem : (extChartAt I c) p ∈ (extChartAt I c).target :=
    (extChartAt I c).map_source hp
  have hu : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (g ∘ (extChartAt I c).symm)
      ((extChartAt I c).target) :=
    hg.comp_contMDiffOn (contMDiffOn_extChartAt_symm c)
  have huD : ContDiffOn ℝ ∞ (g ∘ (extChartAt I c).symm)
      ((extChartAt I c).target) := contMDiffOn_iff_contDiffOn.mp hu
  have hg_diff : DifferentiableAt ℝ (g ∘ (extChartAt I c).symm)
      ((extChartAt I c) p) :=
    (huD.contDiffAt ((isOpen_extChartAt_target c).mem_nhds hmem)).differentiableAt
      (by simp)
  have hg_has : HasFDerivAt (g ∘ (extChartAt I c).symm)
      (fderiv ℝ (g ∘ (extChartAt I c).symm) ((extChartAt I c) p))
      ((extChartAt I c) p) := hg_diff.hasFDerivAt
  have hg_mf : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (g ∘ (extChartAt I c).symm)
      ((extChartAt I c) p)
      (fderiv ℝ (g ∘ (extChartAt I c).symm) ((extChartAt I c) p)) :=
    HasFDerivAt.hasMFDerivAt hg_has
  have hcomp : HasMFDerivAt I 𝓘(ℝ, ℝ)
      ((g ∘ (extChartAt I c).symm) ∘ (extChartAt I c)) p _ :=
    hg_mf.comp p he_has
  have heq : g =ᶠ[𝓝 p] (g ∘ (extChartAt I c).symm) ∘ (extChartAt I c) := by
    filter_upwards [(isOpen_extChartAt_source c).mem_nhds hp] with y hy
    exact congrArg g ((extChartAt I c).left_inv hy).symm
  have hf_has := hcomp.congr_of_eventuallyEq_abuse heq
  have hmf := hf_has.mfderiv
  rw [hmf] at h
  have he_inv : (mfderiv I 𝓘(ℝ, E) (⇑(extChartAt I c)) p).IsInvertible :=
    isInvertible_mfderiv_extChartAt hp
  have hsurj : Function.Surjective (mfderiv I 𝓘(ℝ, E) (⇑(extChartAt I c)) p) :=
    he_inv.surjective
  unfold mfe_crit
  apply ContinuousLinearMap.ext
  intro w
  obtain ⟨v, hv⟩ := hsurj w
  have h0 := DFunLike.congr_fun h v
  have h1 : (fderiv ℝ (g ∘ ⇑(extChartAt I c).symm) (⇑(extChartAt I c) p))
      ((mfderiv I 𝓘(ℝ, E) ⇑(extChartAt I c) p) v) = 0 := h0
  rw [hv] at h1
  simpa using h1

omit [FiniteDimensional ℝ E] [T2Space M] [SecondCountableTopology M] in
/-- Extended charts are local diffeomorphisms. -/
private lemma mfe_chart_isLocalDiffeo (c p : M) (hp : p ∈ (extChartAt I c).source) :
    IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ (⇑(extChartAt I c)) p := by
  have hto : ContMDiffOn I 𝓘(ℝ, E) ∞ ⇑(extChartAt I c) (extChartAt I c).source := by
    rw [extChartAt_source I c]
    exact contMDiffOn_extChartAt
  let Φ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    PartialDiffeomorph.mk (extChartAt I c) (isOpen_extChartAt_source c)
      (isOpen_extChartAt_target c) hto (contMDiffOn_extChartAt_symm c)
  exact PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Φ hp

omit [FiniteDimensional ℝ E] [I.Boundaryless] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [T2Space M] [SecondCountableTopology M] in
/-- Affine maps `z ↦ T0 (z - z0)` are local diffeomorphisms. -/
private lemma mfe_affine_isLocalDiffeo (n : ℕ)
    (T0 : E ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (z0 z : E) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun z => T0 (z - z0)) z := by
  have hdiff1 : ContDiff ℝ ∞ (fun z : E => T0 (z - z0)) :=
    T0.contDiff.comp (contDiff_id.sub contDiff_const)
  have hdiff2 : ContDiff ℝ ∞ (fun w : EuclideanSpace ℝ (Fin n) => z0 + T0.symm w) :=
    contDiff_const.add T0.symm.contDiff
  have hto : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun z => T0 (z - z0)) univ :=
    hdiff1.contMDiff.contMDiffOn
  have hinv : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞
      (fun w => z0 + T0.symm w) univ :=
    hdiff2.contMDiff.contMDiffOn
  let e : PartialEquiv E (EuclideanSpace ℝ (Fin n)) :=
    { toFun := fun z => T0 (z - z0)
      invFun := fun w => z0 + T0.symm w
      source := univ
      target := univ
      map_source' := fun _ _ => mem_univ _
      map_target' := fun _ _ => mem_univ _
      left_inv' := fun _ _ => by
        show z0 + T0.symm (T0 (_ - z0)) = _
        rw [T0.symm_apply_apply, add_sub_cancel]
      right_inv' := fun _ _ => by
        show T0 ((z0 + T0.symm _) - z0) = _
        rw [add_sub_cancel_left, T0.apply_symm_apply] }
  let Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) E
      (EuclideanSpace ℝ (Fin n)) ∞ :=
    PartialDiffeomorph.mk e isOpen_univ isOpen_univ hto hinv
  exact PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Φ (mem_univ z)

omit [T2Space M] [SecondCountableTopology M] in
/-- The Morse lemma at a nondegenerate chart-critical point. -/
private lemma mfe_morse_at {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (c p : M) (hp : p ∈ (extChartAt I c).source)
    (hcrit : mfe_crit (I := I) g c p) (hnd : mfe_nondeg (I := I) g c p) :
    ∃ (k : ℕ) (_ : k ≤ Module.finrank ℝ E)
      (φ : M → EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
      IsLocalDiffeomorphAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
        ∞ φ p ∧
        φ p = 0 ∧
          ∃ (U : Set M) (_ : IsOpen U) (_ : p ∈ U),
            ∀ q ∈ U, g q = g p + morseQuadratic k (Module.finrank ℝ E) (φ q) := by
  unfold mfe_crit at hcrit
  unfold mfe_nondeg at hnd
  have hmem : (extChartAt I c) p ∈ (extChartAt I c).target :=
    (extChartAt I c).map_source hp
  have hu : ContDiffOn ℝ ∞ (g ∘ ⇑(extChartAt I c).symm) (extChartAt I c).target :=
    contMDiffOn_iff_contDiffOn.mp
      (hg.comp_contMDiffOn (contMDiffOn_extChartAt_symm c))
  set T0 : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean with hT0
  set z0 : E := (extChartAt I c) p with hz0
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_extChartAt_target c) _ hmem
  set R : ℝ := ε / 2 with hR
  have hRpos : 0 < R := by linarith
  have hsub : Metric.closedBall z0 R ⊆ (extChartAt I c).target := by
    intro y hy
    apply hball
    have hle : dist y z0 ≤ R := Metric.mem_closedBall.mp hy
    rw [dist_eq_norm] at hle
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  obtain ⟨β, hrIn, hrOut⟩ :
      ∃ β : ContDiffBump (0 : E), β.rIn = R / 4 ∧ β.rOut = R / 2 :=
    ⟨⟨R / 4, R / 2, by linarith, by linarith⟩, rfl, rfl⟩
  set ũ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    fun w => β (T0.symm w) * (g ∘ ⇑(extChartAt I c).symm) (z0 + T0.symm w) with hũ
  have hagree : ∀ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      ‖T0.symm w‖ < R / 4 →
        ũ w = (g ∘ ⇑(extChartAt I c).symm) (z0 + T0.symm w) := by
    intro w hw
    have h1 : β (T0.symm w) = 1 := by
      apply ContDiffBump.one_of_mem_closedBall
      rw [hrIn, Metric.mem_closedBall, dist_zero_right]
      linarith
    change β (T0.symm w) * (g ∘ ⇑(extChartAt I c).symm) (z0 + T0.symm w) = _
    rw [h1, one_mul]
  have hũsmooth : ContDiff ℝ (⊤ : ℕ∞) ũ := by
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hcase : ‖T0.symm w‖ < R
    · have hdist : dist (z0 + T0.symm w) z0 = ‖T0.symm w‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      have hAmem : z0 + T0.symm w ∈ (extChartAt I c).target :=
        hsub (by rw [Metric.mem_closedBall, hdist]; exact le_of_lt hcase)
      have huAt : ContDiffAt ℝ (⊤ : ℕ∞) (g ∘ ⇑(extChartAt I c).symm)
          (z0 + T0.symm w) :=
        hu.contDiffAt ((isOpen_extChartAt_target c).mem_nhds hAmem)
      have hA : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => z0 + T0.symm y) :=
        contDiff_const.add T0.symm.contDiff
      have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun y => (g ∘ ⇑(extChartAt I c).symm) (z0 + T0.symm y)) w :=
        ContDiffAt.fun_comp w huAt hA.contDiffAt
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => β (T0.symm y)) w :=
        (β.contDiff.comp T0.symm.contDiff).contDiffAt
      have hmul : ContDiffAt ℝ (⊤ : ℕ∞) ũ w := by
        rw [hũ]
        exact h1.mul h2
      exact hmul
    · push Not at hcase
      have hR2 : R / 2 < ‖T0.symm w‖ := by linarith
      have hSopen : IsOpen
          {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) | R / 2 < ‖T0.symm y‖} :=
        isOpen_lt continuous_const (T0.symm.continuous.norm)
      have hSmem : {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) |
          R / 2 < ‖T0.symm y‖} ∈ 𝓝 w := hSopen.mem_nhds hR2
      have heq : ũ =ᶠ[𝓝 w] fun _ => 0 := by
        filter_upwards [hSmem] with y hy
        have hβ : β (T0.symm y) = 0 := by
          apply ContDiffBump.zero_of_le_dist
          rw [hrOut, dist_zero_right]
          exact le_of_lt hy
        simp [hũ, hβ]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  have hũcrit : fderiv ℝ ũ 0 = 0 := by
    have hmem0 : ‖T0.symm (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ < R / 4 := by
      rw [map_zero, norm_zero]
      linarith
    have hSopen : IsOpen
        {w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) | ‖T0.symm w‖ < R / 4} :=
      isOpen_lt (T0.symm.continuous.norm) continuous_const
    have h0mem : {w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) |
        ‖T0.symm w‖ < R / 4} ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
      hSopen.mem_nhds hmem0
    have heq : ũ =ᶠ[𝓝 (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))]
        (fun w => (g ∘ ⇑(extChartAt I c).symm) (z0 + T0.symm w)) := by
      filter_upwards [h0mem] with w hw
      exact hagree w hw
    rw [heq.fderiv_eq]
    have hz0mem : z0 ∈ (extChartAt I c).target :=
      hsub (Metric.mem_closedBall.mpr (by rw [dist_self]; exact le_of_lt hRpos))
    have hu_diff : DifferentiableAt ℝ (g ∘ ⇑(extChartAt I c).symm) z0 :=
      (hu.contDiffAt ((isOpen_extChartAt_target c).mem_nhds hz0mem)).differentiableAt
        (by simp)
    have hA : HasFDerivAt
        (fun w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => z0 + T0.symm w)
        (T0.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E) 0 :=
      ((T0.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E).hasFDerivAt).const_add
        z0
    have hcomp : HasFDerivAt
        ((g ∘ ⇑(extChartAt I c).symm) ∘
          (fun w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => z0 + T0.symm w))
        (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ) 0 := by
      have hu0 : HasFDerivAt (g ∘ ⇑(extChartAt I c).symm)
          (fderiv ℝ (g ∘ ⇑(extChartAt I c).symm) z0)
          ((fun w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => z0 + T0.symm w)
            (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
        simpa using hu_diff.hasFDerivAt
      have h := hu0.comp
        (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) hA
      rw [hcrit, ContinuousLinearMap.zero_comp] at h
      exact h
    exact hcomp.fderiv
  have bridge : ∀ a b : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      fderiv ℝ (fderiv ℝ (fun w => (g ∘ ⇑(extChartAt I c).symm) (z0 + T0.symm w)))
        0 a b =
        fderiv ℝ (fderiv ℝ (g ∘ ⇑(extChartAt I c).symm)) z0
          (T0.symm a) (T0.symm b) := by
    intro a b
    have e1 := iteratedFDeriv_two_apply (𝕜 := ℝ)
      (fun w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        (g ∘ ⇑(extChartAt I c).symm) (z0 + T0.symm w))
      (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ![a, b]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e1
    have e2 := iteratedFDeriv_two_apply (𝕜 := ℝ) (g ∘ ⇑(extChartAt I c).symm) z0
      ![T0.symm a, T0.symm b]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e2
    rw [← e1, ← e2]
    have hvv : (fun w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (g ∘ ⇑(extChartAt I c).symm) (z0 + T0.symm w))
        = (fun z => (g ∘ ⇑(extChartAt I c).symm) (z + z0)) ∘ ⇑T0.symm := by
      funext w
      simp only [Function.comp_apply]
      rw [add_comm]
    rw [hvv]
    have hcomp : iteratedFDerivWithin ℝ 2
        ((fun z => (g ∘ ⇑(extChartAt I c).symm) (z + z0)) ∘ ⇑T0.symm)
        (⇑T0.symm ⁻¹' (Set.univ : Set E)) 0
        = (iteratedFDerivWithin ℝ 2 (fun z => (g ∘ ⇑(extChartAt I c).symm) (z + z0))
          Set.univ (T0.symm 0)).compContinuousLinearMap fun _ =>
            (↑T0.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E) :=
      T0.symm.iteratedFDerivWithin_comp_right _ uniqueDiffOn_univ (Set.mem_univ _) 2
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ, map_zero] at hcomp
    rw [hcomp, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hm : (fun i => (↑T0.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
        →L[ℝ] E) (![a, b] i)) = ![T0.symm a, T0.symm b] := by
      funext i
      fin_cases i <;> simp
    rw [hm]
    have hadd := iteratedFDeriv_comp_add_right (𝕜 := ℝ)
      (f := (g ∘ ⇑(extChartAt I c).symm)) 2 z0 (0 : E)
    rw [hadd, zero_add]
  have hũnd : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      (∀ w, fderiv ℝ (fderiv ℝ ũ) 0 v w = 0) → v = 0 := by
    have hmem0 : ‖T0.symm (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ < R / 4 := by
      rw [map_zero, norm_zero]
      linarith
    have hSopen : IsOpen
        {w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) | ‖T0.symm w‖ < R / 4} :=
      isOpen_lt (T0.symm.continuous.norm) continuous_const
    have h0mem : {w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) |
        ‖T0.symm w‖ < R / 4} ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
      hSopen.mem_nhds hmem0
    have heq : ũ =ᶠ[𝓝 (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))]
        (fun w => (g ∘ ⇑(extChartAt I c).symm) (z0 + T0.symm w)) := by
      filter_upwards [h0mem] with w hw
      exact hagree w hw
    have hfd : fderiv ℝ ũ =ᶠ[𝓝 (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))]
        fderiv ℝ (fun w => (g ∘ ⇑(extChartAt I c).symm) (z0 + T0.symm w)) :=
      heq.fderiv
    have hfd0 : fderiv ℝ (fderiv ℝ ũ) 0
        = fderiv ℝ (fderiv ℝ (fun w => (g ∘ ⇑(extChartAt I c).symm)
          (z0 + T0.symm w))) 0 := hfd.fderiv_eq
    intro v hv
    have hv0 : T0.symm v = 0 := by
      apply hnd
      intro w'
      have e := hv (T0 w')
      rw [hfd0, bridge v (T0 w'), T0.symm_apply_apply] at e
      exact e
    have hvv : v = T0 (T0.symm v) := (T0.apply_symm_apply v).symm
    rw [hv0, map_zero] at hvv
    exact hvv
  obtain ⟨k, hk, ψ0, hψ0, hψ0_0, U0, hU0open, hU0mem, hform⟩ :=
    morse_lemma ũ hũsmooth hũcrit hũnd
  have hũ0 : ũ 0 = g p := by
    have h0 := hagree 0 (by rw [map_zero, norm_zero]; linarith)
    rw [h0, map_zero, add_zero]
    change (g ∘ ⇑(extChartAt I c).symm) z0 = g p
    rw [hz0]
    change g (⇑(extChartAt I c).symm (⇑(extChartAt I c) p)) = g p
    rw [(extChartAt I c).left_inv hp]
  refine ⟨k, hk, fun q => ψ0 (T0 (⇑(extChartAt I c) q - z0)), ?_, ?_,
    (extChartAt I c).source ∩ ⇑(extChartAt I c) ⁻¹'
      ((extChartAt I c).target ∩ (fun z => T0 (z - z0)) ⁻¹' U0 ∩
        Metric.ball z0 (R / 4)), ?_, ?_, ?_⟩
  · have hchart : IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ ⇑(extChartAt I c) p :=
      mfe_chart_isLocalDiffeo c p hp
    have haff : IsLocalDiffeomorphAt 𝓘(ℝ, E)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞
        (fun z => T0 (z - z0)) (⇑(extChartAt I c) p) :=
      mfe_affine_isLocalDiffeo _ T0 z0 _
    have hpt : (fun z => T0 (z - z0)) (⇑(extChartAt I c) p) = 0 := by
      change T0 (⇑(extChartAt I c) p - z0) = 0
      rw [← hz0, sub_self, map_zero]
    have hψ0' : IsLocalDiffeomorphAt
        𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞ ψ0
        ((fun z => T0 (z - z0)) (⇑(extChartAt I c) p)) := by
      rw [hpt]
      exact hψ0
    exact (hchart.comp _ _ haff).comp _ _ hψ0'
  · change ψ0 (T0 (⇑(extChartAt I c) p - z0)) = 0
    have hpt : T0 (⇑(extChartAt I c) p - z0) = 0 := by
      rw [← hz0, sub_self, map_zero]
    rw [hpt, hψ0_0]
  · apply (continuousOn_extChartAt c).isOpen_inter_preimage (isOpen_extChartAt_source c)
    exact ((isOpen_extChartAt_target c).inter
      (hU0open.preimage (T0.continuous.comp (continuous_id.sub continuous_const)))).inter
      Metric.isOpen_ball
  · refine ⟨hp, ?_⟩
    rw [Set.mem_preimage]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hz0]; exact hmem
    · change (fun z => T0 (z - z0)) (⇑(extChartAt I c) p) ∈ U0
      have hpt : (fun z => T0 (z - z0)) (⇑(extChartAt I c) p) = 0 := by
        change T0 (⇑(extChartAt I c) p - z0) = 0
        rw [← hz0, sub_self, map_zero]
      rw [hpt]
      exact hU0mem
    · rw [Metric.mem_ball, ← hz0, dist_self]
      linarith
  · intro q hq
    obtain ⟨hqsrc, hqmem⟩ := hq
    rw [Set.mem_preimage] at hqmem
    obtain ⟨⟨hqtgt, hqU0⟩, hqball⟩ := hqmem
    rw [Set.mem_preimage] at hqU0
    rw [Metric.mem_ball, dist_eq_norm] at hqball
    have hqq : g q = (g ∘ ⇑(extChartAt I c).symm) (⇑(extChartAt I c) q) := by
      change g q = g (⇑(extChartAt I c).symm (⇑(extChartAt I c) q))
      rw [(extChartAt I c).left_inv hqsrc]
    have hnorm : ‖T0.symm (T0 (⇑(extChartAt I c) q - z0))‖ < R / 4 := by
      rw [T0.symm_apply_apply]
      exact hqball
    have hstep := hagree _ hnorm
    rw [T0.symm_apply_apply,
      show z0 + (⇑(extChartAt I c) q - z0) = ⇑(extChartAt I c) q from by abel] at hstep
    have hqU0' : T0 (⇑(extChartAt I c) q - z0) ∈ U0 := hqU0
    have hformq := hform _ hqU0'
    change g q = g p + morseQuadratic k (Module.finrank ℝ E)
      (ψ0 (T0 (⇑(extChartAt I c) q - z0)))
    rw [hqq, ← hstep, hformq, hũ0]

omit [I.Boundaryless] [IsManifold I (⊤ : ℕ∞) M] in
/-- A countable smooth bump covering of `M`. -/
private lemma mfe_cover :
    ∃ (ι : Type uM) (_ : Countable ι), Nonempty (SmoothBumpCovering ι I M univ) := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨ι, fs, -⟩ := SmoothBumpCovering.exists_isSubordinate I
    (isClosed_univ (X := M)) (fun x _ => Filter.univ_mem)
  refine ⟨ι, ?_, ⟨fs⟩⟩
  have hne : ∀ i, (Function.support (fs i)).Nonempty := fun i => (fs i).nonempty_support
  have hcount := fs.locallyFinite.countable_univ hne
  rwa [Set.countable_univ_iff] at hcount

section MFEparam

variable {ι : Type uM} [Countable ι] (fs : SmoothBumpCovering ι I M univ)

/-- The parametrized function `F a x = ∑ᶠ i, ψ i x * a i (χ i x)`. -/
private noncomputable def mfe_F (a : ι → (E →L[ℝ] ℝ)) (x : M) : ℝ :=
  ∑ᶠ i, (fs i x) * (a i ((extChartAt I (fs.c i)) x))

omit [I.Boundaryless] [SecondCountableTopology M] [Countable ι] in
/-- Each term of `F` is smooth. -/
private lemma mfe_term_smooth (a : ι → (E →L[ℝ] ℝ)) (i : ι) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => (fs i x) * (a i ((extChartAt I (fs.c i)) x))) := by
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ ⇑(extChartAt I (fs.c i))
      (chartAt H (fs.c i)).source :=
    contMDiffOn_extChartAt
  have hg : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (⇑(a i) ∘ ⇑(extChartAt I (fs.c i))) (chartAt H (fs.c i)).source :=
    (a i).contMDiff.comp_contMDiffOn hchart
  have h := (fs i).contMDiff_smul hg
  simpa [smul_eq_mul, Function.comp_apply] using h

omit [I.Boundaryless] [SecondCountableTopology M] [Countable ι] in
/-- The vector version of each term is smooth. -/
private lemma mfe_vec_smooth (i : ι) :
    ContMDiff I 𝓘(ℝ, E) ∞
      (fun x => (fs i x) • ((extChartAt I (fs.c i)) x)) := by
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ ⇑(extChartAt I (fs.c i))
      (chartAt H (fs.c i)).source :=
    contMDiffOn_extChartAt
  exact (fs i).contMDiff_smul hchart

omit [I.Boundaryless] [SecondCountableTopology M] [Countable ι] in
/-- `F a` is smooth. -/
private lemma mfe_F_smooth (a : ι → (E →L[ℝ] ℝ)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (mfe_F fs a) := by
  unfold mfe_F
  apply contMDiff_finsum (fun i => mfe_term_smooth fs a i)
  refine fs.locallyFinite.subset ?_
  intro i x hx
  simp only [Function.mem_support, ne_eq] at hx ⊢
  exact left_ne_zero_of_mul hx

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SecondCountableTopology M]
  [Countable ι] in
/-- Linearity in the parameter at a point. -/
private lemma mfe_F_update [DecidableEq ι] (a : ι → (E →L[ℝ] ℝ)) (i : ι) (v : E →L[ℝ] ℝ)
    (x : M) :
    mfe_F fs (Function.update a i v) x =
      mfe_F fs (Function.update a i 0) x +
        (fs i x) * (v ((extChartAt I (fs.c i)) x)) := by
  classical
  have hfin : {j | fs j x ≠ 0}.Finite := fs.point_finite x
  set t : Finset ι := insert i hfin.toFinset with ht
  have hi_t : i ∈ t := by rw [ht]; exact Finset.mem_insert_self i _
  have hmem_t : ∀ j, fs j x ≠ 0 → j ∈ t := by
    intro j hj
    rw [ht]
    exact Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hj)
  have hsupp_v : Function.support
      (fun j => (fs j x) * ((Function.update a i v j) ((extChartAt I (fs.c j)) x))) ⊆
      ↑t := by
    intro j hj
    simp only [Function.mem_support, ne_eq] at hj ⊢
    exact hmem_t j (left_ne_zero_of_mul hj)
  have hsupp_0 : Function.support
      (fun j => (fs j x) * ((Function.update a i 0 j) ((extChartAt I (fs.c j)) x))) ⊆
      ↑t := by
    intro j hj
    simp only [Function.mem_support, ne_eq] at hj ⊢
    exact hmem_t j (left_ne_zero_of_mul hj)
  unfold mfe_F
  rw [finsum_eq_sum_of_support_subset _ hsupp_v,
    finsum_eq_sum_of_support_subset _ hsupp_0]
  have hterm : ∀ j ∈ t,
      (fs j x) * ((Function.update a i v j) ((extChartAt I (fs.c j)) x)) =
        (fs j x) * ((Function.update a i 0 j) ((extChartAt I (fs.c j)) x)) +
          (if i = j then (fs i x) * (v ((extChartAt I (fs.c i)) x)) else 0) := by
    intro j _
    by_cases hji : i = j
    · subst hji
      rw [Function.update_self, Function.update_self,
        zero_apply, mul_zero, zero_add, ite_eq_left rfl]
    · rw [ite_eq_right hji, add_zero]
      have e1 : Function.update a i v j = a j :=
        Function.update_of_ne (Ne.symm hji) v a
      have e0 : Function.update a i 0 j = a j :=
        Function.update_of_ne (Ne.symm hji) 0 a
      rw [e1, e0]
  calc ∑ j ∈ t, (fs j x) * ((Function.update a i v j) ((extChartAt I (fs.c j)) x))
      = ∑ j ∈ t, ((fs j x) * ((Function.update a i 0 j) ((extChartAt I (fs.c j)) x)) +
        (if i = j then (fs i x) * (v ((extChartAt I (fs.c i)) x)) else 0)) :=
        Finset.sum_congr rfl hterm
    _ = (∑ j ∈ t, (fs j x) * ((Function.update a i 0 j) ((extChartAt I (fs.c j)) x))) +
        (∑ j ∈ t, (if i = j then (fs i x) * (v ((extChartAt I (fs.c i)) x)) else 0)) :=
        Finset.sum_add_distrib
    _ = (∑ j ∈ t, (fs j x) * ((Function.update a i 0 j) ((extChartAt I (fs.c j)) x))) +
        (fs i x) * (v ((extChartAt I (fs.c i)) x)) := by
        rw [Finset.sum_ite_eq t i, ite_eq_left hi_t]

/-- Index of the bump equal to `1` near `x`. -/
private noncomputable def mfe_idx (x : M) : ι := fs.ind x (Set.mem_univ x)

/-- Open neighbourhood of `x` on which the bump at `mfe_idx x` equals `1`. -/
private noncomputable def mfe_O (x : M) : Set M :=
  interior {y | fs (mfe_idx fs x) y = 1}

omit [I.Boundaryless] [IsManifold I ∞ M] [SecondCountableTopology M] [Countable ι] in
/-- Properties of `mfe_O`. -/
private lemma mfe_O_props (x : M) :
    IsOpen (mfe_O fs x) ∧ x ∈ mfe_O fs x ∧
    (∀ y ∈ mfe_O fs x, fs (mfe_idx fs x) y = 1) ∧
    mfe_O fs x ⊆ (extChartAt I (fs.c (mfe_idx fs x))).source := by
  have heq : (fs (mfe_idx fs x)) =ᶠ[𝓝 x] 1 :=
    fs.eventuallyEq_one x (Set.mem_univ x)
  have hS : {y | fs (mfe_idx fs x) y = 1} ∈ 𝓝 x := heq
  refine ⟨isOpen_interior, mem_interior_iff_mem_nhds.mpr hS, ?_, ?_⟩
  · intro y hy
    unfold mfe_O at hy
    simpa using interior_subset hy
  · intro y hy
    unfold mfe_O at hy
    have h1 : fs (mfe_idx fs x) y = 1 := by
      simpa using interior_subset hy
    have hsupp : y ∈ Function.support (fs (mfe_idx fs x)) := by
      have hne : fs (mfe_idx fs x) y ≠ 0 := by
        rw [h1]
        exact one_ne_zero
      exact Function.mem_support.mpr hne
    have hts : y ∈ tsupport (fs (mfe_idx fs x)) := subset_tsupport _ hsupp
    have hsub := SmoothBumpFunction.tsupport_subset_chartAt_source (fs (mfe_idx fs x))
    have hchart : y ∈ (chartAt H (fs.c (mfe_idx fs x))).source := hsub hts
    rw [extChartAt_source]
    exact hchart

omit [I.Boundaryless] [IsManifold I ∞ M] [SecondCountableTopology M] [Countable ι] in
/-- Compact pieces `K x ⊆ interior (L x)` inside `O x`. -/
private lemma mfe_KL_exists (x : M) :
    ∃ K L : Set M, IsCompact K ∧ IsCompact L ∧ x ∈ interior K ∧ K ⊆ interior L ∧
      L ⊆ mfe_O fs x := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨hOopen, hxO, -, -⟩ := mfe_O_props fs x
  obtain ⟨K, hKc, hxK, hKO⟩ := exists_compact_subset hOopen hxO
  obtain ⟨L, hLc, hKL, hLO⟩ := exists_compact_between hKc hOopen hKO
  exact ⟨K, L, hKc, hLc, hxK, hKL, hLO⟩

/-- The inner compact piece. -/
private noncomputable def mfe_K (x : M) : Set M :=
  Classical.choose (mfe_KL_exists fs x)

/-- The outer compact piece. -/
private noncomputable def mfe_L (x : M) : Set M :=
  Classical.choose (Classical.choose_spec (mfe_KL_exists fs x))

omit [I.Boundaryless] [IsManifold I ∞ M] [SecondCountableTopology M] [Countable ι] in
/-- Properties of the compact pieces. -/
private lemma mfe_KL_props (x : M) :
    IsCompact (mfe_K fs x) ∧ IsCompact (mfe_L fs x) ∧ x ∈ interior (mfe_K fs x) ∧
    mfe_K fs x ⊆ interior (mfe_L fs x) ∧ mfe_L fs x ⊆ mfe_O fs x :=
  Classical.choose_spec (Classical.choose_spec (mfe_KL_exists fs x))

omit [I.Boundaryless] [IsManifold I ∞ M] [Countable ι] in
/-- Countably many interiors cover `M`. -/
private lemma mfe_T_exists :
    ∃ T : Set M, T.Countable ∧ ⋃ x ∈ T, interior (mfe_K fs x) = univ := by
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x => interior (mfe_K fs x)) (fun x => isOpen_interior)
  refine ⟨T, hTc, ?_⟩
  rw [hTeq]
  apply Set.eq_univ_of_forall
  intro x
  apply Set.mem_iUnion.mpr
  exact ⟨x, (mfe_KL_props fs x).2.2.1⟩

/-- The countable index set. -/
private noncomputable def mfe_T : Set M := Classical.choose (mfe_T_exists fs)

omit [I.Boundaryless] [IsManifold I ∞ M] [Countable ι] in
/-- `mfe_T` is countable. -/
private lemma mfe_T_countable : (mfe_T fs).Countable :=
  (Classical.choose_spec (mfe_T_exists fs)).1

omit [I.Boundaryless] [IsManifold I ∞ M] [Countable ι] in
/-- The interiors over `mfe_T` cover `M`. -/
private lemma mfe_T_cover : ⋃ x ∈ mfe_T fs, interior (mfe_K fs x) = univ :=
  (Classical.choose_spec (mfe_T_exists fs)).2

/-- The finite set of indices meeting `L x`. -/
private noncomputable def mfe_J (x : M) : Finset ι :=
  (fs.locallyFinite.finite_nonempty_inter_compact (mfe_KL_props fs x).2.1).toFinset

omit [I.Boundaryless] [IsManifold I ∞ M] [SecondCountableTopology M] [Countable ι] in
/-- On `interior (L x)`, `F a` is a finite sum over `J x`. -/
private lemma mfe_sum_formula (x : M) (a : ι → (E →L[ℝ] ℝ)) (y : M)
    (hy : y ∈ interior (mfe_L fs x)) :
    mfe_F fs a y = ∑ j ∈ mfe_J fs x, (fs j y) * (a j ((extChartAt I (fs.c j)) y)) := by
  have hL : y ∈ mfe_L fs x := interior_subset hy
  have hsupp : Function.support
      (fun j => (fs j y) * (a j ((extChartAt I (fs.c j)) y))) ⊆ ↑(mfe_J fs x) := by
    intro j hj
    rw [Finset.mem_coe]
    unfold mfe_J
    rw [Set.Finite.mem_toFinset]
    change ((Function.support ↑(fs.toFun j)) ∩ mfe_L fs x).Nonempty
    have hj0 : fs j y ≠ 0 := left_ne_zero_of_mul hj
    exact ⟨y, hj0, hL⟩
  unfold mfe_F
  exact finsum_eq_sum_of_support_subset _ hsupp

/-- Chart points over `interior (L x)`. -/
private noncomputable def mfe_Omega (x : M) : Set E :=
  (extChartAt I (fs.c (mfe_idx fs x))).target ∩
    (extChartAt I (fs.c (mfe_idx fs x))).symm ⁻¹' interior (mfe_L fs x)

omit [IsManifold I ∞ M] [SecondCountableTopology M] [Countable ι] in
/-- `mfe_Omega x` is open. -/
private lemma mfe_Omega_open (x : M) : IsOpen (mfe_Omega fs x) :=
  (continuousOn_extChartAt_symm _).isOpen_inter_preimage
    (isOpen_extChartAt_target _) isOpen_interior

/-- The `j`-th vector piece composed with the chart inverse. -/
private noncomputable def mfe_h (x : M) (j : ι) : E → E :=
  (fun y => (fs j y) • ((extChartAt I (fs.c j)) y)) ∘
    (extChartAt I (fs.c (mfe_idx fs x))).symm

omit [I.Boundaryless] [SecondCountableTopology M] [Countable ι] in
/-- Each `mfe_h x j` is smooth on the chart target. -/
private lemma mfe_h_smooth (x : M) (j : ι) :
    ContDiffOn ℝ ∞ (mfe_h fs x j)
      (extChartAt I (fs.c (mfe_idx fs x))).target := by
  have hv : ContMDiff I 𝓘(ℝ, E) ∞
      (fun y => (fs j y) • ((extChartAt I (fs.c j)) y)) :=
    mfe_vec_smooth fs j
  have hcomp := hv.comp_contMDiffOn
    (contMDiffOn_extChartAt_symm (fs.c (mfe_idx fs x)))
  have hiff := contMDiffOn_iff_contDiffOn.mp hcomp
  unfold mfe_h
  exact hiff

omit [I.Boundaryless] [IsManifold I ∞ M] [SecondCountableTopology M] [Countable ι] in
/-- Chart values at `K x` lie in `mfe_Omega x`. -/
private lemma mfe_chi_mem (x : M) (y : M) (hy : y ∈ mfe_K fs x) :
    (extChartAt I (fs.c (mfe_idx fs x))) y ∈ mfe_Omega fs x := by
  have hprops := mfe_KL_props fs x
  have hO := mfe_O_props fs x
  have hyL : y ∈ interior (mfe_L fs x) := hprops.2.2.2.1 hy
  have hysrc : y ∈ (extChartAt I (fs.c (mfe_idx fs x))).source := by
    apply hO.2.2.2
    apply hprops.2.2.2.2
    exact interior_subset hyL
  refine ⟨(extChartAt I (fs.c (mfe_idx fs x))).map_source hysrc, ?_⟩
  change (extChartAt I (fs.c (mfe_idx fs x))).symm
    ((extChartAt I (fs.c (mfe_idx fs x))) y) ∈ interior (mfe_L fs x)
  rw [(extChartAt I (fs.c (mfe_idx fs x))).left_inv hysrc]
  exact hyL

omit [I.Boundaryless] [IsManifold I ∞ M] [SecondCountableTopology M] [Countable ι] in
/-- On `mfe_Omega x`, `F a ∘ symm` is the finite linear combination. -/
private lemma mfe_sum_Omega (x : M) (a : ι → (E →L[ℝ] ℝ)) (z : E)
    (hz : z ∈ mfe_Omega fs x) :
    ((mfe_F fs a) ∘ (extChartAt I (fs.c (mfe_idx fs x))).symm) z =
      ∑ j ∈ mfe_J fs x, (a j) ((mfe_h fs x j) z) := by
  have hzL : (extChartAt I (fs.c (mfe_idx fs x))).symm z ∈ interior (mfe_L fs x) :=
    hz.2
  have hsum := mfe_sum_formula fs x a _ hzL
  rw [Function.comp_apply, hsum]
  apply Finset.sum_congr rfl
  intro j _
  show (fs j _) * _ = (a j) ((mfe_h fs x j) z)
  unfold mfe_h
  rw [Function.comp_apply, map_smul, smul_eq_mul]

omit [SecondCountableTopology M] [Countable ι] in
/-- First-derivative formula on `mfe_Omega x`. -/
private lemma mfe_D1 (x : M) (a : ι → (E →L[ℝ] ℝ)) (z : E)
    (hz : z ∈ mfe_Omega fs x) :
    fderiv ℝ ((mfe_F fs a) ∘ (extChartAt I (fs.c (mfe_idx fs x))).symm) z =
      ∑ j ∈ mfe_J fs x, (a j).comp (fderiv ℝ (mfe_h fs x j) z) := by
  have hOopen := mfe_Omega_open fs x
  have hmem : mfe_Omega fs x ∈ 𝓝 z := hOopen.mem_nhds hz
  unfold mfe_Omega at hz
  obtain ⟨hzT, -⟩ := hz
  have hevent : ((mfe_F fs a) ∘ (extChartAt I (fs.c (mfe_idx fs x))).symm)
      =ᶠ[𝓝 z] (fun z' => ∑ j ∈ mfe_J fs x, (a j) ((mfe_h fs x j) z')) := by
    filter_upwards [hmem] with z' hz'
    exact mfe_sum_Omega fs x a z' hz'
  have hdiff : ∀ j, DifferentiableAt ℝ (mfe_h fs x j) z := fun j =>
    ((mfe_h_smooth fs x j).contDiffAt
      ((isOpen_extChartAt_target _).mem_nhds hzT)).differentiableAt (by simp)
  have hterm : ∀ j ∈ mfe_J fs x, HasFDerivAt ((a j) ∘ (mfe_h fs x j))
      ((a j).comp (fderiv ℝ (mfe_h fs x j) z)) z := fun j _ =>
    (a j).hasFDerivAt.comp z (hdiff j).hasFDerivAt
  have hsum := HasFDerivAt.sum (u := mfe_J fs x) hterm
  rw [hevent.fderiv_eq]
  have hfun : (fun z' => ∑ j ∈ mfe_J fs x, (a j) ((mfe_h fs x j) z'))
      = (∑ i ∈ mfe_J fs x, ⇑(a i) ∘ mfe_h fs x i) := by
    funext z'
    simp only [Finset.sum_apply, Function.comp_apply]
  rw [hfun]
  exact hsum.fderiv

omit [SecondCountableTopology M] [Countable ι] in
/-- Joint continuity of a first-derivative term. -/
private lemma mfe_D1term_cont (x : M) (j : ι) :
    ContinuousOn (fun p : (ι → (E →L[ℝ] ℝ)) × E =>
      (p.1 j).comp (fderiv ℝ (mfe_h fs x j) p.2))
      (Set.univ ×ˢ mfe_Omega fs x) := by
  have hcont : ContinuousOn (fderiv ℝ (mfe_h fs x j))
      (extChartAt I (fs.c (mfe_idx fs x))).target :=
    (mfe_h_smooth fs x j).continuousOn_fderiv_of_isOpen
      (isOpen_extChartAt_target _) (by simp)
  have hΩsub : mfe_Omega fs x ⊆ (extChartAt I (fs.c (mfe_idx fs x))).target := by
    intro z hz
    unfold mfe_Omega at hz
    exact hz.1
  have hD : ContinuousOn ((fderiv ℝ (mfe_h fs x j)) ∘ Prod.snd)
      (Set.univ ×ˢ mfe_Omega fs x) :=
    (hcont.mono hΩsub).comp continuous_snd.continuousOn
      (fun (p : (ι → (E →L[ℝ] ℝ)) × E) (hp : p ∈ Set.univ ×ˢ mfe_Omega fs x) =>
        hp.2)
  have hj1 : Continuous (fun a : (ι → (E →L[ℝ] ℝ)) => a j) := continuous_apply j
  have hL : Continuous (fun p : (ι → (E →L[ℝ] ℝ)) × E =>
      ContinuousLinearMap.compL ℝ E E ℝ (p.1 j)) :=
    ((ContinuousLinearMap.compL ℝ E E ℝ).continuous.comp hj1).comp continuous_fst
  have hmain : ContinuousOn (fun p : (ι → (E →L[ℝ] ℝ)) × E =>
      (ContinuousLinearMap.compL ℝ E E ℝ (p.1 j))
        (fderiv ℝ (mfe_h fs x j) p.2))
      (Set.univ ×ˢ mfe_Omega fs x) :=
    (hL.continuousOn.mono (Set.subset_univ _)).clm_apply hD
  simpa [ContinuousLinearMap.compL_apply] using hmain

omit [SecondCountableTopology M] [Countable ι] in
/-- Second-derivative formula on `mfe_Omega x`. -/
private lemma mfe_D2 (x : M) (a : ι → (E →L[ℝ] ℝ)) (z : E)
    (hz : z ∈ mfe_Omega fs x) :
    fderiv ℝ (fderiv ℝ ((mfe_F fs a) ∘
      (extChartAt I (fs.c (mfe_idx fs x))).symm)) z =
      ∑ j ∈ mfe_J fs x, (ContinuousLinearMap.compL ℝ E E ℝ (a j)).comp
        (fderiv ℝ (fderiv ℝ (mfe_h fs x j)) z) := by
  have hOopen := mfe_Omega_open fs x
  have hmem : mfe_Omega fs x ∈ 𝓝 z := hOopen.mem_nhds hz
  unfold mfe_Omega at hz
  obtain ⟨hzT, -⟩ := hz
  have hevent1 : fderiv ℝ ((mfe_F fs a) ∘
      (extChartAt I (fs.c (mfe_idx fs x))).symm)
      =ᶠ[𝓝 z] (fun z' => ∑ j ∈ mfe_J fs x,
        (a j).comp (fderiv ℝ (mfe_h fs x j) z')) := by
    filter_upwards [hmem] with z' hz'
    exact mfe_D1 fs x a z' hz'
  have hDf : ∀ j, ContDiffOn ℝ ∞ (fderiv ℝ (mfe_h fs x j))
      (extChartAt I (fs.c (mfe_idx fs x))).target := fun j =>
    (mfe_h_smooth fs x j).fderiv_of_isOpen (isOpen_extChartAt_target _) (by simp)
  have hdiff2 : ∀ j, DifferentiableAt ℝ (fderiv ℝ (mfe_h fs x j)) z := fun j =>
    ((hDf j).contDiffAt ((isOpen_extChartAt_target _).mem_nhds hzT)).differentiableAt
      (by simp)
  have hterm : ∀ j ∈ mfe_J fs x,
      HasFDerivAt (⇑(ContinuousLinearMap.compL ℝ E E ℝ (a j)) ∘
        (fderiv ℝ (mfe_h fs x j)))
        ((ContinuousLinearMap.compL ℝ E E ℝ (a j)).comp
          (fderiv ℝ (fderiv ℝ (mfe_h fs x j)) z)) z := fun j _ =>
    (ContinuousLinearMap.compL ℝ E E ℝ (a j)).hasFDerivAt.comp z
      (hdiff2 j).hasFDerivAt
  have hsum := HasFDerivAt.sum (u := mfe_J fs x) hterm
  rw [hevent1.fderiv_eq]
  have hfun : (fun z' => ∑ j ∈ mfe_J fs x,
        (a j).comp (fderiv ℝ (mfe_h fs x j) z'))
      = (∑ i ∈ mfe_J fs x, ⇑(ContinuousLinearMap.compL ℝ E E ℝ (a i)) ∘
        (fderiv ℝ (mfe_h fs x i))) := by
    funext z'
    simp only [Finset.sum_apply, Function.comp_apply,
      ContinuousLinearMap.compL_apply]
  rw [hfun]
  exact hsum.fderiv

omit [SecondCountableTopology M] [Countable ι] in
/-- Joint continuity of a second-derivative term. -/
private lemma mfe_D2term_cont (x : M) (j : ι) :
    ContinuousOn (fun p : (ι → (E →L[ℝ] ℝ)) × E =>
      (ContinuousLinearMap.compL ℝ E E ℝ (p.1 j)).comp
        (fderiv ℝ (fderiv ℝ (mfe_h fs x j)) p.2))
      (Set.univ ×ˢ mfe_Omega fs x) := by
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ (mfe_h fs x j))
      (extChartAt I (fs.c (mfe_idx fs x))).target :=
    (mfe_h_smooth fs x j).fderiv_of_isOpen (isOpen_extChartAt_target _) (by simp)
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ (mfe_h fs x j)))
      (extChartAt I (fs.c (mfe_idx fs x))).target :=
    hDf.continuousOn_fderiv_of_isOpen (isOpen_extChartAt_target _) (by simp)
  have hΩsub : mfe_Omega fs x ⊆ (extChartAt I (fs.c (mfe_idx fs x))).target := by
    intro z hz
    unfold mfe_Omega at hz
    exact hz.1
  have hD : ContinuousOn ((fderiv ℝ (fderiv ℝ (mfe_h fs x j))) ∘ Prod.snd)
      (Set.univ ×ˢ mfe_Omega fs x) :=
    (hcont.mono hΩsub).comp continuous_snd.continuousOn
      (fun (p : (ι → (E →L[ℝ] ℝ)) × E) (hp : p ∈ Set.univ ×ˢ mfe_Omega fs x) =>
        hp.2)
  have hj1 : Continuous (fun a : (ι → (E →L[ℝ] ℝ)) => a j) := continuous_apply j
  have hinner : Continuous (fun p : (ι → (E →L[ℝ] ℝ)) × E =>
      ContinuousLinearMap.compL ℝ E E ℝ (p.1 j)) :=
    ((ContinuousLinearMap.compL ℝ E E ℝ).continuous.comp hj1).comp continuous_fst
  exact hinner.continuousOn.clm_comp hD

omit [SecondCountableTopology M] [Countable ι] in
/-- Joint continuity of the second-derivative sum. -/
private lemma mfe_D2_cont (x : M) :
    ContinuousOn (fun p : (ι → (E →L[ℝ] ℝ)) × E =>
      ∑ j ∈ mfe_J fs x, (ContinuousLinearMap.compL ℝ E E ℝ (p.1 j)).comp
        (fderiv ℝ (fderiv ℝ (mfe_h fs x j)) p.2))
      (Set.univ ×ˢ mfe_Omega fs x) := by
  apply continuousOn_finsetSum
  intro j _
  exact mfe_D2term_cont fs x j

/-- Good parameters at `x`: every chart-critical point in `K x` is nondegenerate. -/
private noncomputable def mfe_Good (x : M) : Set (ι → (E →L[ℝ] ℝ)) :=
  { a | ∀ y ∈ mfe_K fs x, mfe_crit (I := I) (mfe_F fs a) (fs.c (mfe_idx fs x)) y →
    mfe_nondeg (I := I) (mfe_F fs a) (fs.c (mfe_idx fs x)) y }

omit [SecondCountableTopology M] [Countable ι] in
/-- Chart-criticality on `K x` is the vanishing of the `D1` sum. -/
private lemma mfe_crit_iff (x : M) (a : ι → (E →L[ℝ] ℝ)) (y : M)
    (hy : y ∈ mfe_K fs x) :
    mfe_crit (I := I) (mfe_F fs a) (fs.c (mfe_idx fs x)) y ↔
      (∑ j ∈ mfe_J fs x, (a j).comp
        (fderiv ℝ (mfe_h fs x j) ((extChartAt I (fs.c (mfe_idx fs x))) y))) = 0 := by
  unfold mfe_crit
  rw [mfe_D1 fs x a _ (mfe_chi_mem fs x y hy)]

omit [SecondCountableTopology M] [Countable ι] in
/-- Degeneracy on `K x` is a unit kernel vector of the `D2` sum. -/
private lemma mfe_not_nondeg_iff (x : M) (a : ι → (E →L[ℝ] ℝ)) (y : M)
    (hy : y ∈ mfe_K fs x) :
    ¬ mfe_nondeg (I := I) (mfe_F fs a) (fs.c (mfe_idx fs x)) y ↔
      ∃ v : E, ‖v‖ = 1 ∧
        ((∑ j ∈ mfe_J fs x, (ContinuousLinearMap.compL ℝ E E ℝ (a j)).comp
          (fderiv ℝ (fderiv ℝ (mfe_h fs x j))
            ((extChartAt I (fs.c (mfe_idx fs x))) y))) v = 0) := by
  have hD2 := mfe_D2 fs x a _ (mfe_chi_mem fs x y hy)
  unfold mfe_nondeg
  rw [hD2]
  constructor
  · intro hneg
    push Not at hneg
    obtain ⟨v, hv, hne⟩ := hneg
    have hSv : (∑ j ∈ mfe_J fs x, (ContinuousLinearMap.compL ℝ E E ℝ (a j)).comp
        (fderiv ℝ (fderiv ℝ (mfe_h fs x j))
          ((extChartAt I (fs.c (mfe_idx fs x))) y))) v = 0 := by
      apply ContinuousLinearMap.ext
      intro w
      exact hv w
    have hnorm_ne : ‖v‖ ≠ 0 := fun h => hne (norm_eq_zero.mp h)
    refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg v),
        inv_mul_cancel₀ hnorm_ne]
    · rw [map_smul, hSv, smul_zero]
  · rintro ⟨u, hnorm, hSu⟩ hall
    have hu0 : u = 0 := hall u (fun w => by
      have : ((∑ j ∈ mfe_J fs x, (ContinuousLinearMap.compL ℝ E E ℝ (a j)).comp
          (fderiv ℝ (fderiv ℝ (mfe_h fs x j))
            ((extChartAt I (fs.c (mfe_idx fs x))) y))) u) w = 0 := by
        rw [hSu]
        rfl
      exact this)
    rw [hu0, norm_zero] at hnorm
    exact one_ne_zero hnorm.symm

omit [I.Boundaryless] [IsManifold I ∞ M] [SecondCountableTopology M] [Countable ι] in
/-- `K x` lies in `O x` and in the chart source. -/
private lemma mfe_K_sub (x : M) :
    mfe_K fs x ⊆ mfe_O fs x ∧
    mfe_K fs x ⊆ (extChartAt I (fs.c (mfe_idx fs x))).source := by
  obtain ⟨-, -, -, hKL, hLO⟩ := mfe_KL_props fs x
  obtain ⟨-, -, -, hOsrc⟩ := mfe_O_props fs x
  have hKO : mfe_K fs x ⊆ mfe_O fs x :=
    fun y hy => hLO (interior_subset (hKL hy))
  exact ⟨hKO, fun y hy => hOsrc (hKO hy)⟩

omit [I.Boundaryless] [IsManifold I ∞ M] [SecondCountableTopology M] [Countable ι] in
/-- The chart is continuous on the subtype `K x`. -/
private lemma mfe_chi_cont (x : M) :
    Continuous (fun y : ↥(mfe_K fs x) => (extChartAt I (fs.c (mfe_idx fs x))) (y : M)) := by
  have hcont : ContinuousOn ⇑(extChartAt I (fs.c (mfe_idx fs x))) (mfe_K fs x) :=
    (continuousOn_extChartAt _).mono (mfe_K_sub fs x).2
  exact continuousOn_iff_continuous_domRestrict.mp hcont

omit [I.Boundaryless] [IsManifold I ∞ M] [SecondCountableTopology M] [Countable ι] in
/-- First-derivative map on `P × (K × sphere)`. -/
private noncomputable def mfe_F1 (x : M) :
    (ι → (E →L[ℝ] ℝ)) × (↥(mfe_K fs x) × ↥(Metric.sphere (0 : E) 1)) →
      (E →L[ℝ] ℝ) :=
  fun p => ∑ j ∈ mfe_J fs x, (p.1 j).comp
    (fderiv ℝ (mfe_h fs x j) ((extChartAt I (fs.c (mfe_idx fs x))) (p.2.1 : M)))

omit [SecondCountableTopology M] [Countable ι] in
/-- `mfe_F1 x` is continuous. -/
private lemma mfe_F1_cont (x : M) : Continuous (mfe_F1 fs x) := by
  unfold mfe_F1
  apply continuous_finsetSum
  intro j _
  have e_cont : Continuous (fun p : (ι → (E →L[ℝ] ℝ)) ×
      (↥(mfe_K fs x) × ↥(Metric.sphere (0 : E) 1)) =>
        (p.1, (extChartAt I (fs.c (mfe_idx fs x))) (p.2.1 : M))) :=
    continuous_fst.prodMk
      ((mfe_chi_cont fs x).comp (continuous_fst.comp continuous_snd))
  have e_maps : Set.MapsTo (fun p : (ι → (E →L[ℝ] ℝ)) ×
      (↥(mfe_K fs x) × ↥(Metric.sphere (0 : E) 1)) =>
        (p.1, (extChartAt I (fs.c (mfe_idx fs x))) (p.2.1 : M)))
      Set.univ (Set.univ ×ˢ mfe_Omega fs x) := by
    intro p _
    refine ⟨Set.mem_univ _, ?_⟩
    exact mfe_chi_mem fs x _ p.2.1.property
  have hcomp := (mfe_D1term_cont fs x j).comp e_cont.continuousOn e_maps
  rwa [continuousOn_univ] at hcomp

omit [SecondCountableTopology M] [Countable ι] in
/-- Second-derivative map on `P × (K × sphere)`, evaluated at the sphere vector. -/
private noncomputable def mfe_F2 (x : M) :
    (ι → (E →L[ℝ] ℝ)) × (↥(mfe_K fs x) × ↥(Metric.sphere (0 : E) 1)) →
      (E →L[ℝ] ℝ) :=
  fun p => ((∑ j ∈ mfe_J fs x, (ContinuousLinearMap.compL ℝ E E ℝ (p.1 j)).comp
    (fderiv ℝ (fderiv ℝ (mfe_h fs x j))
      ((extChartAt I (fs.c (mfe_idx fs x))) (p.2.1 : M)))) (p.2.2 : E))

omit [SecondCountableTopology M] [Countable ι] in
/-- `mfe_F2 x` is continuous. -/
private lemma mfe_F2_cont (x : M) : Continuous (mfe_F2 fs x) := by
  have e_cont : Continuous (fun p : (ι → (E →L[ℝ] ℝ)) ×
      (↥(mfe_K fs x) × ↥(Metric.sphere (0 : E) 1)) =>
        (p.1, (extChartAt I (fs.c (mfe_idx fs x))) (p.2.1 : M))) :=
    continuous_fst.prodMk
      ((mfe_chi_cont fs x).comp (continuous_fst.comp continuous_snd))
  have e_maps : Set.MapsTo (fun p : (ι → (E →L[ℝ] ℝ)) ×
      (↥(mfe_K fs x) × ↥(Metric.sphere (0 : E) 1)) =>
        (p.1, (extChartAt I (fs.c (mfe_idx fs x))) (p.2.1 : M)))
      Set.univ (Set.univ ×ˢ mfe_Omega fs x) := by
    intro p _
    refine ⟨Set.mem_univ _, ?_⟩
    exact mfe_chi_mem fs x _ p.2.1.property
  have hD : Continuous (fun p : (ι → (E →L[ℝ] ℝ)) ×
      (↥(mfe_K fs x) × ↥(Metric.sphere (0 : E) 1)) =>
        ∑ j ∈ mfe_J fs x, (ContinuousLinearMap.compL ℝ E E ℝ (p.1 j)).comp
          (fderiv ℝ (fderiv ℝ (mfe_h fs x j))
            ((extChartAt I (fs.c (mfe_idx fs x))) (p.2.1 : M)))) := by
    have hcomp := (mfe_D2_cont fs x).comp e_cont.continuousOn e_maps
    rwa [continuousOn_univ] at hcomp
  have hv : Continuous (fun p : (ι → (E →L[ℝ] ℝ)) ×
      (↥(mfe_K fs x) × ↥(Metric.sphere (0 : E) 1)) => ((p.2.2 : E))) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have happly := hD.clm_apply hv
  have heq : (fun p : (ι → (E →L[ℝ] ℝ)) ×
      (↥(mfe_K fs x) × ↥(Metric.sphere (0 : E) 1)) =>
        ((∑ j ∈ mfe_J fs x, (ContinuousLinearMap.compL ℝ E E ℝ (p.1 j)).comp
          (fderiv ℝ (fderiv ℝ (mfe_h fs x j))
            ((extChartAt I (fs.c (mfe_idx fs x))) (p.2.1 : M)))) (p.2.2 : E))) =
      mfe_F2 fs x := rfl
  rwa [heq] at happly

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [SecondCountableTopology M]
  [Countable ι] in
/-- Norm-one vectors are the sphere. -/
private lemma mfe_norm_sphere (v : E) : ‖v‖ = 1 ↔ v ∈ Metric.sphere (0 : E) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]

omit [SecondCountableTopology M] [Countable ι] in
/-- The complement of `Good` is the projection of the zero set. -/
private lemma mfe_compl_eq (x : M) :
    (mfe_Good fs x)ᶜ =
      Prod.fst '' (mfe_F1 fs x ⁻¹' {0} ∩ mfe_F2 fs x ⁻¹' {0}) := by
  ext a
  constructor
  · intro ha
    rw [Set.mem_compl_iff] at ha
    simp only [mfe_Good, Set.mem_ofPred_eq] at ha
    push Not at ha
    obtain ⟨y, hyK, hcrit, hndeg⟩ := ha
    obtain ⟨v, hnorm, hD2v⟩ :=
      (mfe_not_nondeg_iff fs x a y hyK).mp hndeg
    have hF1 : mfe_F1 fs x (a, (⟨y, hyK⟩, ⟨v, (mfe_norm_sphere v).mp hnorm⟩)) = 0 := by
      unfold mfe_F1
      exact (mfe_crit_iff fs x a y hyK).mp hcrit
    have hF2 : mfe_F2 fs x (a, (⟨y, hyK⟩, ⟨v, (mfe_norm_sphere v).mp hnorm⟩)) = 0 := by
      unfold mfe_F2
      simpa using hD2v
    exact ⟨_, ⟨hF1, hF2⟩, rfl⟩
  · rintro ⟨p, ⟨hF1, hF2⟩, rfl⟩
    rw [Set.mem_compl_iff]
    intro hgood
    have hyK : (p.2.1 : M) ∈ mfe_K fs x := p.2.1.property
    have hcrit : mfe_crit (I := I) (mfe_F fs p.1) (fs.c (mfe_idx fs x)) (p.2.1 : M) := by
      have h : (∑ j ∈ mfe_J fs x, (p.1 j).comp
          (fderiv ℝ (mfe_h fs x j)
            ((extChartAt I (fs.c (mfe_idx fs x))) (p.2.1 : M)))) = 0 := by
        have := hF1
        unfold mfe_F1 at this
        exact this
      exact (mfe_crit_iff fs x p.1 _ hyK).mpr h
    have hnd := hgood _ hyK hcrit
    have hD2v : ((∑ j ∈ mfe_J fs x, (ContinuousLinearMap.compL ℝ E E ℝ (p.1 j)).comp
        (fderiv ℝ (fderiv ℝ (mfe_h fs x j))
          ((extChartAt I (fs.c (mfe_idx fs x))) (p.2.1 : M)))) (p.2.2 : E)) = 0 := by
      have := hF2
      unfold mfe_F2 at this
      exact this
    have hnorm : ‖(p.2.2 : E)‖ = 1 := (mfe_norm_sphere _).mpr p.2.2.property
    exact ((mfe_not_nondeg_iff fs x p.1 _ hyK).mpr ⟨_, hnorm, hD2v⟩) hnd

omit [SecondCountableTopology M] [Countable ι] in
/-- `Good x` is open. -/
private lemma mfe_Good_isOpen (x : M) : IsOpen (mfe_Good fs x) := by
  have hKc : IsCompact (mfe_K fs x) := (mfe_KL_props fs x).1
  have hS : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere _ _
  have : CompactSpace ↥(mfe_K fs x) := isCompact_iff_compactSpace.mp hKc
  have : CompactSpace ↥(Metric.sphere (0 : E) 1) := isCompact_iff_compactSpace.mp hS
  have hclosed : IsClosed (mfe_F1 fs x ⁻¹' {0} ∩ mfe_F2 fs x ⁻¹' {0}) :=
    (isClosed_singleton.preimage (mfe_F1_cont fs x)).inter
      (isClosed_singleton.preimage (mfe_F2_cont fs x))
  have himg : IsClosed (Prod.fst '' (mfe_F1 fs x ⁻¹' {0} ∩ mfe_F2 fs x ⁻¹' {0})) :=
    isClosedMap_fst_of_compactSpace _ hclosed
  rw [← mfe_compl_eq fs x] at himg
  have hopen : IsOpen ((mfe_Good fs x)ᶜᶜ) := isOpen_compl_iff.mpr himg
  rwa [compl_compl] at hopen

/-- Chart points over `O x` (for the Sard argument). -/
private noncomputable def mfe_Omega' (x : M) : Set E :=
  (extChartAt I (fs.c (mfe_idx fs x))).target ∩
    (extChartAt I (fs.c (mfe_idx fs x))).symm ⁻¹' mfe_O fs x

omit [IsManifold I ∞ M] [SecondCountableTopology M] [Countable ι] in
/-- `mfe_Omega' x` is open. -/
private lemma mfe_Omega'_open (x : M) : IsOpen (mfe_Omega' fs x) := by
  unfold mfe_Omega'
  exact (continuousOn_extChartAt_symm _).isOpen_inter_preimage
    (isOpen_extChartAt_target _) (mfe_O_props fs x).1

omit [I.Boundaryless] [IsManifold I ∞ M] [SecondCountableTopology M] [Countable ι] in
/-- Chart values at `K x` lie in `mfe_Omega' x`. -/
private lemma mfe_Omega'_mem (x : M) (y : M) (hy : y ∈ mfe_K fs x) :
    (extChartAt I (fs.c (mfe_idx fs x))) y ∈ mfe_Omega' fs x := by
  have hKO := (mfe_K_sub fs x).1 hy
  have hysrc := (mfe_K_sub fs x).2 hy
  refine ⟨(extChartAt I (fs.c (mfe_idx fs x))).map_source hysrc, ?_⟩
  change (extChartAt I (fs.c (mfe_idx fs x))).symm
    ((extChartAt I (fs.c (mfe_idx fs x))) y) ∈ mfe_O fs x
  rw [(extChartAt I (fs.c (mfe_idx fs x))).left_inv hysrc]
  exact hKO

omit [I.Boundaryless] [IsManifold I ∞ M] [SecondCountableTopology M] [Countable ι] in
/-- On `Omega'`, updating the `i`-th parameter adds the linear function. -/
private lemma mfe_update_Omega' (x : M) [DecidableEq ι] (a : ι → (E →L[ℝ] ℝ))
    (v : E →L[ℝ] ℝ)
    (z : E) (hz : z ∈ mfe_Omega' fs x) :
    ((mfe_F fs (Function.update a (mfe_idx fs x) v)) ∘
      (extChartAt I (fs.c (mfe_idx fs x))).symm) z =
      ((mfe_F fs (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm) z + v z := by
  classical
  obtain ⟨hzT, hzO⟩ := hz
  set i := mfe_idx fs x with hi
  set y := (extChartAt I (fs.c i)).symm z with hy
  have hyO : y ∈ mfe_O fs x := hzO
  have hψ : fs i y = 1 := (mfe_O_props fs x).2.2.1 y hyO
  have hχ : (extChartAt I (fs.c i)) y = z :=
    (extChartAt I (fs.c i)).right_inv hzT
  have hupd := mfe_F_update fs a i v y
  rw [Function.comp_apply, Function.comp_apply, hupd, hψ, hχ, one_mul]

omit [I.Boundaryless] [SecondCountableTopology M] [Countable ι] in
/-- `F a` in chart coordinates is smooth on the target. -/
private lemma mfe_g_contDiffOn (x : M) (a : ι → (E →L[ℝ] ℝ)) :
    ContDiffOn ℝ ∞ ((mfe_F fs a) ∘ (extChartAt I (fs.c (mfe_idx fs x))).symm)
      (extChartAt I (fs.c (mfe_idx fs x))).target := by
  exact contMDiffOn_iff_contDiffOn.mp
    ((mfe_F_smooth fs a).comp_contMDiffOn
      (contMDiffOn_extChartAt_symm (fs.c (mfe_idx fs x))))

omit [SecondCountableTopology M] [Countable ι] in
/-- First derivative after updating the parameter. -/
private lemma mfe_update_D1 (x : M) [DecidableEq ι] (a : ι → (E →L[ℝ] ℝ))
    (v : E →L[ℝ] ℝ) (z : E) (hz : z ∈ mfe_Omega' fs x) :
    fderiv ℝ ((mfe_F fs (Function.update a (mfe_idx fs x) v)) ∘
      (extChartAt I (fs.c (mfe_idx fs x))).symm) z =
      fderiv ℝ ((mfe_F fs (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm) z + v := by
  have hOopen := mfe_Omega'_open fs x
  have hmem : mfe_Omega' fs x ∈ 𝓝 z := hOopen.mem_nhds hz
  have hevent : ((mfe_F fs (Function.update a (mfe_idx fs x) v)) ∘
      (extChartAt I (fs.c (mfe_idx fs x))).symm)
      =ᶠ[𝓝 z] (fun z' =>
        ((mfe_F fs (Function.update a (mfe_idx fs x) 0)) ∘
          (extChartAt I (fs.c (mfe_idx fs x))).symm) z' + v z') := by
    filter_upwards [hmem] with z' hz'
    exact mfe_update_Omega' fs x a v z' hz'
  rw [hevent.fderiv_eq]
  have hzT : z ∈ (extChartAt I (fs.c (mfe_idx fs x))).target := hz.1
  have hg_diff : DifferentiableAt ℝ ((mfe_F fs (Function.update a (mfe_idx fs x) 0)) ∘
      (extChartAt I (fs.c (mfe_idx fs x))).symm) z :=
    ((mfe_g_contDiffOn fs x _).contDiffAt
      ((isOpen_extChartAt_target _).mem_nhds hzT)).differentiableAt (by simp)
  exact (hg_diff.hasFDerivAt.add v.hasFDerivAt).fderiv

omit [SecondCountableTopology M] [Countable ι] in
/-- Second derivative after updating the parameter. -/
private lemma mfe_update_D2 (x : M) [DecidableEq ι] (a : ι → (E →L[ℝ] ℝ))
    (v : E →L[ℝ] ℝ) (z : E) (hz : z ∈ mfe_Omega' fs x) :
    fderiv ℝ (fderiv ℝ ((mfe_F fs (Function.update a (mfe_idx fs x) v)) ∘
      (extChartAt I (fs.c (mfe_idx fs x))).symm)) z =
      fderiv ℝ (fderiv ℝ ((mfe_F fs (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm)) z := by
  have hOopen := mfe_Omega'_open fs x
  have hmem : mfe_Omega' fs x ∈ 𝓝 z := hOopen.mem_nhds hz
  have hevent1 : fderiv ℝ ((mfe_F fs (Function.update a (mfe_idx fs x) v)) ∘
      (extChartAt I (fs.c (mfe_idx fs x))).symm)
      =ᶠ[𝓝 z] (fun z' =>
        fderiv ℝ ((mfe_F fs (Function.update a (mfe_idx fs x) 0)) ∘
          (extChartAt I (fs.c (mfe_idx fs x))).symm) z' + v) := by
    filter_upwards [hmem] with z' hz'
    rw [mfe_update_D1 fs x a v z' hz']
  rw [hevent1.fderiv_eq]
  have hzT : z ∈ (extChartAt I (fs.c (mfe_idx fs x))).target := hz.1
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ ((mfe_F fs
      (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm))
      (extChartAt I (fs.c (mfe_idx fs x))).target :=
    (mfe_g_contDiffOn fs x _).fderiv_of_isOpen (isOpen_extChartAt_target _) (by simp)
  have hg2_diff : DifferentiableAt ℝ (fderiv ℝ ((mfe_F fs
      (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm)) z :=
    (hDf.contDiffAt ((isOpen_extChartAt_target _).mem_nhds hzT)).differentiableAt
      (by simp)
  have hadd := hg2_diff.hasFDerivAt.add (hasFDerivAt_const v z)
  have hfin := hadd.fderiv
  rwa [add_zero] at hfin

/-- The dual has the same finrank. -/
private lemma mfe_finrank_dual :
    Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E)).symm.finrank_eq.trans
    Subspace.dual_finrank_eq

omit [SecondCountableTopology M] [Countable ι] in
/-- The Sard null set for the negated derivative map. -/
private lemma mfe_sard_null (x : M) [DecidableEq ι] (a : ι → (E →L[ℝ] ℝ)) :
    (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (E →L[ℝ] ℝ))
      ((fun z => -(fderiv ℝ ((mfe_F fs
      (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm) z)) ''
      {z | z ∈ mfe_Omega' fs x ∧ ¬ Function.Surjective
        (fderiv ℝ (fun z => -(fderiv ℝ ((mfe_F fs
          (Function.update a (mfe_idx fs x) 0)) ∘
            (extChartAt I (fs.c (mfe_idx fs x))).symm) z)) z)}) = 0 := by
  have hg := mfe_g_contDiffOn fs x (Function.update a (mfe_idx fs x) 0)
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ ((mfe_F fs
      (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm))
      (extChartAt I (fs.c (mfe_idx fs x))).target :=
    hg.fderiv_of_isOpen (isOpen_extChartAt_target _) (by simp)
  have hU : mfe_Omega' fs x ⊆ (extChartAt I (fs.c (mfe_idx fs x))).target :=
    fun z hz => hz.1
  have hneg : ContDiffOn ℝ ∞ (fun z => -(fderiv ℝ ((mfe_F fs
      (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm) z)) (mfe_Omega' fs x) :=
    (hD.mono hU).neg
  exact sard_euclidean_open E (E →L[ℝ] ℝ)
    (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (E →L[ℝ] ℝ))
    (mfe_Omega' fs x) (mfe_Omega'_open fs x) _ hneg

omit [SecondCountableTopology M] [Countable ι] in
/-- Every bad parameter value is a Sard critical value. -/
private lemma mfe_bad_mem_S (x : M) [DecidableEq ι] (a : ι → (E →L[ℝ] ℝ))
    (v : E →L[ℝ] ℝ)
    (hbadv : Function.update a (mfe_idx fs x) v ∉ mfe_Good fs x) :
    v ∈ (fun z => -(fderiv ℝ ((mfe_F fs (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm) z)) ''
      {z | z ∈ mfe_Omega' fs x ∧ ¬ Function.Surjective
        (fderiv ℝ (fun z => -(fderiv ℝ ((mfe_F fs
          (Function.update a (mfe_idx fs x) 0)) ∘
            (extChartAt I (fs.c (mfe_idx fs x))).symm) z)) z)} := by
  simp only [mfe_Good, Set.mem_ofPred_eq] at hbadv
  push Not at hbadv
  obtain ⟨y, hyK, hcrit, hndeg⟩ := hbadv
  set z := (extChartAt I (fs.c (mfe_idx fs x))) y with hz_def
  have hzm : z ∈ mfe_Omega' fs x := mfe_Omega'_mem fs x y hyK
  have hzT : z ∈ (extChartAt I (fs.c (mfe_idx fs x))).target := hzm.1
  have hD1 := mfe_update_D1 fs x a v z hzm
  have hD2 := mfe_update_D2 fs x a v z hzm
  have h0 : fderiv ℝ ((mfe_F fs (Function.update a (mfe_idx fs x) v)) ∘
      (extChartAt I (fs.c (mfe_idx fs x))).symm) z = 0 := hcrit
  have hv_eq : v = -(fderiv ℝ ((mfe_F fs (Function.update a (mfe_idx fs x) 0)) ∘
      (extChartAt I (fs.c (mfe_idx fs x))).symm) z) := by
    rw [hD1, add_comm] at h0
    exact eq_neg_of_add_eq_zero_left h0
  unfold mfe_nondeg at hndeg
  rw [hD2] at hndeg
  push Not at hndeg
  obtain ⟨u, hu, hne⟩ := hndeg
  have hker : (fderiv ℝ (fderiv ℝ ((mfe_F fs (Function.update a (mfe_idx fs x) 0)) ∘
      (extChartAt I (fs.c (mfe_idx fs x))).symm)) z) u = 0 :=
    ContinuousLinearMap.ext fun w => hu w
  have hninj : ¬ Function.Injective (fderiv ℝ (fderiv ℝ ((mfe_F fs
      (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm)) z) := by
    intro hinj
    exact hne (hinj (by rw [hker, map_zero]))
  have hnsurj : ¬ Function.Surjective (fderiv ℝ (fderiv ℝ ((mfe_F fs
      (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm)) z) := by
    intro hsurj
    apply hninj
    have hinj' : Function.Injective
        ⇑((fderiv ℝ (fderiv ℝ ((mfe_F fs (Function.update a (mfe_idx fs x) 0)) ∘
          (extChartAt I (fs.c (mfe_idx fs x))).symm)) z).toLinearMap) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        mfe_finrank_dual.symm).mpr hsurj
    exact hinj'
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ ((mfe_F fs
      (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm))
      (extChartAt I (fs.c (mfe_idx fs x))).target :=
    (mfe_g_contDiffOn fs x _).fderiv_of_isOpen (isOpen_extChartAt_target _) (by simp)
  have hg2_diff : DifferentiableAt ℝ (fderiv ℝ ((mfe_F fs
      (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm)) z :=
    (hDf.contDiffAt ((isOpen_extChartAt_target _).mem_nhds hzT)).differentiableAt
      (by simp)
  have hneg_deriv : fderiv ℝ (fun z => -(fderiv ℝ ((mfe_F fs
      (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm) z)) z =
      -(fderiv ℝ (fderiv ℝ ((mfe_F fs (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm)) z) :=
    (hg2_diff.hasFDerivAt.neg).fderiv
  have hnsurj_neg : ¬ Function.Surjective (fderiv ℝ (fun z => -(fderiv ℝ ((mfe_F fs
      (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm) z)) z) := by
    rw [hneg_deriv]
    intro hsurj_neg
    apply hnsurj
    intro w
    obtain ⟨t, ht⟩ := hsurj_neg (-w)
    refine ⟨t, neg_inj.mp ?_⟩
    have h2 : (-(fderiv ℝ (fderiv ℝ ((mfe_F fs
      (Function.update a (mfe_idx fs x) 0)) ∘
        (extChartAt I (fs.c (mfe_idx fs x))).symm)) z)) t = -w := ht
    rw [neg_apply] at h2
    exact h2
  exact ⟨z, ⟨hzm, hnsurj_neg⟩, hv_eq.symm⟩

omit [SecondCountableTopology M] [Countable ι] in
/-- `Good x` is dense. -/
private lemma mfe_Good_dense (x : M) : Dense (mfe_Good fs x) := by
  classical
  rw [dense_iff_inter_open]
  intro U hUopen hUne
  obtain ⟨a, ha⟩ := hUne
  set i := mfe_idx fs x with hi
  set V : Set (E →L[ℝ] ℝ) := {v | Function.update a i v ∈ U} with hV
  have hcont : Continuous (fun v : E →L[ℝ] ℝ => Function.update a i v) := by
    rw [continuous_pi_iff]
    intro j
    by_cases hji : j = i
    · subst hji
      have heq : (fun v : E →L[ℝ] ℝ => Function.update a i v i) = id := by
        funext v
        exact Function.update_self i v a
      rw [heq]
      exact continuous_id
    · have heq : (fun v : E →L[ℝ] ℝ => Function.update a i v j) =
          fun _ => a j := by
        funext v
        exact Function.update_of_ne hji _ _
      rw [heq]
      exact continuous_const
  have hVopen : IsOpen V := hUopen.preimage hcont
  have haiV : a i ∈ V := by
    change Function.update a i (a i) ∈ U
    rw [Function.update_eq_self]
    exact ha
  set S : Set (E →L[ℝ] ℝ) := (fun z => -(fderiv ℝ ((mfe_F fs
      (Function.update a i 0)) ∘ (extChartAt I (fs.c i)).symm) z)) ''
      {z | z ∈ mfe_Omega' fs x ∧ ¬ Function.Surjective
        (fderiv ℝ (fun z => -(fderiv ℝ ((mfe_F fs
          (Function.update a i 0)) ∘ (extChartAt I (fs.c i)).symm) z)) z)} with hS
  have hSnull : (MeasureTheory.Measure.addHaar :
      MeasureTheory.Measure (E →L[ℝ] ℝ)) S = 0 :=
    mfe_sard_null fs x a
  have hint : interior S = ∅ :=
    MeasureTheory.Measure.interior_eq_empty_of_null hSnull
  have hnotsub : ∃ v ∈ V, v ∉ S := by
    by_contra hcon
    push Not at hcon
    have hsub : V ⊆ S := fun v hv => hcon v hv
    have hVint : V ⊆ interior S := interior_maximal hsub hVopen
    have hne : (interior S).Nonempty := ⟨a i, hVint haiV⟩
    rw [hint] at hne
    exact Set.not_nonempty_empty hne
  obtain ⟨v, hvV, hvS⟩ := hnotsub
  have hvU : Function.update a i v ∈ U := hvV
  have hgood : Function.update a i v ∈ mfe_Good fs x := by
    by_contra hbadv
    exact hvS (mfe_bad_mem_S fs x a v hbadv)
  exact ⟨_, hvU, hgood⟩

/-- One parameter is good on every member of the countable compact cover. -/
private lemma mfe_exists_good :
    ∃ a : ι → (E →L[ℝ] ℝ), ∀ x ∈ mfe_T fs, a ∈ mfe_Good fs x := by
  let _ : Countable ↥(mfe_T fs) := (mfe_T_countable fs).to_subtype
  have hdense : Dense (⋂ x : ↥(mfe_T fs), mfe_Good fs x) :=
    dense_iInter_of_isOpen (fun x => mfe_Good_isOpen fs x) (fun x => mfe_Good_dense fs x)
  obtain ⟨a, ha⟩ := hdense.nonempty
  exact ⟨a, fun x hx => Set.mem_iInter.mp ha ⟨x, hx⟩⟩

end MFEparam

end MathlibExt.Geometry.Manifold.MorseExistenceWanted

@[expose] public section

/-!
# Existence of Morse functions

Wishlist global existence of a `C^∞` Morse function on every Hausdorff
second-countable boundaryless finite-dimensional real manifold.
-/

noncomputable section

open scoped Manifold ContDiff

namespace MathlibExt.Geometry.Manifold.MorseExistenceWanted

open MathlibExt.Geometry.Manifold.ReebSphereWanted

/--
Every Hausdorff second-countable boundaryless finite-dimensional `C^∞` manifold `M` admits a `C^∞`
Morse function `f : M → ℝ`. Source: J. Milnor, Morse Theory, Ann. of Math. Studies 51 (1963); M.
Hirsch, Differential Topology; J. Lee, Intro to Smooth Manifolds, 2nd ed.; Lean states
boundaryless finite-dimensional second-countable specialization.

Proves `Wanted` entry `morse_function_exists`.
-/
public theorem morse_function_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    : ∃ f : M → ℝ, IsMorseFunction (I := I) f := by
  obtain ⟨ι, hι, ⟨fs⟩⟩ := mfe_cover (I := I) (M := M)
  let _ : Countable ι := hι
  obtain ⟨a, ha⟩ := mfe_exists_good fs
  refine ⟨mfe_F fs a, ?_⟩
  unfold IsMorseFunction
  refine ⟨mfe_F_smooth fs a, fun p hp => ?_⟩
  have hpcover : p ∈ ⋃ x ∈ mfe_T fs, interior (mfe_K fs x) := by
    rw [mfe_T_cover fs]
    exact Set.mem_univ p
  simp only [Set.mem_iUnion] at hpcover
  obtain ⟨x, hxT, hpKint⟩ := hpcover
  have hpK : p ∈ mfe_K fs x := interior_subset hpKint
  have hpSource : p ∈ (extChartAt I (fs.c (mfe_idx fs x))).source :=
    (mfe_K_sub fs x).2 hpK
  have hcrit : mfe_crit (I := I) (mfe_F fs a) (fs.c (mfe_idx fs x)) p :=
    mfe_crit_of_mfderiv (mfe_F_smooth fs a) _ _ hpSource hp
  have hnd : mfe_nondeg (I := I) (mfe_F fs a) (fs.c (mfe_idx fs x)) p :=
    ha x hxT p hpK hcrit
  exact mfe_morse_at (mfe_F_smooth fs a) _ _ hpSource hcrit hnd

end MathlibExt.Geometry.Manifold.MorseExistenceWanted
