/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.GibbsSimplex

/-!
# The plus state is a DLR state under finite-volume consistency

The Ising specification acting on bounded continuous functions, and the DLR property of the plus
state assuming consistency of the plus measures.

## i. Overview

The specification `η ↦ fvMeasure η n B β h` maps bounded continuous functions to bounded continuous
functions (Feller property). If the plus-boundary box measures are consistent with the specification
of every smaller box (`FVConsistency`), the consistency identity passes to the weak limit defining
the plus state, and the plus state is a DLR state. `FVConsistencyProve` proves the consistency
hypothesis.

## ii. Key results

- `StatMech.Ising.specApply` : the specification applied to a function
- `StatMech.Ising.specApply_bcf` : the Feller property
- `StatMech.Ising.FVConsistency` : consistency of the plus measures with the specification
- `StatMech.Ising.isingSpecFull` : the specification as a kernel on the full σ-algebra
- `StatMech.Ising.psdlr_plusState_isDLR` : the plus state is a DLR state under consistency

## iii. Table of contents

- A. The specification on functions
- B. Finite-volume consistency
- C. The specification as a kernel
- D. The DLR property in the limit

## iv. References

- H.-O. Georgii, *Gibbs Measures and Phase Transitions*, de Gruyter (1988; 2nd ed. 2011), Chapters
  1–4
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}

/-! ## A. The specification on functions -/

/-- The specification applied to `f`: `η ↦ ∫ f d(fvMeasure η n B β h)`. -/
noncomputable def specApply (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (f : ConfigSpace (Site d) → ℝ) (ω : ConfigSpace (Site d)) : ℝ :=
  ∫ y, f y ∂(fvMeasure ω n B β h)

lemma specApply_eq_sum (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (f : ConfigSpace (Site d) → ℝ) (ω : ConfigSpace (Site d)) :
    specApply n B β h f ω
      = ∑ τ : {x // x ∈ box d n} → Bool, fvProb ω n B β h τ * f (glue ω τ) := by
  unfold specApply fvMeasure
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (fvProb_nonneg ω n B β h τ)]
  · intro τ _
    exact (integrable_dirac (by simp [enorm_eq_nnnorm])).smul_measure (by simp)

lemma continuous_glue (n : ℕ) (τ : {x // x ∈ box d n} → Bool) :
    Continuous (fun ω : ConfigSpace (Site d) => glue ω τ) := by
  refine continuous_pi (fun x => ?_)
  by_cases hx : x ∈ box d n
  · simp only [glue, hx, dite_eq_left]; exact continuous_const
  · simp only [glue, hx, dite_eq_right, not_false_iff]; exact continuous_apply x

lemma continuous_spin_glue (n : ℕ) (τ : {x // x ∈ box d n} → Bool) (x : Site d) :
    Continuous (fun ω : ConfigSpace (Site d) => spin (glue ω τ) x) :=
  (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 : ℝ) else -1)).comp
    ((continuous_apply x).comp (continuous_glue n τ))

lemma continuous_bond_glue (n : ℕ) (τ : {x // x ∈ box d n} → Bool) (e : Sym2 (Site d)) :
    Continuous (fun ω : ConfigSpace (Site d) => bond (glue ω τ) e) := by
  induction e using Sym2.inductionOn with
  | hf x y => simp only [bond_mk]; exact (continuous_spin_glue n τ x).mul (continuous_spin_glue n τ
      y)

lemma continuous_fvEnergy (n : ℕ) (B : Finset (Sym2 (Site d))) (h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    Continuous (fun ω : ConfigSpace (Site d) => fvEnergy ω n B h τ) := by
  unfold fvEnergy
  refine Continuous.sub (Continuous.neg (continuous_finsetSum _ ?_))
    (Continuous.const_mul (continuous_finsetSum _ ?_) h)
  · intro e _; exact continuous_bond_glue n τ e
  · intro x _; exact continuous_spin_glue n τ x

lemma continuous_fvWeight (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    Continuous (fun ω : ConfigSpace (Site d) => fvWeight ω n B β h τ) := by
  unfold fvWeight
  exact Real.continuous_exp.comp ((continuous_fvEnergy n B h τ).const_mul (-β))

lemma continuous_fvZ (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    Continuous (fun ω : ConfigSpace (Site d) => fvZ ω n B β h) := by
  unfold fvZ
  exact continuous_finsetSum _ (fun τ _ => continuous_fvWeight n B β h τ)

lemma continuous_fvProb (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    Continuous (fun ω : ConfigSpace (Site d) => fvProb ω n B β h τ) := by
  unfold fvProb
  exact (continuous_fvWeight n B β h τ).div (continuous_fvZ n B β h)
    (fun ω => fvZ_ne_zero ω n B β h)

lemma specApply_continuous (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    {f : ConfigSpace (Site d) → ℝ} (hf : Continuous f) :
    Continuous (specApply n B β h f) := by
  have heq : specApply n B β h f
      = fun ω => ∑ τ : {x // x ∈ box d n} → Bool, fvProb ω n B β h τ * f (glue ω τ) := by
    funext ω; exact specApply_eq_sum n B β h f ω
  rw [heq]
  exact continuous_finsetSum _
    (fun τ _ => (continuous_fvProb n B β h τ).mul (hf.comp (continuous_glue n τ)))

/-- The specification applied to a bounded continuous function, as a bounded continuous function. -/
noncomputable def specApply_bcf (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (f : ConfigSpace (Site d) →ᵇ ℝ) : ConfigSpace (Site d) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨specApply n B β h (f : ConfigSpace (Site d) → ℝ), specApply_continuous n B β h f.continuous⟩

@[simp] lemma specApply_bcf_apply (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (f : ConfigSpace (Site d) →ᵇ ℝ) (ω : ConfigSpace (Site d)) :
    specApply_bcf n B β h f ω = specApply n B β h (f : ConfigSpace (Site d) → ℝ) ω := rfl

/-! ## B. Finite-volume consistency -/

/-- The plus measures in `Λ_m` are invariant under the specification in every `Λ_n ⊆ Λ_m`. -/
def FVConsistency (d : ℕ) (β h : ℝ) : Prop :=
  ∀ (n m : ℕ), n ≤ m → ∀ f : ConfigSpace (Site d) →ᵇ ℝ,
    ∫ ω, specApply n (bondFinsetTouch d n) β h (f : ConfigSpace (Site d) → ℝ) ω
        ∂(plusMeasure d m β h : Measure (ConfigSpace (Site d)))
      = ∫ ω, f ω ∂(plusMeasure d m β h : Measure (ConfigSpace (Site d)))

lemma psdlr_specApply_integral_eq (β h : ℝ) (hcons : FVConsistency d β h)
    (n : ℕ) (f : ConfigSpace (Site d) →ᵇ ℝ) :
    ∫ ω, specApply n (bondFinsetTouch d n) β h (f : ConfigSpace (Site d) → ℝ) ω
        ∂(plusState d β h : Measure (ConfigSpace (Site d)))
      = ∫ ω, f ω ∂(plusState d β h : Measure (ConfigSpace (Site d))) := by
  obtain ⟨φ, hφ, hconv⟩ := plusState_isInfiniteVolumeState d β h
  set g := specApply_bcf n (bondFinsetTouch d n) β h f with hg
  have hLg : Tendsto (fun k => ∫ ω, g ω ∂((fun m => plusMeasure d m β h) (φ k) : Measure
      (ConfigSpace (Site d))))
      atTop (𝓝 (∫ ω, g ω ∂(plusState d β h : Measure (ConfigSpace (Site d))))) := by
    have := (hconv.tendsto_integral g)
    simpa [Function.comp] using this
  have hLf : Tendsto (fun k => ∫ ω, f ω ∂((fun m => plusMeasure d m β h) (φ k) : Measure
      (ConfigSpace (Site d))))
      atTop (𝓝 (∫ ω, f ω ∂(plusState d β h : Measure (ConfigSpace (Site d))))) := by
    have := (hconv.tendsto_integral f)
    simpa [Function.comp] using this
  have hev : ∀ᶠ k in atTop,
      (fun k => ∫ ω, g ω ∂((fun m => plusMeasure d m β h) (φ k) : Measure (ConfigSpace (Site d)))) k
        = (fun k => ∫ ω, f ω ∂((fun m => plusMeasure d m β h) (φ k) : Measure (ConfigSpace (Site
            d)))) k := by
    have hge : ∀ᶠ k in atTop, n ≤ φ k := by
      have : Tendsto φ atTop atTop := hφ.tendsto_atTop
      exact this.eventually_ge_atTop n
    filter_upwards [hge] with k hk
    simp only [hg, specApply_bcf_apply]
    exact hcons n (φ k) hk f
  have : (∫ ω, g ω ∂(plusState d β h : Measure (ConfigSpace (Site d))))
      = (∫ ω, f ω ∂(plusState d β h : Measure (ConfigSpace (Site d)))) :=
    tendsto_nhds_unique (hLg.congr' hev) hLf
  simpa only [hg, specApply_bcf_apply] using this

/-! ## C. The specification as a kernel -/

/-- The Ising specification in `Λ_n` as a Markov kernel on the full σ-algebra. -/
noncomputable def isingSpecFull (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    Kernel (ConfigSpace (Site d)) (ConfigSpace (Site d)) :=
  Kernel.mk (fun η => fvMeasure η n B β h)
    (Measure.measurable_of_measurable_coe _
      (fun _ hs => (meas_fvMeasure_coe n B β h hs).mono (outsideSigma_le (box d n)) le_rfl))

@[simp] lemma isingSpecFull_apply (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (η : ConfigSpace (Site d)) :
    (isingSpecFull n B β h) η = fvMeasure η n B β h := rfl

/-- The full Ising specification is a Markov kernel. -/
instance isMarkov_isingSpecFull (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    IsMarkovKernel (isingSpecFull n B β h) :=
  ⟨fun η => by rw [isingSpecFull_apply]; exact fvMeasure_isProbabilityMeasure η n B β h⟩

lemma integral_bind_specApply (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (μ : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure μ]
    (f : ConfigSpace (Site d) →ᵇ ℝ) :
    ∫ y, f y ∂((isingSpecFull n B β h) ∘ₘ μ)
      = ∫ ω, specApply n B β h (f : ConfigSpace (Site d) → ℝ) ω ∂μ := by
  set K := isingSpecFull n B β h with hK
  have hbind : K ∘ₘ μ = (μ ⊗ₘ K).map Prod.snd := by
    rw [← Measure.snd_compProd μ K, Measure.snd]
  rw [hbind]
  rw [integral_map measurable_snd.aemeasurable
    (f.continuous.aestronglyMeasurable)]
  rw [Measure.integral_compProd]
  · refine integral_congr_ae (Eventually.of_forall (fun ω => ?_))
    change ∫ b, f b ∂(K ω) = specApply n B β h (f : ConfigSpace (Site d) → ℝ) ω
    rw [hK, isingSpecFull_apply]
    rfl
  · exact (BoundedContinuousFunction.integrable (μ ⊗ₘ K) (f.compContinuous ⟨Prod.snd,
      continuous_snd⟩))

lemma psdlr_bind_eq (β h : ℝ) (hcons : FVConsistency d β h) (n : ℕ) :
    (isingSpecFull n (bondFinsetTouch d n) β h) ∘ₘ (plusState d β h : Measure (ConfigSpace (Site
        d)))
      = (plusState d β h : Measure (ConfigSpace (Site d))) := by
  set μ := (plusState d β h : Measure (ConfigSpace (Site d))) with hμ
  set K := isingSpecFull n (bondFinsetTouch d n) β h with hK
  have : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have : IsProbabilityMeasure (K ∘ₘ μ) := by
    rw [hK]; infer_instance
  have hfm : (⟨K ∘ₘ μ, inferInstance⟩ : FiniteMeasure (ConfigSpace (Site d)))
      = (⟨μ, inferInstance⟩ : FiniteMeasure (ConfigSpace (Site d))) := by
    refine FiniteMeasure.ext_of_forall_integral_eq (fun f => ?_)
    change ∫ y, f y ∂(K ∘ₘ μ) = ∫ y, f y ∂μ
    rw [integral_bind_specApply n (bondFinsetTouch d n) β h μ f]
    exact psdlr_specApply_integral_eq β h hcons n f
  have := congrArg (fun ν : FiniteMeasure (ConfigSpace (Site d)) => (ν : Measure (ConfigSpace (Site
      d)))) hfm
  simpa using this

/-! ## D. The DLR property in the limit -/

/-- The σ-algebra of events determined by the spins outside `Λ`. -/
@[reducible] def outsideInvariantMS {E : Type*} (Λ : Set E) : MeasurableSpace (ConfigSpace E) where
  MeasurableSet' s := ∀ ω ω' : ConfigSpace E, (∀ x ∉ Λ, ω x = ω' x) → (ω ∈ s ↔ ω' ∈ s)
  measurableSet_empty := by simp
  measurableSet_compl s hs ω ω' h := by simp only [Set.mem_compl_iff]; rw [hs ω ω' h]
  measurableSet_iUnion f hf ω ω' h := by
    simp only [Set.mem_iUnion]; exact exists_congr (fun i => hf i ω ω' h)

lemma outsideSigma_le_invariant {E : Type*} [Countable E] (Λ : Set E) :
    outsideSigma Λ ≤ outsideInvariantMS Λ := by
  refine iSup₂_le (fun e he => ?_)
  rintro s ⟨t, _, rfl⟩ ω ω' hagree
  have : ω e = ω' e := hagree e he
  simp only [Set.mem_preimage, ConfigSpace.eval]
  rw [this]

lemma glue_mem_iff_of_outsideSigma (n : ℕ) {s : Set (ConfigSpace (Site d))}
    (hs : MeasurableSet[outsideSigma (box d n)] s) (ω : ConfigSpace (Site d))
    (τ : {x // x ∈ box d n} → Bool) :
    glue ω τ ∈ s ↔ ω ∈ s :=
  (outsideSigma_le_invariant (box d n) s hs) (glue ω τ) ω
    (fun x hx => by rw [glue_not_mem ω τ hx])

lemma fvMeasure_apply_eq_sum (ω : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) {t : Set (ConfigSpace (Site d))}
    (ht : MeasurableSet t) :
    (fvMeasure ω n B β h) t
      = ∑ τ : {x // x ∈ box d n} → Bool,
          ENNReal.ofReal (fvProb ω n B β h τ) * (Set.indicator t (1 : ConfigSpace (Site d) → ℝ≥0∞)
              (glue ω τ)) := by
  unfold fvMeasure
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ ht]

lemma fvMeasure_inter_outsideSigma (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    {s : Set (ConfigSpace (Site d))} (hs : MeasurableSet[outsideSigma (box d n)] s)
    {t : Set (ConfigSpace (Site d))} (ht : MeasurableSet t) (ω : ConfigSpace (Site d)) :
    (fvMeasure ω n B β h) (s ∩ t)
      = (Set.indicator s (1 : ConfigSpace (Site d) → ℝ≥0∞) ω) * (fvMeasure ω n B β h) t := by
  have hst : MeasurableSet (s ∩ t) := ((outsideSigma_le (box d n)) s hs).inter ht
  rw [fvMeasure_apply_eq_sum ω n B β h hst, fvMeasure_apply_eq_sum ω n B β h ht,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  have hloc : glue ω τ ∈ s ↔ ω ∈ s := glue_mem_iff_of_outsideSigma n hs ω τ
  by_cases hωs : ω ∈ s
  · have hglue_s : glue ω τ ∈ s := hloc.mpr hωs
    rw [Set.indicator_of_mem hωs, Pi.one_apply, one_mul]
    congr 1
    by_cases hglue_t : glue ω τ ∈ t
    · rw [Set.indicator_of_mem (show glue ω τ ∈ s ∩ t from ⟨hglue_s, hglue_t⟩),
        Set.indicator_of_mem hglue_t]
    · rw [Set.indicator_of_notMem (show glue ω τ ∉ s ∩ t from fun hc => hglue_t hc.2),
        Set.indicator_of_notMem hglue_t]
  · have hglue_s : glue ω τ ∉ s := fun hc => hωs (hloc.mp hc)
    rw [Set.indicator_of_notMem hωs,
      Set.indicator_of_notMem (show glue ω τ ∉ s ∩ t from fun hc => hglue_s hc.1)]
    simp

lemma psdlr_compProd_rect (β h : ℝ) (hcons : FVConsistency d β h) (n : ℕ)
    {s : Set (ConfigSpace (Site d))} (hs : MeasurableSet[outsideSigma (box d n)] s)
    {t : Set (ConfigSpace (Site d))} (ht : MeasurableSet t) :
    (((plusState d β h : Measure (ConfigSpace (Site d))).trim (outsideSigma_le (box d n)))
        ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h)) (s ×ˢ t)
      = (plusState d β h : Measure (ConfigSpace (Site d))) (s ∩ t) := by
  set μ := (plusState d β h : Measure (ConfigSpace (Site d))) with hμ
  set hm := outsideSigma_le (box d n) with hmdef
  set B := bondFinsetTouch d n with hB
  have : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have : SigmaFinite (μ.trim hm) := by
    have : IsFiniteMeasure (μ.trim hm) := ⟨by
      rw [trim_measurableSet_eq hm MeasurableSet.univ]; exact measure_lt_top μ _⟩
    infer_instance
  rw [Measure.compProd_apply_prod hs ht]
  have hker : ∀ ω, (isingSpec n B β h) ω t = (fvMeasure ω n B β h) t :=
    fun ω => by rw [isingSpec_apply]
  simp_rw [hker]
  rw [setLIntegral_trim hm (meas_fvMeasure_coe n B β h ht) hs]
  have hsfull : MeasurableSet s := (outsideSigma_le (box d n)) s hs
  rw [← lintegral_indicator hsfull]
  have heq : (fun ω => Set.indicator s (fun ω => (fvMeasure ω n B β h) t) ω)
      = (fun ω => (fvMeasure ω n B β h) (s ∩ t)) := by
    funext ω
    by_cases hωs : ω ∈ s
    · rw [Set.indicator_of_mem hωs, fvMeasure_inter_outsideSigma n B β h hs ht ω,
        Set.indicator_of_mem hωs, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem hωs, fvMeasure_inter_outsideSigma n B β h hs ht ω,
        Set.indicator_of_notMem hωs]
      simp
  rw [heq]
  have hbindapp : (isingSpecFull n B β h ∘ₘ μ) (s ∩ t)
      = ∫⁻ ω, (fvMeasure ω n B β h) (s ∩ t) ∂μ := by
    rw [Measure.bind_apply (((outsideSigma_le (box d n)) s hs).inter ht)
      (isingSpecFull n B β h).aemeasurable]
    rfl
  rw [← hbindapp, psdlr_bind_eq β h hcons n]

lemma psdlr_compProd_trim_eq (β h : ℝ) (hcons : FVConsistency d β h) (n : ℕ) :
    ((plusState d β h : Measure (ConfigSpace (Site d))).trim (outsideSigma_le (box d n)))
        ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h)
      = @Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _
          ((outsideSigma (box d n)).prod inferInstance) (fun ω ↦ (id ω, id ω))
          (plusState d β h : Measure (ConfigSpace (Site d))) := by
  set μ := (plusState d β h : Measure (ConfigSpace (Site d))) with hμ
  set hm := outsideSigma_le (box d n) with hmdef
  have : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have : SigmaFinite (μ.trim hm) := by
    have : IsFiniteMeasure (μ.trim hm) := ⟨by
      rw [trim_measurableSet_eq hm MeasurableSet.univ]; exact measure_lt_top μ _⟩
    infer_instance
  set K := isingSpec n (bondFinsetTouch d n) β h with hK
  have : IsMarkovKernel K := isMarkov_isingSpec n (bondFinsetTouch d n) β h
  have hcs : IsCountablySpanning {s : Set (ConfigSpace (Site d)) | MeasurableSet[outsideSigma (box d
      n)] s} :=
    ⟨fun _ => Set.univ, fun _ => Set.mem_ofPred.mpr MeasurableSet.univ, by rw [Set.iUnion_const]⟩
  have hcs0 : IsCountablySpanning {t : Set (ConfigSpace (Site d)) | MeasurableSet t} :=
    ⟨fun _ => Set.univ, fun _ => Set.mem_ofPred.mpr MeasurableSet.univ, by rw [Set.iUnion_const]⟩
  have hgenC : ((outsideSigma (box d n)).prod inferInstance)
      = generateFrom (Set.image2 (fun a b : Set (ConfigSpace (Site d)) => a ×ˢ b)
          {s | MeasurableSet[outsideSigma (box d n)] s} {t | MeasurableSet t}) :=
    (@generateFrom_eq_prod (ConfigSpace (Site d)) (ConfigSpace (Site d))
      (outsideSigma (box d n)) inferInstance _ _
      (@generateFrom_measurableSet _ (outsideSigma (box d n))) (@generateFrom_measurableSet _ _)
      hcs hcs0).symm
  have hpiC : IsPiSystem (Set.image2 (fun a b : Set (ConfigSpace (Site d)) => a ×ˢ b)
      {s | MeasurableSet[outsideSigma (box d n)] s} {t | MeasurableSet t}) :=
    @isPiSystem_prod (ConfigSpace (Site d)) (ConfigSpace (Site d)) (outsideSigma (box d n)) _
  have hf : @Measurable (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d))
      inferInstance ((outsideSigma (box d n)).prod inferInstance) (fun ω => (id ω, id ω)) :=
    (measurable_id'' hm).prodMk measurable_id
  refine @Measure.ext_of_generateFrom_of_iUnion (ConfigSpace (Site d) × ConfigSpace (Site d))
    ((outsideSigma (box d n)).prod inferInstance) _ _ _ (fun _ => Set.univ) hgenC hpiC
    (by rw [Set.iUnion_const])
    (fun _ => Set.mem_image2.mpr
      ⟨Set.univ, Set.mem_ofPred.mpr MeasurableSet.univ, Set.univ,
        Set.mem_ofPred.mpr MeasurableSet.univ, by simp⟩)
    (fun _ => ?_) (fun r hr => ?_)
  · exact (measure_lt_top ((μ.trim hm) ⊗ₘ K) _).ne
  · rw [Set.mem_image2] at hr
    obtain ⟨s, hs, t, ht, rfl⟩ := hr
    simp only [Set.mem_ofPred_eq] at hs ht
    have hLeft : ((μ.trim hm) ⊗ₘ K) (s ×ˢ t) = μ (s ∩ t) :=
      psdlr_compProd_rect β h hcons n hs ht
    have hRight : (@Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d))
        _
        ((outsideSigma (box d n)).prod inferInstance) (fun ω ↦ (id ω, id ω)) μ) (s ×ˢ t)
        = μ (s ∩ t) := by
      rw [Measure.map_apply (μ := μ) hf
        (@MeasurableSet.prod _ _ (outsideSigma (box d n)) _ s t hs ht)]
      rfl
    rw [hLeft, hRight]

lemma psdlr_plusState_isDLR (β h : ℝ) (hcons : FVConsistency d β h) :
    IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))) :=
  isDLRState_of_compProd_trim β h _ (fun n => psdlr_compProd_trim_eq β h hcons n)

end Ising

end StatMech

