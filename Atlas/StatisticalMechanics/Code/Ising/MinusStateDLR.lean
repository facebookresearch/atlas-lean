/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Ising.IsingMinusTIFromPlacement

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal BoundedContinuousFunction

namespace StatMech.Ising

open StatMech.Lattice

variable {d : Nat}



theorem msdlr_finite_consistency {n m : Nat} (hnm : n <= m) (beta h : Real)
    (f : ConfigSpace (Site d) →ᵇ Real) :
    (∫ omega, specApply n (bondFinsetTouch d n) beta h
        (f : ConfigSpace (Site d) -> Real) omega
      ∂(minusMeasure d m beta h : Measure (ConfigSpace (Site d))))
      = ∫ omega, f omega
        ∂(minusMeasure d m beta h : Measure (ConfigSpace (Site d))) := by
  change (∫ omega, specApply n (bondFinsetTouch d n) beta h
      (f : ConfigSpace (Site d) -> Real) omega
    ∂(fvMeasure (minusField d) m (bondFinsetTouch d m) beta h))
    = ∫ omega, f omega
      ∂(fvMeasure (minusField d) m (bondFinsetTouch d m) beta h)
  rw [integral_fvMeasure_eq_sum (minusField d) m
      (bondFinsetTouch d m) beta h
      (specApply n (bondFinsetTouch d n) beta h
        (f : ConfigSpace (Site d) -> Real)),
    integral_fvMeasure_eq_sum (minusField d) m
      (bondFinsetTouch d m) beta h
      (f : ConfigSpace (Site d) -> Real)]
  simp only [specApply_eq_sum]
  exact consistency_double_sum hnm (minusField d) beta h
    (f : ConfigSpace (Site d) -> Real)


theorem msdlr_specApply_integral_eq (beta h : Real) (n : Nat)
    (f : ConfigSpace (Site d) →ᵇ Real) :
    ∫ omega, specApply n (bondFinsetTouch d n) beta h
        (f : ConfigSpace (Site d) -> Real) omega
        ∂(minusState d beta h : Measure (ConfigSpace (Site d)))
      = ∫ omega, f omega
        ∂(minusState d beta h : Measure (ConfigSpace (Site d))) := by
  obtain ⟨phi, hphi, hconv⟩ := minusState_isInfiniteVolumeState d beta h
  let g := specApply_bcf n (bondFinsetTouch d n) beta h f
  have hLg : Tendsto
      (fun k => ∫ omega, g omega
        ∂(minusMeasure d (phi k) beta h : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, g omega
        ∂(minusState d beta h : Measure (ConfigSpace (Site d))))) := by
    simpa [Function.comp] using hconv.tendsto_integral g
  have hLf : Tendsto
      (fun k => ∫ omega, f omega
        ∂(minusMeasure d (phi k) beta h : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, f omega
        ∂(minusState d beta h : Measure (ConfigSpace (Site d))))) := by
    simpa [Function.comp] using hconv.tendsto_integral f
  have hev : ∀ᶠ k in atTop,
      (∫ omega, g omega
        ∂(minusMeasure d (phi k) beta h : Measure (ConfigSpace (Site d))))
      = ∫ omega, f omega
        ∂(minusMeasure d (phi k) beta h : Measure (ConfigSpace (Site d))) := by
    have hge : ∀ᶠ k in atTop, n <= phi k :=
      hphi.tendsto_atTop.eventually_ge_atTop n
    filter_upwards [hge] with k hk
    exact msdlr_finite_consistency hk beta h f
  have heq := tendsto_nhds_unique (hLg.congr' hev) hLf
  simpa only [g, specApply_bcf_apply] using heq


theorem msdlr_bind_eq (beta h : Real) (n : Nat) :
    (isingSpecFull n (bondFinsetTouch d n) beta h) ∘ₘ
        (minusState d beta h : Measure (ConfigSpace (Site d)))
      = (minusState d beta h : Measure (ConfigSpace (Site d))) := by
  let mu : Measure (ConfigSpace (Site d)) := minusState d beta h
  let K := isingSpecFull n (bondFinsetTouch d n) beta h
  haveI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  haveI : IsProbabilityMeasure (K ∘ₘ mu) := by dsimp [K]; infer_instance
  have hfm : (⟨K ∘ₘ mu, inferInstance⟩ : FiniteMeasure (ConfigSpace (Site d)))
      = (⟨mu, inferInstance⟩ : FiniteMeasure (ConfigSpace (Site d))) := by
    refine FiniteMeasure.ext_of_forall_integral_eq (fun f => ?_)
    show ∫ y, f y ∂(K ∘ₘ mu) = ∫ y, f y ∂mu
    dsimp only [K]
    rw [integral_bind_specApply n (bondFinsetTouch d n) beta h mu f]
    exact msdlr_specApply_integral_eq beta h n f
  exact congrArg
    (fun nu : FiniteMeasure (ConfigSpace (Site d)) =>
      (nu : Measure (ConfigSpace (Site d)))) hfm



theorem compProd_rect_of_bind_eq (beta h : Real)
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu] (n : Nat)
    (hbind : (isingSpecFull n (bondFinsetTouch d n) beta h) ∘ₘ mu = mu)
    {s : Set (ConfigSpace (Site d))}
    (hs : MeasurableSet[outsideSigma (box d n)] s)
    {t : Set (ConfigSpace (Site d))} (ht : MeasurableSet t) :
    ((mu.trim (outsideSigma_le (box d n))) ⊗ₘ
        (isingSpec n (bondFinsetTouch d n) beta h)) (s ×ˢ t)
      = mu (s ∩ t) := by
  let hm := outsideSigma_le (box d n)
  let B := bondFinsetTouch d n
  haveI : SigmaFinite (mu.trim hm) := by
    haveI : IsFiniteMeasure (mu.trim hm) := ⟨by
      rw [trim_measurableSet_eq hm MeasurableSet.univ]
      exact measure_lt_top mu _⟩
    infer_instance
  rw [Measure.compProd_apply_prod hs ht]
  change ∫⁻ omega in s, (fvMeasure omega n B beta h) t ∂mu.trim hm
      = mu (s ∩ t)
  rw [setLIntegral_trim hm (meas_fvMeasure_coe n B beta h ht) hs]
  have hsfull : MeasurableSet s := hm s hs
  rw [← lintegral_indicator hsfull]
  have heq :
      (fun omega => Set.indicator s
          (fun omega => (fvMeasure omega n B beta h) t) omega)
        = fun omega => (fvMeasure omega n B beta h) (s ∩ t) := by
    funext omega
    by_cases homega : omega ∈ s
    · rw [Set.indicator_of_mem homega,
        fvMeasure_inter_outsideSigma n B beta h hs ht omega,
        Set.indicator_of_mem homega, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem homega,
        fvMeasure_inter_outsideSigma n B beta h hs ht omega,
        Set.indicator_of_notMem homega]
      simp
  rw [heq]
  have hbindapp : (isingSpecFull n B beta h ∘ₘ mu) (s ∩ t)
      = ∫⁻ omega, (fvMeasure omega n B beta h) (s ∩ t) ∂mu := by
    rw [Measure.bind_apply (hsfull.inter ht)
      (isingSpecFull n B beta h).aemeasurable]
    rfl
  rw [← hbindapp, hbind]


theorem compProd_trim_eq_of_bind_eq (beta h : Real)
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu] (n : Nat)
    (hbind : (isingSpecFull n (bondFinsetTouch d n) beta h) ∘ₘ mu = mu) :
    (mu.trim (outsideSigma_le (box d n))) ⊗ₘ
        (isingSpec n (bondFinsetTouch d n) beta h)
      = @Measure.map (ConfigSpace (Site d))
          (ConfigSpace (Site d) × ConfigSpace (Site d)) _
          ((outsideSigma (box d n)).prod inferInstance)
          (fun omega => (id omega, id omega)) mu := by
  let hm := outsideSigma_le (box d n)
  haveI : SigmaFinite (mu.trim hm) := by
    haveI : IsFiniteMeasure (mu.trim hm) := ⟨by
      rw [trim_measurableSet_eq hm MeasurableSet.univ]
      exact measure_lt_top mu _⟩
    infer_instance
  let K := isingSpec n (bondFinsetTouch d n) beta h
  haveI : IsMarkovKernel K :=
    isMarkov_isingSpec n (bondFinsetTouch d n) beta h
  have hcs : IsCountablySpanning
      {s : Set (ConfigSpace (Site d)) |
        MeasurableSet[outsideSigma (box d n)] s} :=
    ⟨fun _ => Set.univ, fun _ => Set.mem_setOf.mpr MeasurableSet.univ,
      by rw [Set.iUnion_const]⟩
  have hcs0 : IsCountablySpanning
      {t : Set (ConfigSpace (Site d)) | MeasurableSet t} :=
    ⟨fun _ => Set.univ, fun _ => Set.mem_setOf.mpr MeasurableSet.univ,
      by rw [Set.iUnion_const]⟩
  have hgenC : ((outsideSigma (box d n)).prod inferInstance)
      = generateFrom (Set.image2
          (fun a b : Set (ConfigSpace (Site d)) => a ×ˢ b)
          {s | MeasurableSet[outsideSigma (box d n)] s}
          {t | MeasurableSet t}) :=
    (@generateFrom_eq_prod (ConfigSpace (Site d))
      (ConfigSpace (Site d)) (outsideSigma (box d n)) inferInstance _ _
      (@generateFrom_measurableSet _ (outsideSigma (box d n)))
      (@generateFrom_measurableSet _ _) hcs hcs0).symm
  have hpiC : IsPiSystem (Set.image2
      (fun a b : Set (ConfigSpace (Site d)) => a ×ˢ b)
      {s | MeasurableSet[outsideSigma (box d n)] s}
      {t | MeasurableSet t}) :=
    @isPiSystem_prod (ConfigSpace (Site d)) (ConfigSpace (Site d))
      (outsideSigma (box d n)) _
  have hf : @Measurable (ConfigSpace (Site d))
      (ConfigSpace (Site d) × ConfigSpace (Site d)) inferInstance
      ((outsideSigma (box d n)).prod inferInstance)
      (fun omega => (id omega, id omega)) :=
    (measurable_id'' hm).prodMk measurable_id
  refine @Measure.ext_of_generateFrom_of_iUnion
    (ConfigSpace (Site d) × ConfigSpace (Site d))
    ((outsideSigma (box d n)).prod inferInstance) _ _ _
    (fun _ => Set.univ) hgenC hpiC (by rw [Set.iUnion_const])
    (fun _ => Set.mem_image2.mpr
      ⟨Set.univ, Set.mem_setOf.mpr MeasurableSet.univ,
        Set.univ, Set.mem_setOf.mpr MeasurableSet.univ, by simp⟩)
    (fun _ => ?_) (fun r hr => ?_)
  · exact (measure_lt_top ((mu.trim hm) ⊗ₘ K) _).ne
  · rw [Set.mem_image2] at hr
    obtain ⟨s, hs, t, ht, rfl⟩ := hr
    simp only [Set.mem_setOf_eq] at hs ht
    have hLeft : ((mu.trim hm) ⊗ₘ K) (s ×ˢ t) = mu (s ∩ t) :=
      compProd_rect_of_bind_eq beta h mu n hbind hs ht
    have hRight :
        (@Measure.map (ConfigSpace (Site d))
          (ConfigSpace (Site d) × ConfigSpace (Site d)) _
          ((outsideSigma (box d n)).prod inferInstance)
          (fun omega => (id omega, id omega)) mu) (s ×ˢ t)
          = mu (s ∩ t) := by
      rw [Measure.map_apply (μ := mu) hf
        (@MeasurableSet.prod _ _ (outsideSigma (box d n)) _ s t hs ht)]
      rfl
    rw [hLeft, hRight]



theorem isDLRState_of_specFull_bind_eq (beta h : Real)
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (hbind : ∀ n, (isingSpecFull n (bondFinsetTouch d n) beta h) ∘ₘ mu = mu) :
    IsDLRState d beta h mu :=
  isDLRState_of_compProd_trim beta h mu
    (fun n => compProd_trim_eq_of_bind_eq beta h mu n (hbind n))


theorem msdlr_minusState_isDLR_uncond (beta h : Real) :
    IsDLRState d beta h
      (minusState d beta h : Measure (ConfigSpace (Site d))) :=
  isDLRState_of_specFull_bind_eq beta h _ (msdlr_bind_eq beta h)

end StatMech.Ising
