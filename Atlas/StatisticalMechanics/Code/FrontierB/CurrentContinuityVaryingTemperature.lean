/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Code.FrontierB.CurrentContinuityMagnetizationFK
import Code.Ising.FreeStateDLR
import Mathlib.Topology.UniformSpace.CompactConvergence

open Filter MeasureTheory ProbabilityTheory MeasurableSpace Set Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction UniformConvergence

namespace StatMech.FrontierB

open ConfigSpace Ising Lattice

variable {d : Nat}



theorem continuous_fvWeight_beta_boundary
    (n : Nat) (B : Finset (Sym2 (Site d))) (h : Real)
    (tau : {x // x ∈ box d n} → Bool) :
    Continuous (fun z : Real × ConfigSpace (Site d) =>
      fvWeight z.2 n B z.1 h tau) := by
  unfold fvWeight
  exact Real.continuous_exp.comp
    (continuous_fst.neg.mul ((continuous_fvEnergy n B h tau).comp continuous_snd))

theorem continuous_fvZ_beta_boundary
    (n : Nat) (B : Finset (Sym2 (Site d))) (h : Real) :
    Continuous (fun z : Real × ConfigSpace (Site d) => fvZ z.2 n B z.1 h) := by
  unfold fvZ
  exact continuous_finsetSum _
    (fun tau _ => continuous_fvWeight_beta_boundary n B h tau)

theorem continuous_fvProb_beta_boundary
    (n : Nat) (B : Finset (Sym2 (Site d))) (h : Real)
    (tau : {x // x ∈ box d n} → Bool) :
    Continuous (fun z : Real × ConfigSpace (Site d) =>
      fvProb z.2 n B z.1 h tau) := by
  unfold fvProb
  exact (continuous_fvWeight_beta_boundary n B h tau).div
    (continuous_fvZ_beta_boundary n B h)
    (fun z => fvZ_ne_zero z.2 n B z.1 h)



theorem continuous_specApply_beta_boundary
    (n : Nat) (B : Finset (Sym2 (Site d))) (h : Real)
    (f : ConfigSpace (Site d) →ᵇ Real) :
    Continuous (fun z : Real × ConfigSpace (Site d) =>
      specApply n B z.1 h (f : ConfigSpace (Site d) → Real) z.2) := by
  have heq : (fun z : Real × ConfigSpace (Site d) =>
      specApply n B z.1 h (f : ConfigSpace (Site d) → Real) z.2) =
      fun z => ∑ tau : {x // x ∈ box d n} → Bool,
        fvProb z.2 n B z.1 h tau * f (glue z.2 tau) := by
    funext z
    exact specApply_eq_sum n B z.1 h f z.2
  rw [heq]
  exact continuous_finsetSum _ (fun tau _ =>
    (continuous_fvProb_beta_boundary n B h tau).mul
      (f.continuous.comp ((continuous_glue n tau).comp continuous_snd)))

noncomputable def specApplyBetaContinuousMap
    (n : Nat) (B : Finset (Sym2 (Site d))) (h : Real)
    (f : ConfigSpace (Site d) →ᵇ Real) :
    C(Real × ConfigSpace (Site d), Real) :=
  ⟨fun z => specApply n B z.1 h (f : ConfigSpace (Site d) → Real) z.2,
    continuous_specApply_beta_boundary n B h f⟩



theorem specApply_tendstoUniformly_beta
    (n : Nat) (B : Finset (Sym2 (Site d))) (h : Real)
    (f : ConfigSpace (Site d) →ᵇ Real)
    {betaSeq : Nat → Real} {beta : Real}
    (hbeta : Tendsto betaSeq atTop (nhds beta)) :
    TendstoUniformly
      (fun k omega => specApply n B (betaSeq k) h
        (f : ConfigSpace (Site d) → Real) omega)
      (fun omega => specApply n B beta h
        (f : ConfigSpace (Site d) → Real) omega) atTop := by
  let F := (specApplyBetaContinuousMap n B h f).curry
  have hF : Tendsto (fun k => F (betaSeq k)) atTop (nhds (F beta)) :=
    F.continuous.tendsto beta |>.comp hbeta
  have hu := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hF)
    Set.univ _root_.isCompact_univ
  simpa only [F, specApplyBetaContinuousMap, ContinuousMap.curry_apply,
    tendstoUniformlyOn_univ] using hu





theorem fvMeasure_specApply_integral_eq
    (eta : ConfigSpace (Site d)) {n m : Nat} (hnm : n ≤ m)
    (beta h : Real) (f : ConfigSpace (Site d) →ᵇ Real) :
    (∫ omega, specApply n (bondFinsetTouch d n) beta h
        (f : ConfigSpace (Site d) → Real) omega
      ∂(fvMeasure eta m (bondFinsetTouch d m) beta h)) =
      ∫ omega, f omega
        ∂(fvMeasure eta m (bondFinsetTouch d m) beta h) := by
  rw [integral_fvMeasure_eq_sum eta m (bondFinsetTouch d m) beta h
      (specApply n (bondFinsetTouch d n) beta h
        (f : ConfigSpace (Site d) → Real)),
    integral_fvMeasure_eq_sum eta m (bondFinsetTouch d m) beta h
      (f : ConfigSpace (Site d) → Real)]
  simp only [specApply_eq_sum]
  exact consistency_double_sum hnm eta beta h
    (f : ConfigSpace (Site d) → Real)





theorem integral_specApply_tendsto_of_beta_tendsto
    (mu : Nat → ProbabilityMeasure (ConfigSpace (Site d)))
    (muLim : ProbabilityMeasure (ConfigSpace (Site d)))
    (hmu : WeakConvergesTo mu muLim)
    {betaSeq : Nat → Real} {beta h : Real}
    (hbeta : Tendsto betaSeq atTop (nhds beta))
    (n : Nat) (f : ConfigSpace (Site d) →ᵇ Real) :
    Tendsto (fun k => ∫ omega,
        specApply n (bondFinsetTouch d n) (betaSeq k) h
          (f : ConfigSpace (Site d) → Real) omega
        ∂(mu k : Measure (ConfigSpace (Site d)))) atTop
      (nhds (∫ omega,
        specApply n (bondFinsetTouch d n) beta h
          (f : ConfigSpace (Site d) → Real) omega
        ∂(muLim : Measure (ConfigSpace (Site d))))) := by
  let g : ConfigSpace (Site d) →ᵇ Real :=
    specApply_bcf n (bondFinsetTouch d n) beta h f
  let gk : Nat → ConfigSpace (Site d) →ᵇ Real := fun k =>
    specApply_bcf n (bondFinsetTouch d n) (betaSeq k) h f
  have hfixed : Tendsto (fun k => ∫ omega, g omega
      ∂(mu k : Measure (ConfigSpace (Site d)))) atTop
      (nhds (∫ omega, g omega
        ∂(muLim : Measure (ConfigSpace (Site d))))) :=
    hmu.tendsto_integral g
  have hunif : TendstoUniformly (fun k omega => gk k omega)
      (fun omega => g omega) atTop := by
    simpa only [gk, g, specApply_bcf_apply] using
      specApply_tendstoUniformly_beta n (bondFinsetTouch d n) h f hbeta
  have hdiff : Tendsto (fun k =>
      (∫ omega, gk k omega ∂(mu k : Measure (ConfigSpace (Site d)))) -
        ∫ omega, g omega ∂(mu k : Measure (ConfigSpace (Site d))))
      atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    have heps2 : 0 < epsilon / 2 := half_pos hepsilon
    have hev := (Metric.tendstoUniformly_iff.mp hunif) (epsilon / 2) heps2
    rw [eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine ⟨N, fun k hkN => ?_⟩
    have hk := hN k hkN
    rw [dist_zero_right]
    rw [← integral_sub ((gk k).integrable (mu k)) (g.integrable (mu k))]
    calc
      |∫ omega, gk k omega - g omega
          ∂(mu k : Measure (ConfigSpace (Site d)))| ≤ epsilon / 2 := by
        simpa using norm_integral_le_of_norm_le_const
          (μ := (mu k : Measure (ConfigSpace (Site d))))
          (f := fun omega => gk k omega - g omega)
          (C := epsilon / 2) (Filter.Eventually.of_forall (fun omega => by
            simpa only [Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using
              (hk omega).le))
      _ < epsilon := half_lt_self hepsilon
  have hsum := hdiff.add hfixed
  simpa only [gk, g, specApply_bcf_apply, zero_add,
    sub_add_cancel] using hsum





theorem isingSpecFull_bind_eq_of_integral_eq
    (beta h : Real) (mu : Measure (ConfigSpace (Site d)))
    [IsProbabilityMeasure mu]
    (hinv : ∀ (n : Nat) (f : ConfigSpace (Site d) →ᵇ Real),
      (∫ omega, specApply n (bondFinsetTouch d n) beta h
          (f : ConfigSpace (Site d) → Real) omega ∂mu) =
        ∫ omega, f omega ∂mu)
    (n : Nat) :
    (isingSpecFull n (bondFinsetTouch d n) beta h) ∘ₘ mu = mu := by
  let K := isingSpecFull n (bondFinsetTouch d n) beta h
  haveI : IsProbabilityMeasure (K ∘ₘ mu) := by
    dsimp only [K]
    infer_instance
  have hfm : (⟨K ∘ₘ mu, inferInstance⟩ :
      FiniteMeasure (ConfigSpace (Site d))) =
      (⟨mu, inferInstance⟩ : FiniteMeasure (ConfigSpace (Site d))) := by
    refine FiniteMeasure.ext_of_forall_integral_eq (fun f => ?_)
    show ∫ y, f y ∂(K ∘ₘ mu) = ∫ y, f y ∂mu
    rw [integral_bind_specApply n (bondFinsetTouch d n) beta h mu f]
    exact hinv n f
  exact congrArg
    (fun nu : FiniteMeasure (ConfigSpace (Site d)) =>
      (nu : Measure (ConfigSpace (Site d)))) hfm



theorem compProd_rect_of_isingSpecFull_bind_eq
    (beta h : Real) (mu : Measure (ConfigSpace (Site d)))
    [IsProbabilityMeasure mu] (n : Nat)
    (hbind : (isingSpecFull n (bondFinsetTouch d n) beta h) ∘ₘ mu = mu)
    {s : Set (ConfigSpace (Site d))}
    (hs : MeasurableSet[outsideSigma (box d n)] s)
    {t : Set (ConfigSpace (Site d))} (ht : MeasurableSet t) :
    ((mu.trim (outsideSigma_le (box d n))) ⊗ₘ
        (isingSpec n (bondFinsetTouch d n) beta h)) (s ×ˢ t) =
      mu (s ∩ t) := by
  let hm := outsideSigma_le (box d n)
  let B := bondFinsetTouch d n
  haveI : SigmaFinite (mu.trim hm) := by
    haveI : IsFiniteMeasure (mu.trim hm) := ⟨by
      rw [trim_measurableSet_eq hm MeasurableSet.univ]
      exact measure_lt_top mu _⟩
    infer_instance
  rw [Measure.compProd_apply_prod hs ht]
  simp only [isingSpec_apply]
  rw [setLIntegral_trim hm (meas_fvMeasure_coe n B beta h ht) hs]
  have hsfull : MeasurableSet s := (outsideSigma_le (box d n)) s hs
  rw [← lintegral_indicator hsfull]
  have heq : (fun omega => Set.indicator s
      (fun omega => (fvMeasure omega n B beta h) t) omega) =
      (fun omega => (fvMeasure omega n B beta h) (s ∩ t)) := by
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
  have hbindapp : (isingSpecFull n B beta h ∘ₘ mu) (s ∩ t) =
      ∫⁻ omega, (fvMeasure omega n B beta h) (s ∩ t) ∂mu := by
    rw [Measure.bind_apply (((outsideSigma_le (box d n)) s hs).inter ht)
      (isingSpecFull n B beta h).aemeasurable]
    rfl
  rw [← hbindapp, hbind]



theorem isDLRState_of_specApply_integral_eq
    (beta h : Real) (mu : Measure (ConfigSpace (Site d)))
    [IsProbabilityMeasure mu]
    (hinv : ∀ (n : Nat) (f : ConfigSpace (Site d) →ᵇ Real),
      (∫ omega, specApply n (bondFinsetTouch d n) beta h
          (f : ConfigSpace (Site d) → Real) omega ∂mu) =
        ∫ omega, f omega ∂mu) :
    IsDLRState d beta h mu := by
  apply isDLRState_of_compProd_trim beta h mu
  intro n
  let hm := outsideSigma_le (box d n)
  let K := isingSpec n (bondFinsetTouch d n) beta h
  haveI : SigmaFinite (mu.trim hm) := by
    haveI : IsFiniteMeasure (mu.trim hm) := ⟨by
      rw [trim_measurableSet_eq hm MeasurableSet.univ]
      exact measure_lt_top mu _⟩
    infer_instance
  haveI : IsMarkovKernel K := isMarkov_isingSpec n
    (bondFinsetTouch d n) beta h
  have hbind := isingSpecFull_bind_eq_of_integral_eq beta h mu hinv n
  have hcs : IsCountablySpanning
      {s : Set (ConfigSpace (Site d)) |
        MeasurableSet[outsideSigma (box d n)] s} :=
    ⟨fun _ => Set.univ, fun _ => Set.mem_setOf.mpr MeasurableSet.univ,
      by rw [Set.iUnion_const]⟩
  have hcs0 : IsCountablySpanning
      {t : Set (ConfigSpace (Site d)) | MeasurableSet t} :=
    ⟨fun _ => Set.univ, fun _ => Set.mem_setOf.mpr MeasurableSet.univ,
      by rw [Set.iUnion_const]⟩
  have hgen : ((outsideSigma (box d n)).prod inferInstance) =
      generateFrom (Set.image2
        (fun a b : Set (ConfigSpace (Site d)) => a ×ˢ b)
        {s | MeasurableSet[outsideSigma (box d n)] s}
        {t | MeasurableSet t}) :=
    (@generateFrom_eq_prod (ConfigSpace (Site d)) (ConfigSpace (Site d))
      (outsideSigma (box d n)) inferInstance _ _
      (@generateFrom_measurableSet _ (outsideSigma (box d n)))
      (@generateFrom_measurableSet _ _) hcs hcs0).symm
  have hpi : IsPiSystem (Set.image2
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
    (fun _ => Set.univ) hgen hpi (by rw [Set.iUnion_const])
    (fun _ => Set.mem_image2.mpr
      ⟨Set.univ, Set.mem_setOf.mpr MeasurableSet.univ,
        Set.univ, Set.mem_setOf.mpr MeasurableSet.univ, by simp⟩)
    (fun _ => ?_) (fun r hr => ?_)
  · exact (measure_lt_top ((mu.trim hm) ⊗ₘ K) _).ne
  · rw [Set.mem_image2] at hr
    obtain ⟨s, hs, t, ht, rfl⟩ := hr
    simp only [Set.mem_setOf_eq] at hs ht
    have hleft : ((mu.trim hm) ⊗ₘ K) (s ×ˢ t) = mu (s ∩ t) :=
      compProd_rect_of_isingSpecFull_bind_eq beta h mu n hbind hs ht
    have hright : (@Measure.map (ConfigSpace (Site d))
        (ConfigSpace (Site d) × ConfigSpace (Site d)) _
        ((outsideSigma (box d n)).prod inferInstance)
        (fun omega => (id omega, id omega)) mu) (s ×ˢ t) =
        mu (s ∩ t) := by
      rw [Measure.map_apply (μ := mu) hf
        (@MeasurableSet.prod _ _ (outsideSigma (box d n)) _ s t hs ht)]
      rfl
    rw [hleft, hright]






theorem varyingFiniteGibbsWeakLimit_isDLR
    (eta : Nat → ConfigSpace (Site d)) (radius : Nat → Nat)
    (betaSeq : Nat → Real) (beta h : Real)
    (hradius : Tendsto radius atTop atTop)
    (hbeta : Tendsto betaSeq atTop (nhds beta))
    (muLim : ProbabilityMeasure (ConfigSpace (Site d)))
    (hweak : WeakConvergesTo
      (fun k => fvProbabilityMeasure (eta k) (radius k)
        (bondFinsetTouch d (radius k)) (betaSeq k) h) muLim) :
    IsDLRState d beta h (muLim : Measure (ConfigSpace (Site d))) := by
  apply isDLRState_of_specApply_integral_eq beta h
    (muLim : Measure (ConfigSpace (Site d)))
  intro n f
  let mu : Nat → ProbabilityMeasure (ConfigSpace (Site d)) := fun k =>
    fvProbabilityMeasure (eta k) (radius k)
      (bondFinsetTouch d (radius k)) (betaSeq k) h
  have hspec := integral_specApply_tendsto_of_beta_tendsto
    mu muLim (by simpa only [mu] using hweak) (h := h) hbeta n f
  have hf := (show WeakConvergesTo mu muLim by
    simpa only [mu] using hweak).tendsto_integral f
  have heq : ∀ᶠ k in atTop,
      (∫ omega, specApply n (bondFinsetTouch d n) (betaSeq k) h
          (f : ConfigSpace (Site d) → Real) omega
        ∂(mu k : Measure (ConfigSpace (Site d)))) =
        ∫ omega, f omega ∂(mu k : Measure (ConfigSpace (Site d))) := by
    have hge : ∀ᶠ k in atTop, n ≤ radius k :=
      hradius.eventually_ge_atTop n
    filter_upwards [hge] with k hk
    change (∫ omega, specApply n (bondFinsetTouch d n) (betaSeq k) h
        (f : ConfigSpace (Site d) → Real) omega
      ∂(fvMeasure (eta k) (radius k) (bondFinsetTouch d (radius k))
        (betaSeq k) h)) = _
    exact fvMeasure_specApply_integral_eq (eta k) hk (betaSeq k) h f
  exact tendsto_nhds_unique (hspec.congr' heq) hf



theorem varyingFreeGibbsWeakLimit_isDLR
    (radius : Nat → Nat) (betaSeq : Nat → Real) (beta h : Real)
    (hradius : Tendsto radius atTop atTop)
    (hbeta : Tendsto betaSeq atTop (nhds beta))
    (muLim : ProbabilityMeasure (ConfigSpace (Site d)))
    (hweak : WeakConvergesTo
      (fun k => freeMeasure d (radius k) (betaSeq k) h) muLim) :
    IsDLRState d beta h (muLim : Measure (ConfigSpace (Site d))) := by
  apply isDLRState_of_specApply_integral_eq beta h
    (muLim : Measure (ConfigSpace (Site d)))
  intro n f
  let mu : Nat → ProbabilityMeasure (ConfigSpace (Site d)) := fun k =>
    freeMeasure d (radius k) (betaSeq k) h
  have hweak' : WeakConvergesTo mu muLim := by simpa only [mu] using hweak
  have hspec := integral_specApply_tendsto_of_beta_tendsto
    mu muLim hweak' (h := h) hbeta n f
  have hf := hweak'.tendsto_integral f
  have heq : ∀ᶠ k in atTop,
      (∫ omega, specApply n (bondFinsetTouch d n) (betaSeq k) h
          (f : ConfigSpace (Site d) → Real) omega
        ∂(mu k : Measure (ConfigSpace (Site d)))) =
        ∫ omega, f omega ∂(mu k : Measure (ConfigSpace (Site d))) := by
    have hge : ∀ᶠ k in atTop, n + 1 ≤ radius k :=
      hradius.eventually_ge_atTop (n + 1)
    filter_upwards [hge] with k hk
    change (∫ omega, specApply n (bondFinsetTouch d n) (betaSeq k) h
        (f : ConfigSpace (Site d) → Real) omega
      ∂(freeMeasure d (radius k) (betaSeq k) h :
        Measure (ConfigSpace (Site d)))) = _
    exact freeMeasure_specApply_integral_eq hk (betaSeq k) h f
  exact tendsto_nhds_unique (hspec.congr' heq) hf



theorem freeState_isDLR (beta h : Real) :
    IsDLRState d beta h
      (freeState d beta h : Measure (ConfigSpace (Site d))) := by
  obtain ⟨phi, hphi, hweak⟩ := freeState_isInfiniteVolumeState d beta h
  apply varyingFreeGibbsWeakLimit_isDLR phi (fun _ => beta) beta h
  · exact hphi.tendsto_atTop
  · exact tendsto_const_nhds
  · simpa only [Function.comp_apply] using hweak



theorem currentContinuity_freeState_eq_minusState_of_freeLROZero
    (beta : Real) (hbeta0 : 0 < beta) (hd : 1 ≤ d)
    (hLRO : CurrentContinuityFreeLROZero d beta) :
    (freeState d beta 0 : Measure (ConfigSpace (Site d))) =
      (minusState d beta 0 : Measure (ConfigSpace (Site d))) :=
  currentContinuity_gibbs_unique_of_freeLROZero beta hbeta0 hd hLRO
    (freeState d beta 0 : Measure (ConfigSpace (Site d)))
    (freeState_isDLR beta 0)



theorem currentContinuity_plusState_eq_freeState_of_freeLROZero
    (beta : Real) (hbeta0 : 0 < beta) (hd : 1 ≤ d)
    (hLRO : CurrentContinuityFreeLROZero d beta) :
    (plusState d beta 0 : Measure (ConfigSpace (Site d))) =
      (freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
  calc
    (plusState d beta 0 : Measure (ConfigSpace (Site d))) =
        (minusState d beta 0 : Measure (ConfigSpace (Site d))) :=
      (currentContinuity_magnetization_and_phase_eq_of_freeLROZero
        beta hbeta0 hd hLRO).2
    _ = (freeState d beta 0 : Measure (ConfigSpace (Site d))) :=
      (currentContinuity_freeState_eq_minusState_of_freeLROZero
        beta hbeta0 hd hLRO).symm



theorem currentContinuity_allTwoPoint_eq_of_freeLROZero
    (beta : Real) (hbeta0 : 0 < beta) (hd : 1 ≤ d)
    (hLRO : CurrentContinuityFreeLROZero d beta) :
    ∀ x y : Site d,
      currentContinuityPlusTwoPoint d beta x y =
        currentContinuityFreeTwoPoint d beta x y := by
  intro x y
  unfold currentContinuityPlusTwoPoint currentContinuityFreeTwoPoint
  rw [currentContinuity_plusState_eq_freeState_of_freeLROZero
    beta hbeta0 hd hLRO]



theorem isingSpecFull_bind_eq_of_isDLRState
    (beta h : Real) (mu : Measure (ConfigSpace (Site d)))
    [IsProbabilityMeasure mu] (hmu : IsDLRState d beta h mu) (n : Nat) :
    (isingSpecFull n (bondFinsetTouch d n) beta h) ∘ₘ mu = mu := by
  let hm := outsideSigma_le (box d n)
  let K := isingSpec n (bondFinsetTouch d n) beta h
  haveI : SigmaFinite (mu.trim hm) := by
    haveI : IsFiniteMeasure (mu.trim hm) := ⟨by
      rw [trim_measurableSet_eq hm MeasurableSet.univ]
      exact measure_lt_top mu _⟩
    infer_instance
  ext t ht
  rw [Measure.bind_apply ht
    (isingSpecFull n (bondFinsetTouch d n) beta h).aemeasurable]
  change (∫⁻ omega, (fvMeasure omega n (bondFinsetTouch d n) beta h) t ∂mu) = _
  rw [← lintegral_trim hm (meas_fvMeasure_coe n
    (bondFinsetTouch d n) beta h ht)]
  have hcomp := dlr_compProd_trim_eq beta h mu hmu n
  have hrect := congrArg (fun nu : @Measure
      (ConfigSpace (Site d) × ConfigSpace (Site d))
      ((outsideSigma (box d n)).prod inferInstance) => nu (Set.univ ×ˢ t)) hcomp
  change ((mu.trim (outsideSigma_le (box d n))) ⊗ₘ
      (isingSpec n (bondFinsetTouch d n) beta h)) (Set.univ ×ˢ t) =
    (@Measure.map (ConfigSpace (Site d))
      (ConfigSpace (Site d) × ConfigSpace (Site d)) _
      ((outsideSigma (box d n)).prod inferInstance)
      (fun omega => (id omega, id omega)) mu) (Set.univ ×ˢ t) at hrect
  rw [Measure.compProd_apply_prod MeasurableSet.univ ht] at hrect
  have hf : @Measurable (ConfigSpace (Site d))
      (ConfigSpace (Site d) × ConfigSpace (Site d)) inferInstance
      ((outsideSigma (box d n)).prod inferInstance)
      (fun omega => (id omega, id omega)) :=
    (measurable_id'' hm).prodMk measurable_id
  rw [Measure.map_apply hf
    (@MeasurableSet.prod _ _ (outsideSigma (box d n)) _
      Set.univ t MeasurableSet.univ ht)] at hrect
  have hpre : (fun omega : ConfigSpace (Site d) => (id omega, id omega)) ⁻¹'
      (Set.univ ×ˢ t) = t := by ext omega; simp
  rw [hpre] at hrect
  simpa only [isingSpec_apply, setLIntegral_univ] using hrect



theorem specApply_integral_eq_of_isDLRState
    (beta h : Real) (mu : Measure (ConfigSpace (Site d)))
    [IsProbabilityMeasure mu] (hmu : IsDLRState d beta h mu)
    (n : Nat) (f : ConfigSpace (Site d) →ᵇ Real) :
    (∫ omega, specApply n (bondFinsetTouch d n) beta h
        (f : ConfigSpace (Site d) → Real) omega ∂mu) =
      ∫ omega, f omega ∂mu := by
  rw [← integral_bind_specApply n (bondFinsetTouch d n) beta h mu f,
    isingSpecFull_bind_eq_of_isDLRState beta h mu hmu n]



theorem varyingDLRWeakLimit_isDLR
    (mu : Nat → ProbabilityMeasure (ConfigSpace (Site d)))
    (betaSeq : Nat → Real) (beta h : Real)
    (hmu : ∀ k, IsDLRState d (betaSeq k) h
      (mu k : Measure (ConfigSpace (Site d))))
    (hbeta : Tendsto betaSeq atTop (nhds beta))
    (muLim : ProbabilityMeasure (ConfigSpace (Site d)))
    (hweak : WeakConvergesTo mu muLim) :
    IsDLRState d beta h (muLim : Measure (ConfigSpace (Site d))) := by
  apply isDLRState_of_specApply_integral_eq beta h
    (muLim : Measure (ConfigSpace (Site d)))
  intro n f
  have hspec := integral_specApply_tendsto_of_beta_tendsto
    mu muLim hweak (h := h) hbeta n f
  have hf := hweak.tendsto_integral f
  have heq : ∀ k,
      (∫ omega, specApply n (bondFinsetTouch d n) (betaSeq k) h
          (f : ConfigSpace (Site d) → Real) omega
        ∂(mu k : Measure (ConfigSpace (Site d)))) =
        ∫ omega, f omega ∂(mu k : Measure (ConfigSpace (Site d))) :=
    fun k => specApply_integral_eq_of_isDLRState
      (betaSeq k) h (mu k : Measure (ConfigSpace (Site d))) (hmu k) n f
  exact tendsto_nhds_unique
    (hspec.congr' (Filter.Eventually.of_forall heq)) hf






theorem currentContinuity_varyingDLR_tendsto_of_freeLROZero
    (beta : Real) (hbeta0 : 0 < beta) (hd : 1 ≤ d)
    (hLRO : CurrentContinuityFreeLROZero d beta)
    (mu : Nat → ProbabilityMeasure (ConfigSpace (Site d)))
    (betaSeq : Nat → Real)
    (hmu : ∀ k, IsDLRState d (betaSeq k) 0
      (mu k : Measure (ConfigSpace (Site d))))
    (hbeta : Tendsto betaSeq atTop (nhds beta)) :
    WeakConvergesTo mu (minusState d beta 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨nu, phi, hphi, hweak⟩ := prokhorov_seq_compact (mu ∘ ns)
  have hbetaSub : Tendsto (betaSeq ∘ ns ∘ phi) atTop (nhds beta) := by
    exact hbeta.comp (hns.comp hphi.tendsto_atTop)
  have hdlr : IsDLRState d beta 0
      (nu : Measure (ConfigSpace (Site d))) := by
    apply varyingDLRWeakLimit_isDLR (mu := mu ∘ ns ∘ phi)
      (betaSeq := betaSeq ∘ ns ∘ phi) (beta := beta) (h := 0)
    · intro k
      exact hmu (ns (phi k))
    · exact hbetaSub
    · simpa only [Function.comp_assoc] using hweak
  have hnuMeasure : (nu : Measure (ConfigSpace (Site d))) =
      (minusState d beta 0 : Measure (ConfigSpace (Site d))) :=
    currentContinuity_gibbs_unique_of_freeLROZero
      beta hbeta0 hd hLRO (nu : Measure _) hdlr
  have hnu : nu = minusState d beta 0 := by
    apply ProbabilityMeasure.toMeasure_injective
    exact hnuMeasure
  refine ⟨phi, ?_⟩
  simpa only [Function.comp_assoc, hnu] using hweak



theorem currentContinuity_varyingFiniteGibbs_tendsto_of_freeLROZero
    (beta : Real) (hbeta0 : 0 < beta) (hd : 1 ≤ d)
    (hLRO : CurrentContinuityFreeLROZero d beta)
    (eta : Nat → ConfigSpace (Site d)) (radius : Nat → Nat)
    (betaSeq : Nat → Real)
    (hradius : Tendsto radius atTop atTop)
    (hbeta : Tendsto betaSeq atTop (nhds beta)) :
    WeakConvergesTo
      (fun k => fvProbabilityMeasure (eta k) (radius k)
        (bondFinsetTouch d (radius k)) (betaSeq k) 0)
      (minusState d beta 0) := by
  let mu : Nat → ProbabilityMeasure (ConfigSpace (Site d)) := fun k =>
    fvProbabilityMeasure (eta k) (radius k)
      (bondFinsetTouch d (radius k)) (betaSeq k) 0
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨nu, phi, hphi, hweak⟩ := prokhorov_seq_compact (mu ∘ ns)
  have hcofinal : Tendsto (ns ∘ phi) atTop atTop :=
    hns.comp hphi.tendsto_atTop
  have hdlr : IsDLRState d beta 0
      (nu : Measure (ConfigSpace (Site d))) := by
    apply varyingFiniteGibbsWeakLimit_isDLR
      (eta := eta ∘ ns ∘ phi) (radius := radius ∘ ns ∘ phi)
      (betaSeq := betaSeq ∘ ns ∘ phi) (beta := beta) (h := 0)
    · exact hradius.comp hcofinal
    · exact hbeta.comp hcofinal
    · simpa only [mu, Function.comp_assoc] using hweak
  have hnuMeasure : (nu : Measure (ConfigSpace (Site d))) =
      (minusState d beta 0 : Measure (ConfigSpace (Site d))) :=
    currentContinuity_gibbs_unique_of_freeLROZero
      beta hbeta0 hd hLRO (nu : Measure _) hdlr
  have hnu : nu = minusState d beta 0 := by
    apply ProbabilityMeasure.toMeasure_injective
    exact hnuMeasure
  refine ⟨phi, ?_⟩
  simpa only [mu, Function.comp_assoc, hnu] using hweak



theorem currentContinuity_varyingDLR_localExpectation_tendsto
    (beta : Real) (hbeta0 : 0 < beta) (hd : 1 ≤ d)
    (hLRO : CurrentContinuityFreeLROZero d beta)
    (mu : Nat → ProbabilityMeasure (ConfigSpace (Site d)))
    (betaSeq : Nat → Real)
    (hmu : ∀ k, IsDLRState d (betaSeq k) 0
      (mu k : Measure (ConfigSpace (Site d))))
    (hbeta : Tendsto betaSeq atTop (nhds beta))
    (f : ConfigSpace (Site d) →ᵇ Real) :
    Tendsto (fun k => ∫ omega, f omega
      ∂(mu k : Measure (ConfigSpace (Site d)))) atTop
      (nhds (∫ omega, f omega
        ∂(minusState d beta 0 : Measure (ConfigSpace (Site d))))) :=
  (currentContinuity_varyingDLR_tendsto_of_freeLROZero
    beta hbeta0 hd hLRO mu betaSeq hmu hbeta).tendsto_integral f



theorem currentContinuity_varyingFiniteGibbs_localExpectation_tendsto
    (beta : Real) (hbeta0 : 0 < beta) (hd : 1 ≤ d)
    (hLRO : CurrentContinuityFreeLROZero d beta)
    (eta : Nat → ConfigSpace (Site d)) (radius : Nat → Nat)
    (betaSeq : Nat → Real)
    (hradius : Tendsto radius atTop atTop)
    (hbeta : Tendsto betaSeq atTop (nhds beta))
    (f : ConfigSpace (Site d) →ᵇ Real) :
    Tendsto (fun k => ∫ omega, f omega
      ∂(fvMeasure (eta k) (radius k) (bondFinsetTouch d (radius k))
        (betaSeq k) 0)) atTop
      (nhds (∫ omega, f omega
        ∂(minusState d beta 0 : Measure (ConfigSpace (Site d))))) :=
  (currentContinuity_varyingFiniteGibbs_tendsto_of_freeLROZero
    beta hbeta0 hd hLRO eta radius betaSeq hradius hbeta).tendsto_integral f

end StatMech.FrontierB
