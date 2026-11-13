/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































































import Code.FK.IntegralShiftDecay
import Code.FK.DensityFiniteToInfinite
import Code.FK.FKUniquenessClose

open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice

namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}











noncomputable def idc_coordCM (e : Sym2 (Site d)) : C(ConfigSpace (Sym2 (Site d)), ℝ) :=
  ⟨fun ω => if ω e then (1 : ℝ) else 0,
    (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 : ℝ) else 0)).comp
      (ConfigSpace.continuous_eval e)⟩

@[simp] theorem idc_coordCM_apply (e : Sym2 (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    idc_coordCM e ω = if ω e then (1 : ℝ) else 0 := rfl



noncomputable def idc_coordBcf (e : Sym2 (Site d)) : ConfigSpace (Sym2 (Site d)) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact (idc_coordCM e)

@[simp] theorem idc_coordBcf_apply (e : Sym2 (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    idc_coordBcf e ω = if ω e then (1 : ℝ) else 0 := rfl



theorem idc_openEdgeEvent_measurable (e : Sym2 (Site d)) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} := by
  have hpre : {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} = (fun ω => ω e) ⁻¹' {true} := by
    ext ω; simp
  rw [hpre]
  exact (measurable_pi_apply e) (measurableSet_singleton true)










theorem idc_integral_coordBcf (e : Sym2 (Site d)) (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsFiniteMeasure μ] :
    (∫ ω, idc_coordBcf e ω ∂μ) = μ.real {ω | ω e = true} := by
  have heq : (fun ω => idc_coordBcf e ω)
      = Set.indicator {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [idc_coordBcf_apply, Set.indicator]
    by_cases h : ω e <;> simp [h, Set.mem_setOf_eq]
  rw [heq, MeasureTheory.integral_indicator_const (1 : ℝ) (idc_openEdgeEvent_measurable e)]
  simp



theorem idc_openEdge_eq_boxRestrict (N : ℕ) (eb : Sym2 (boxVerts d N)) :
    {ω : ConfigSpace (Sym2 (Site d)) | ω (edgeIncl d N eb) = true}
      = boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb) := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage, boxEdgeOpenEvent, boxRestrict]








theorem idc_integral_coordBcf_wired (N m : ℕ) (hNm : N ≤ m) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∫ ω, idc_coordBcf (edgeIncl d N eb) ω
        ∂((wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : ProbabilityMeasure _) : Measure _))
      = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (innerEdgeLE d hNm eb) := by
  rw [idc_integral_coordBcf, idc_openEdge_eq_boxRestrict,
    dfi_wired_finite_mass_eq_edgeMarg N m hNm eb hp hp1]




theorem idc_integral_coordBcf_free (N m : ℕ) (hNm : N ≤ m) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∫ ω, idc_coordBcf (edgeIncl d N eb) ω
        ∂((freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : ProbabilityMeasure _) : Measure _))
      = edgeMargProb (fkProb (boxGraph d m) p 2) (innerEdgeLE d hNm eb) := by
  rw [idc_integral_coordBcf, idc_openEdge_eq_boxRestrict,
    dfi_free_finite_mass_eq_edgeMarg N m hNm eb hp hp1]










theorem idc_coordBcf_comp_shift (e : Sym2 (Site d)) (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) :
    idc_coordBcf e (shift g ω) = idc_coordBcf (g⁻¹ • e) ω := rfl






theorem idc_decayFun_coord (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (e : Sym2 (Site d)) (n : ℕ) :
    isd_decayFun μ g (idc_coordBcf e) n
      = ((μ n : Measure (ConfigSpace (Sym2 (Site d)))).real {ω | ω e = true})
        - ((μ n : Measure (ConfigSpace (Sym2 (Site d)))).real {ω | ω (g⁻¹ • e) = true}) := by
  unfold isd_decayFun
  rw [idc_integral_coordBcf e]
  congr 1
  rw [show (fun ω => idc_coordBcf e (shift g ω)) = (fun ω => idc_coordBcf (g⁻¹ • e) ω) from
    funext (fun ω => idc_coordBcf_comp_shift e g ω)]
  rw [idc_integral_coordBcf (g⁻¹ • e)]

























theorem idc_wired_coord_decay_of_density_eq (N : ℕ) (eb eb' : Sym2 (boxVerts d N))
    (g : Multiplicative (Site d)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hshift : g⁻¹ • (edgeIncl d N eb) = edgeIncl d N eb')
    (hdens : wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb') p) :
    Tendsto (isd_decayFun (fun m => wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2))
        g (idc_coordBcf (edgeIncl d N eb))) atTop (𝓝 0) := by
  
  have h1 : Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real {ω | ω (edgeIncl d N eb) = true})
      atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb) p)) :=
    wiredEdgeDensity_q2_tendsto d N eb hp hp1
  
  have h2 : Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real {ω | ω (edgeIncl d N eb') = true})
      atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb') p)) :=
    wiredEdgeDensity_q2_tendsto d N eb' hp hp1
  
  have hdecayeq : isd_decayFun (fun m => wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2))
        g (idc_coordBcf (edgeIncl d N eb))
      = fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real {ω | ω (edgeIncl d N eb) = true}
        - (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real {ω | ω (edgeIncl d N eb') = true} := by
    funext m
    rw [idc_decayFun_coord]
    rw [hshift]
  
  rw [hdecayeq]
  have := h1.sub h2
  rw [hdens, sub_self] at this
  exact this










noncomputable def idc_cylinderAlg (d : ℕ) : Subalgebra ℝ C(ConfigSpace (Sym2 (Site d)), ℝ) :=
  Algebra.adjoin ℝ (Set.range (idc_coordCM (d := d)))




theorem idc_cylinderAlg_separatesPoints (d : ℕ) :
    (idc_cylinderAlg d).SeparatesPoints := by
  rintro ω₁ ω₂ hne
  obtain ⟨e, he⟩ : ∃ e, ω₁ e ≠ ω₂ e := by
    by_contra hc
    exact hne (funext fun e => not_not.mp (fun h => hc ⟨e, h⟩))
  refine ⟨(idc_coordCM e : ConfigSpace (Sym2 (Site d)) → ℝ),
    ⟨idc_coordCM e, Algebra.subset_adjoin ⟨e, rfl⟩, rfl⟩, ?_⟩
  simp only [idc_coordCM_apply]
  intro hcontra
  apply he
  by_cases h1 : ω₁ e <;> by_cases h2 : ω₂ e <;> simp_all



noncomputable def idc_cylinderBcfSet (d : ℕ) : Set (ConfigSpace (Sym2 (Site d)) →ᵇ ℝ) :=
  BoundedContinuousFunction.mkOfCompact ''
    (idc_cylinderAlg d : Set C(ConfigSpace (Sym2 (Site d)), ℝ))





theorem idc_cylinderBcfSet_dense (d : ℕ) : Dense (idc_cylinderBcfSet d) := by
  rw [Metric.dense_iff]
  intro g ε hε
  obtain ⟨f, hf⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (idc_cylinderAlg d) (idc_cylinderAlg_separatesPoints d) g.toContinuousMap ε hε
  refine ⟨BoundedContinuousFunction.mkOfCompact (f : C(_, ℝ)), ?_, ⟨(f : C(_, ℝ)), f.2, rfl⟩⟩
  rw [Metric.mem_ball]
  have hg : BoundedContinuousFunction.mkOfCompact g.toContinuousMap = g :=
    BoundedContinuousFunction.ext (congrFun rfl)
  calc dist (BoundedContinuousFunction.mkOfCompact (f : C(_, ℝ))) g
      = dist (BoundedContinuousFunction.mkOfCompact (f : C(_, ℝ)))
          (BoundedContinuousFunction.mkOfCompact g.toContinuousMap) := by rw [hg]
    _ = dist (f : C(_, ℝ)) g.toContinuousMap := BoundedContinuousFunction.dist_mkOfCompact _ _
    _ = ‖(f : C(_, ℝ)) - g.toContinuousMap‖ := dist_eq_norm _ _
    _ < ε := hf















def idc_wiredCylinderDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f ∈ idc_cylinderBcfSet d,
    Tendsto (isd_decayFun (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) g f) atTop (𝓝 0)


def idc_freeCylinderDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f ∈ idc_cylinderBcfSet d,
    Tendsto (isd_decayFun (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) g f) atTop (𝓝 0)





theorem idc_wiredDenseDecay_of_cylinderDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hcyl : idc_wiredCylinderDecay hp hp1 hq g φ) :
    isd_wiredDenseDecay hp hp1 hq g φ :=
  ⟨idc_cylinderBcfSet d, idc_cylinderBcfSet_dense d, hcyl⟩



theorem idc_freeDenseDecay_of_cylinderDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hcyl : idc_freeCylinderDecay hp hp1 hq g φ) :
    isd_freeDenseDecay hp hp1 hq g φ :=
  ⟨idc_cylinderBcfSet d, idc_cylinderBcfSet_dense d, hcyl⟩






theorem idc_wiredIntegralShiftDecay_of_cylinderDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hcyl : idc_wiredCylinderDecay hp hp1 hq g φ) :
    ivt_wiredIntegralShiftDecay hp hp1 hq g φ :=
  isd_wiredIntegralShiftDecay_of_dense hp hp1 hq g φ
    (idc_wiredDenseDecay_of_cylinderDecay hp hp1 hq g φ hcyl)



theorem idc_freeIntegralShiftDecay_of_cylinderDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hcyl : idc_freeCylinderDecay hp hp1 hq g φ) :
    ivt_freeIntegralShiftDecay hp hp1 hq g φ :=
  isd_freeIntegralShiftDecay_of_dense hp hp1 hq g φ
    (idc_freeDenseDecay_of_cylinderDecay hp hp1 hq g φ hcyl)











theorem idc_wiredCylinderDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : idc_wiredCylinderDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
  intro f _
  have hzero : isd_decayFun (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
      (1 : Multiplicative (Site d)) f = fun _ => (0 : ℝ) := by
    funext n; exact isd_decayFun_one _ f n
  rw [hzero]
  exact tendsto_const_nhds



theorem idc_freeCylinderDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : idc_freeCylinderDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
  intro f _
  have hzero : isd_decayFun (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
      (1 : Multiplicative (Site d)) f = fun _ => (0 : ℝ) := by
    funext n; exact isd_decayFun_one _ f n
  rw [hzero]
  exact tendsto_const_nhds





theorem idc_wiredIntegralShiftDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : ivt_wiredIntegralShiftDecay hp hp1 hq (1 : Multiplicative (Site d)) φ :=
  idc_wiredIntegralShiftDecay_of_cylinderDecay hp hp1 hq (1 : Multiplicative (Site d)) φ
    (idc_wiredCylinderDecay_one hp hp1 hq φ)















theorem idc_wiredIV_isTranslationInvariant_of_cylinderDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q)
    (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
          (wiredInfiniteVolume d hp hp1 hq) →
        idc_wiredCylinderDecay hp hp1 hq g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) :=
  isd_wiredIV_isTranslationInvariant_of_denseDecay hp hp1 hq
    (fun g φ hφ hconv => idc_wiredDenseDecay_of_cylinderDecay hp hp1 hq g φ (hcyl g φ hφ hconv))



theorem idc_freeIV_isTranslationInvariant_of_cylinderDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q)
    (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
          (freeInfiniteVolume d hp hp1 hq) →
        idc_freeCylinderDecay hp hp1 hq g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) :=
  isd_freeIV_isTranslationInvariant_of_denseDecay hp hp1 hq
    (fun g φ hφ hconv => idc_freeDenseDecay_of_cylinderDecay hp hp1 hq g φ (hcyl g φ hφ hconv))

end FK

end StatMech
