/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Code.FK.IntegralDecayClose
import Code.FK.FiniteVolumeShift

open MeasureTheory Filter Topology BoundedContinuousFunction SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}








variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]












theorem cdc_eventMassProb_reCfgIso_inv (σ : V ≃ W)
    (μV : ConfigSpace (Sym2 V) → ℝ) (μW : ConfigSpace (Sym2 W) → ℝ)
    (hμ : ∀ ω, μV (reCfgIso σ ω) = μW ω) (S : Set (ConfigSpace (Sym2 V))) :
    ∑ ω : ConfigSpace (Sym2 W),
          (reCfgIso σ ⁻¹' S).indicator (fun _ => (1:ℝ)) ω * μW ω
      = ∑ η : ConfigSpace (Sym2 V), S.indicator (fun _ => (1:ℝ)) η * μV η := by
  rw [← Equiv.sum_comp (reCfgIsoEquiv σ)
    (fun η => S.indicator (fun _ => (1:ℝ)) η * μV η)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  show (reCfgIso σ ⁻¹' S).indicator (fun _ => (1:ℝ)) ω * μW ω
    = S.indicator (fun _ => (1:ℝ)) (reCfgIso σ ω) * μV (reCfgIso σ ω)
  rw [hμ ω]
  have hind : (reCfgIso σ ⁻¹' S).indicator (fun _ => (1:ℝ)) ω
      = S.indicator (fun _ => (1:ℝ)) (reCfgIso σ ω) := by
    by_cases h : reCfgIso σ ω ∈ S
    · rw [Set.indicator_of_mem (show ω ∈ reCfgIso σ ⁻¹' S from h),
        Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (show ω ∉ reCfgIso σ ⁻¹' S from h),
        Set.indicator_of_notMem h]
  rw [hind]










def cdc_multiOpenEvent (s : Finset (Sym2 (Site d))) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ∀ e ∈ s, ω e = true}





theorem cdc_prod_coordCM_eq_indicator (s : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) :
    (∏ e ∈ s, idc_coordCM e ω) = (cdc_multiOpenEvent s).indicator (fun _ => (1:ℝ)) ω := by
  simp only [idc_coordCM_apply]
  by_cases h : ω ∈ cdc_multiOpenEvent s
  · rw [Set.indicator_of_mem h]
    refine Finset.prod_eq_one fun e he => ?_
    rw [if_pos (h e he)]
  · rw [Set.indicator_of_notMem h]
    simp only [cdc_multiOpenEvent, Set.mem_setOf_eq, not_forall] at h
    obtain ⟨e, he, hee⟩ := h
    refine Finset.prod_eq_zero he ?_
    rw [if_neg (by simpa using hee)]



theorem cdc_multiOpenEvent_isIncreasing (s : Finset (Sym2 (Site d))) :
    IsIncreasing (cdc_multiOpenEvent s) := by
  intro a b hab ha e he
  have hle := hab e
  rw [ha e he] at hle
  exact le_antisymm (by simp) hle



theorem cdc_multiOpenEvent_measurable (s : Finset (Sym2 (Site d))) :
    MeasurableSet (cdc_multiOpenEvent s) := by
  have : cdc_multiOpenEvent s = ⋂ e ∈ s, {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} := by
    ext ω; simp only [cdc_multiOpenEvent, Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  exact MeasurableSet.biInter s.countable_toSet (fun e _ => idc_openEdgeEvent_measurable e)









noncomputable def cdc_monomialCM (s : Finset (Sym2 (Site d))) :
    C(ConfigSpace (Sym2 (Site d)), ℝ) :=
  ∏ e ∈ s, idc_coordCM e


noncomputable def cdc_monomialBcf (s : Finset (Sym2 (Site d))) :
    ConfigSpace (Sym2 (Site d)) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact (cdc_monomialCM s)

@[simp] theorem cdc_monomialCM_apply (s : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) :
    cdc_monomialCM s ω = ∏ e ∈ s, idc_coordCM e ω := by
  simp only [cdc_monomialCM, ContinuousMap.prod_apply]

@[simp] theorem cdc_monomialBcf_apply (s : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) :
    cdc_monomialBcf s ω = ∏ e ∈ s, idc_coordCM e ω := by
  simp only [cdc_monomialBcf, BoundedContinuousFunction.mkOfCompact_apply, cdc_monomialCM_apply]




theorem cdc_integral_monomialBcf (s : Finset (Sym2 (Site d)))
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsFiniteMeasure μ] :
    (∫ ω, cdc_monomialBcf s ω ∂μ) = μ.real (cdc_multiOpenEvent s) := by
  have heq : (fun ω => cdc_monomialBcf s ω)
      = Set.indicator (cdc_multiOpenEvent s) (fun _ => (1 : ℝ)) := by
    funext ω
    rw [cdc_monomialBcf_apply, cdc_prod_coordCM_eq_indicator]
  rw [heq, MeasureTheory.integral_indicator_const (1 : ℝ) (cdc_multiOpenEvent_measurable s)]
  simp





theorem cdc_monomialBcf_comp_shift (s : Finset (Sym2 (Site d)))
    (g : Multiplicative (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    cdc_monomialBcf s (shift g ω)
      = (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e))).indicator (fun _ => (1:ℝ)) ω := by
  rw [cdc_monomialBcf_apply]
  have : (∏ e ∈ s, idc_coordCM e (shift g ω))
      = (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e))).indicator (fun _ => (1:ℝ)) ω := by
    rw [← cdc_prod_coordCM_eq_indicator]
    rw [Finset.prod_image (fun a _ b _ hab => by
      have : g⁻¹ • a = g⁻¹ • b := hab
      exact (MulAction.injective g⁻¹) this)]
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [idc_coordCM_apply, idc_coordCM_apply, shift_apply]
  exact this




theorem cdc_decayFun_monomial (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (s : Finset (Sym2 (Site d))) (n : ℕ) :
    isd_decayFun μ g (cdc_monomialBcf s) n
      = ((μ n : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent s))
        - ((μ n : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e)))) := by
  unfold isd_decayFun
  rw [cdc_integral_monomialBcf s]
  congr 1
  
  have hshift : (fun ω => cdc_monomialBcf s (shift g ω))
      = Set.indicator (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e))) (fun _ => (1:ℝ)) := by
    funext ω; exact cdc_monomialBcf_comp_shift s g ω
  rw [hshift,
    MeasureTheory.integral_indicator_const (1 : ℝ)
      (cdc_multiOpenEvent_measurable (s.image (fun e => g⁻¹ • e)))]
  simp










def cdc_boxMultiOpenEvent (N : ℕ) (t : Finset (Sym2 (boxVerts d N))) :
    Set (ConfigSpace (Sym2 (boxVerts d N))) :=
  {σ | ∀ eb ∈ t, σ eb = true}


theorem cdc_boxMultiOpenEvent_isIncreasing (N : ℕ) (t : Finset (Sym2 (boxVerts d N))) :
    IsIncreasing (cdc_boxMultiOpenEvent N t) := by
  intro a b hab ha eb heb
  have hle := hab eb
  rw [ha eb heb] at hle
  exact le_antisymm (by simp) hle






theorem cdc_multiOpenEvent_image_eq_boxRestrict (N : ℕ) (t : Finset (Sym2 (boxVerts d N))) :
    cdc_multiOpenEvent (t.image (edgeIncl d N))
      = boxRestrict d N ⁻¹' (cdc_boxMultiOpenEvent N t) := by
  ext ω
  simp only [cdc_multiOpenEvent, cdc_boxMultiOpenEvent, Set.mem_setOf_eq, Set.mem_preimage,
    boxRestrict, Finset.forall_mem_image]





theorem cdc_wired_multiOpenEvent_tendsto (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
  rw [cdc_multiOpenEvent_image_eq_boxRestrict N t]
  exact fk_wired_infinite_measure N hp hp1 (cdc_boxMultiOpenEvent_isIncreasing N t)



theorem cdc_free_multiOpenEvent_tendsto (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
  rw [cdc_multiOpenEvent_image_eq_boxRestrict N t]
  exact fk_free_infinite_measure N hp hp1 (cdc_boxMultiOpenEvent_isIncreasing N t)









theorem cdc_edge_mem_range (x y : Site d)
    {N : ℕ} (hx : x ∈ box d N) (hy : y ∈ box d N) :
    s(x, y) ∈ Set.range (edgeIncl d N) :=
  ⟨s(⟨x, hx⟩, ⟨y, hy⟩), by unfold edgeIncl; rw [Sym2.map_mk]⟩




theorem cdc_finset_in_box (s : Finset (Sym2 (Site d))) :
    ∃ (N : ℕ) (t : Finset (Sym2 (boxVerts d N))), s = t.image (edgeIncl d N) := by
  classical
  
  set rad : Sym2 (Site d) → ℕ := fun e => Sym2.lift
      ⟨fun x y => Finset.univ.sup (fun i => (x i).natAbs ⊔ (y i).natAbs),
        fun x y => by simp only [sup_comm]⟩ e with hrad
  have hrad_mk : ∀ x y : Site d,
      rad s(x, y) = Finset.univ.sup (fun i => (x i).natAbs ⊔ (y i).natAbs) := fun x y => rfl
  
  refine ⟨s.sup rad, ?_⟩
  set N := s.sup rad with hN
  
  have hmem : ∀ e ∈ s, e ∈ Set.range (edgeIncl d N) := by
    intro e he
    induction e using Sym2.ind with | _ x y =>
    have hle : Finset.univ.sup (fun i => (x i).natAbs ⊔ (y i).natAbs) ≤ N := by
      rw [hN, ← hrad_mk x y]
      exact Finset.le_sup he
    have hxi : ∀ i, (x i).natAbs ≤ N := fun i =>
      le_trans (le_trans (le_max_left _ ((y i).natAbs))
        (Finset.le_sup (f := fun i => (x i).natAbs ⊔ (y i).natAbs) (Finset.mem_univ i))) hle
    have hyi : ∀ i, (y i).natAbs ≤ N := fun i =>
      le_trans (le_trans (le_max_right ((x i).natAbs) _)
        (Finset.le_sup (f := fun i => (x i).natAbs ⊔ (y i).natAbs) (Finset.mem_univ i))) hle
    exact cdc_edge_mem_range x y hxi hyi
  
  refine ⟨s.attach.image (fun e => (hmem e.1 e.2).choose), ?_⟩
  rw [Finset.image_image]
  ext e
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, Function.comp_apply]
  constructor
  · intro he
    exact ⟨e, he, (hmem e he).choose_spec⟩
  · rintro ⟨a, ha, rfl⟩
    rw [(hmem a ha).choose_spec]
    exact ha














def cdc_wiredMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) : Prop :=
  ∀ s : Finset (Sym2 (Site d)),
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent s)
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e)))



def cdc_freeMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) : Prop :=
  ∀ s : Finset (Sym2 (Site d)),
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent s)
      = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e)))









theorem cdc_decayFun_monomial_wired_tendsto_zero {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hhom : cdc_wiredMultiHomogeneous hp hp1 g) (s : Finset (Sym2 (Site d))) :
    Tendsto (isd_decayFun (fun n => wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2))
        g (cdc_monomialBcf s)) atTop (𝓝 0) := by
  
  have hdecay : isd_decayFun
      (fun n => wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2))
      g (cdc_monomialBcf s)
    = fun n => (wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent s)
        - (wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e))) := by
    funext n; exact cdc_decayFun_monomial _ g s n
  rw [hdecay]
  
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  obtain ⟨N', t', hst'⟩ := cdc_finset_in_box (s.image (fun e => g⁻¹ • e))
  
  have h1full := cdc_wired_multiOpenEvent_tendsto N t hp hp1
  rw [← hst] at h1full
  have h2full := cdc_wired_multiOpenEvent_tendsto N' t' hp hp1
  rw [← hst'] at h2full
  
  have h1 := h1full.comp hφ.tendsto_atTop
  have h2 := h2full.comp hφ.tendsto_atTop
  
  have hsub := h1.sub h2
  rw [← hhom s, sub_self] at hsub
  exact hsub



theorem cdc_decayFun_monomial_free_tendsto_zero {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hhom : cdc_freeMultiHomogeneous hp hp1 g) (s : Finset (Sym2 (Site d))) :
    Tendsto (isd_decayFun (fun n => freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2))
        g (cdc_monomialBcf s)) atTop (𝓝 0) := by
  have hdecay : isd_decayFun
      (fun n => freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2))
      g (cdc_monomialBcf s)
    = fun n => (freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent s)
        - (freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e))) := by
    funext n; exact cdc_decayFun_monomial _ g s n
  rw [hdecay]
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  obtain ⟨N', t', hst'⟩ := cdc_finset_in_box (s.image (fun e => g⁻¹ • e))
  have h1full := cdc_free_multiOpenEvent_tendsto N t hp hp1
  rw [← hst] at h1full
  have h2full := cdc_free_multiOpenEvent_tendsto N' t' hp hp1
  rw [← hst'] at h2full
  have h1 := h1full.comp hφ.tendsto_atTop
  have h2 := h2full.comp hφ.tendsto_atTop
  have hsub := h1.sub h2
  rw [← hhom s, sub_self] at hsub
  exact hsub










theorem cdc_monomialCM_empty : cdc_monomialCM (∅ : Finset (Sym2 (Site d))) = 1 := by
  unfold cdc_monomialCM
  rw [Finset.prod_empty]


theorem cdc_monomialCM_singleton (e : Sym2 (Site d)) :
    cdc_monomialCM ({e} : Finset (Sym2 (Site d))) = idc_coordCM e := by
  unfold cdc_monomialCM
  rw [Finset.prod_singleton]





theorem cdc_monomialCM_mul (s₁ s₂ : Finset (Sym2 (Site d))) :
    cdc_monomialCM s₁ * cdc_monomialCM s₂ = cdc_monomialCM (s₁ ∪ s₂) := by
  apply ContinuousMap.ext
  intro ω
  simp only [ContinuousMap.mul_apply, cdc_monomialCM_apply, cdc_prod_coordCM_eq_indicator]
  have hinter : cdc_multiOpenEvent (s₁ ∪ s₂)
      = cdc_multiOpenEvent s₁ ∩ cdc_multiOpenEvent s₂ := by
    ext ω'
    simp only [cdc_multiOpenEvent, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_union]
    constructor
    · intro h; exact ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩
    · rintro ⟨h1, h2⟩ e (he | he)
      · exact h1 e he
      · exact h2 e he
  rw [hinter]
  have := Set.inter_indicator_mul (s := cdc_multiOpenEvent s₁) (t := cdc_multiOpenEvent s₂)
    (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) ω
  simp only [mul_one] at this
  rw [this]





theorem cdc_closure_isMonomial {h : C(ConfigSpace (Sym2 (Site d)), ℝ)}
    (hh : h ∈ Submonoid.closure (Set.range (idc_coordCM (d := d)))) :
    ∃ s : Finset (Sym2 (Site d)), h = cdc_monomialCM s := by
  induction hh using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    exact ⟨{e}, (cdc_monomialCM_singleton e).symm⟩
  | one => exact ⟨∅, (cdc_monomialCM_empty).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s₁, rfl⟩ := hx
    obtain ⟨s₂, rfl⟩ := hy
    exact ⟨s₁ ∪ s₂, cdc_monomialCM_mul s₁ s₂⟩








theorem cdc_decayFun_add (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (f f' : ConfigSpace (Sym2 (Site d)) →ᵇ ℝ) (n : ℕ) :
    isd_decayFun μ g (f + f') n = isd_decayFun μ g f n + isd_decayFun μ g f' n := by
  simp only [isd_decayFun, BoundedContinuousFunction.coe_add, Pi.add_apply]
  have h1 : (∫ x, (f x + f' x) ∂(μ n : Measure _))
      = (∫ x, f x ∂(μ n : Measure _)) + ∫ x, f' x ∂(μ n : Measure _) :=
    integral_add (f.integrable _) (f'.integrable _)
  have h2 : (∫ x, (f (shift g x) + f' (shift g x)) ∂(μ n : Measure _))
      = (∫ x, f (shift g x) ∂(μ n : Measure _)) + ∫ x, f' (shift g x) ∂(μ n : Measure _) :=
    integral_add ((f.compContinuous ⟨shift g, continuous_shift g⟩).integrable _)
      ((f'.compContinuous ⟨shift g, continuous_shift g⟩).integrable _)
  rw [h1, h2]
  ring


theorem cdc_decayFun_smul (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (c : ℝ) (f : ConfigSpace (Sym2 (Site d)) →ᵇ ℝ) (n : ℕ) :
    isd_decayFun μ g (c • f) n = c * isd_decayFun μ g f n := by
  simp only [isd_decayFun, BoundedContinuousFunction.coe_smul, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul]
  ring


theorem cdc_decayFun_zero (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (n : ℕ) :
    isd_decayFun μ g (0 : ConfigSpace (Sym2 (Site d)) →ᵇ ℝ) n = 0 := by
  simp only [isd_decayFun, BoundedContinuousFunction.coe_zero, Pi.zero_apply, integral_zero,
    sub_zero]














noncomputable def cdc_wiredDecaySet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) :
    Submodule ℝ C(ConfigSpace (Sym2 (Site d)), ℝ) where
  carrier := {h | Tendsto (isd_decayFun
      (fun n => wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) g
      (BoundedContinuousFunction.mkOfCompact h)) atTop (𝓝 0)}
  add_mem' {h h'} hh hh' := by
    simp only [Set.mem_setOf_eq] at hh hh' ⊢
    have hsum := hh.add hh'
    rw [add_zero] at hsum
    refine hsum.congr (fun n => ?_)
    rw [BoundedContinuousFunction.mkOfCompact_add, cdc_decayFun_add]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have hz : isd_decayFun
        (fun n => wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) g
        (BoundedContinuousFunction.mkOfCompact (0 : C(ConfigSpace (Sym2 (Site d)), ℝ)))
      = fun _ => (0:ℝ) := by
      funext n
      rw [BoundedContinuousFunction.mkOfCompact_zero, cdc_decayFun_zero]
    rw [hz]; exact tendsto_const_nhds
  smul_mem' c h hh := by
    simp only [Set.mem_setOf_eq] at hh ⊢
    have hsmul := hh.const_mul c
    rw [mul_zero] at hsmul
    refine hsmul.congr (fun n => ?_)
    have hms : BoundedContinuousFunction.mkOfCompact (c • h)
        = c • BoundedContinuousFunction.mkOfCompact h := rfl
    rw [hms, cdc_decayFun_smul]


noncomputable def cdc_freeDecaySet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) :
    Submodule ℝ C(ConfigSpace (Sym2 (Site d)), ℝ) where
  carrier := {h | Tendsto (isd_decayFun
      (fun n => freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) g
      (BoundedContinuousFunction.mkOfCompact h)) atTop (𝓝 0)}
  add_mem' {h h'} hh hh' := by
    simp only [Set.mem_setOf_eq] at hh hh' ⊢
    have hsum := hh.add hh'
    rw [add_zero] at hsum
    refine hsum.congr (fun n => ?_)
    rw [BoundedContinuousFunction.mkOfCompact_add, cdc_decayFun_add]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have hz : isd_decayFun
        (fun n => freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) g
        (BoundedContinuousFunction.mkOfCompact (0 : C(ConfigSpace (Sym2 (Site d)), ℝ)))
      = fun _ => (0:ℝ) := by
      funext n
      rw [BoundedContinuousFunction.mkOfCompact_zero, cdc_decayFun_zero]
    rw [hz]; exact tendsto_const_nhds
  smul_mem' c h hh := by
    simp only [Set.mem_setOf_eq] at hh ⊢
    have hsmul := hh.const_mul c
    rw [mul_zero] at hsmul
    refine hsmul.congr (fun n => ?_)
    have hms : BoundedContinuousFunction.mkOfCompact (c • h)
        = c • BoundedContinuousFunction.mkOfCompact h := rfl
    rw [hms, cdc_decayFun_smul]













theorem cdc_cylinderAlg_le_wiredDecaySet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hhom : cdc_wiredMultiHomogeneous hp hp1 g) :
    Subalgebra.toSubmodule (idc_cylinderAlg d) ≤ cdc_wiredDecaySet hp hp1 g φ := by
  unfold idc_cylinderAlg
  rw [Algebra.adjoin_eq_span]
  rw [Submodule.span_le]
  intro h hh
  obtain ⟨s, rfl⟩ := cdc_closure_isMonomial hh
  
  show Tendsto (isd_decayFun
      (fun n => wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) g
      (BoundedContinuousFunction.mkOfCompact (cdc_monomialCM s))) atTop (𝓝 0)
  have := cdc_decayFun_monomial_wired_tendsto_zero hp hp1 g φ hφ hhom s
  exact this



theorem cdc_cylinderAlg_le_freeDecaySet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hhom : cdc_freeMultiHomogeneous hp hp1 g) :
    Subalgebra.toSubmodule (idc_cylinderAlg d) ≤ cdc_freeDecaySet hp hp1 g φ := by
  unfold idc_cylinderAlg
  rw [Algebra.adjoin_eq_span]
  rw [Submodule.span_le]
  intro h hh
  obtain ⟨s, rfl⟩ := cdc_closure_isMonomial hh
  show Tendsto (isd_decayFun
      (fun n => freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) g
      (BoundedContinuousFunction.mkOfCompact (cdc_monomialCM s))) atTop (𝓝 0)
  exact cdc_decayFun_monomial_free_tendsto_zero hp hp1 g φ hφ hhom s













theorem cdc_wiredCylinderDecay {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hhom : cdc_wiredMultiHomogeneous hp hp1 g) :
    idc_wiredCylinderDecay hp hp1 (by norm_num : (0:ℝ) < 2) g φ := by
  intro f hf
  obtain ⟨h, hhmem, rfl⟩ := hf
  exact cdc_cylinderAlg_le_wiredDecaySet hp hp1 g φ hφ hhom hhmem



theorem cdc_freeCylinderDecay {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hhom : cdc_freeMultiHomogeneous hp hp1 g) :
    idc_freeCylinderDecay hp hp1 (by norm_num : (0:ℝ) < 2) g φ := by
  intro f hf
  obtain ⟨h, hhmem, rfl⟩ := hf
  exact cdc_cylinderAlg_le_freeDecaySet hp hp1 g φ hφ hhom hhmem














theorem cdc_wiredMultiHomogeneous_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    cdc_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) := by
  intro s
  have hs : s.image (fun e => (1 : Multiplicative (Site d))⁻¹ • e) = s := by
    rw [show (fun e : Sym2 (Site d) => (1 : Multiplicative (Site d))⁻¹ • e)
        = (fun e => e) from by funext e; rw [inv_one, one_smul]]
    exact Finset.image_id
  rw [hs]



theorem cdc_freeMultiHomogeneous_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    cdc_freeMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) := by
  intro s
  have hs : s.image (fun e => (1 : Multiplicative (Site d))⁻¹ • e) = s := by
    rw [show (fun e : Sym2 (Site d) => (1 : Multiplicative (Site d))⁻¹ • e)
        = (fun e => e) from by funext e; rw [inv_one, one_smul]]
    exact Finset.image_id
  rw [hs]





theorem cdc_wiredCylinderDecay_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) :
    idc_wiredCylinderDecay hp hp1 (by norm_num : (0:ℝ) < 2) (1 : Multiplicative (Site d)) φ :=
  cdc_wiredCylinderDecay hp hp1 (1 : Multiplicative (Site d)) φ hφ
    (cdc_wiredMultiHomogeneous_one hp hp1)













theorem cdc_wiredIV_isTranslationInvariant_of_homogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hhom : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2))
          (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)) →
        cdc_wiredMultiHomogeneous hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  idc_wiredIV_isTranslationInvariant_of_cylinderDecay hp hp1 (by norm_num : (0:ℝ) < 2)
    (fun g φ hφ hconv => cdc_wiredCylinderDecay hp hp1 g φ hφ (hhom g φ hφ hconv))



theorem cdc_freeIV_isTranslationInvariant_of_homogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hhom : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2))
          (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)) →
        cdc_freeMultiHomogeneous hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  idc_freeIV_isTranslationInvariant_of_cylinderDecay hp hp1 (by norm_num : (0:ℝ) < 2)
    (fun g φ hφ hconv => cdc_freeCylinderDecay hp hp1 g φ hφ (hhom g φ hφ hconv))

end FK

end StatMech
