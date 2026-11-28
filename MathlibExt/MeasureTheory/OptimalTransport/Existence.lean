/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Existence of optimal couplings

On Polish spaces, for a continuous cost `c : X × Y → [0, ∞]`, the total cost `π ↦ ∫ c dπ` attains
its minimum on the set of couplings of two probability measures
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Theorem 4.1, case `a = b = 0`
with a continuous cost). The proof follows Villani's: the set of couplings is tight (Lemma 4.4)
and closed for weak convergence, hence compact by Prokhorov's theorem, and the total cost is
lower semicontinuous (Lemma 4.3).

As a consequence the infimum defining the Wasserstein distance is attained.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling isCoupling_iff_map)

namespace MathlibExt.MeasureTheory.OptimalTransport.Existence

open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **The set of couplings is closed.** On Polish spaces, the couplings of two probability
measures form a closed set for the topology of weak convergence (C. Villani, *Optimal Transport:
Old and New*, Springer 2009, proof of Theorem 4.1). -/
theorem isClosed_setOf_isCoupling (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    IsClosed {π : ProbabilityMeasure (X × Y) | IsCoupling μ ν π} := by
  have e : {π : ProbabilityMeasure (X × Y) | IsCoupling μ ν π} =
      (fun π : ProbabilityMeasure (X × Y) => π.map Prod.fst) ⁻¹' {μ} ∩
        (fun π : ProbabilityMeasure (X × Y) => π.map Prod.snd) ⁻¹' {ν} := by
    ext π
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact isCoupling_iff_map μ ν π
  rw [e]
  exact (isClosed_singleton.preimage (ProbabilityMeasure.continuous_map continuous_fst)).inter
    (isClosed_singleton.preimage (ProbabilityMeasure.continuous_map continuous_snd))

/-- **Tightness of transference plans.** On Polish spaces, the couplings of two probability
measures form a tight set (C. Villani, *Optimal Transport: Old and New*, Springer 2009,
Lemma 4.4, with the singletons `{μ}` and `{ν}`). -/
theorem isTightMeasureSet_setOf_isCoupling (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) :
    IsTightMeasureSet {((π : ProbabilityMeasure (X × Y)) : Measure (X × Y)) |
      π ∈ {π : ProbabilityMeasure (X × Y) | IsCoupling μ ν π}} := by
  have hμ : IsTightMeasureSet {(μ : Measure X)} := isTightMeasureSet_singleton
  have hν : IsTightMeasureSet {(ν : Measure Y)} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hμ hν ⊢
  intro ε hε
  obtain ⟨K₁, hK₁, h₁⟩ := hμ (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨K₂, hK₂, h₂⟩ := hν (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨K₁ ×ˢ K₂, hK₁.prod hK₂, ?_⟩
  rintro _ ⟨π, hπ, rfl⟩
  obtain ⟨hπ1, hπ2⟩ : IsCoupling μ ν π := hπ
  have hsub : (K₁ ×ˢ K₂)ᶜ ⊆ Prod.fst ⁻¹' K₁ᶜ ∪ Prod.snd ⁻¹' K₂ᶜ := by
    intro z hz
    simp only [mem_compl_iff, mem_prod, not_and_or] at hz
    simpa only [mem_union, mem_preimage, mem_compl_iff] using hz
  have e1 : (π : Measure (X × Y)) (Prod.fst ⁻¹' K₁ᶜ) = (μ : Measure X) K₁ᶜ := by
    rw [hπ1, Measure.map_apply measurable_fst hK₁.isClosed.measurableSet.compl]
  have e2 : (π : Measure (X × Y)) (Prod.snd ⁻¹' K₂ᶜ) = (ν : Measure Y) K₂ᶜ := by
    rw [hπ2, Measure.map_apply measurable_snd hK₂.isClosed.measurableSet.compl]
  calc (π : Measure (X × Y)) (K₁ ×ˢ K₂)ᶜ
      ≤ (π : Measure (X × Y)) (Prod.fst ⁻¹' K₁ᶜ ∪ Prod.snd ⁻¹' K₂ᶜ) := measure_mono hsub
    _ ≤ (π : Measure (X × Y)) (Prod.fst ⁻¹' K₁ᶜ) + (π : Measure (X × Y)) (Prod.snd ⁻¹' K₂ᶜ) :=
        measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := by
        rw [e1, e2]; exact add_le_add (h₁ _ rfl) (h₂ _ rfl)
    _ = ε := ENNReal.add_halves ε

/-- **Lower semicontinuity of the total cost.** On a Polish space `Z`, for a continuous
`c : Z → [0, ∞]`, the map `π ↦ ∫ c dπ` is lower semicontinuous on probability measures with the
topology of weak convergence (C. Villani, *Optimal Transport: Old and New*, Springer 2009,
Lemma 4.3, nonnegative case: `F : π ↦ ∫ c dπ` is lower semicontinuous). -/
theorem lowerSemicontinuous_lintegral {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] {c : Z → ℝ≥0∞} (hc : Continuous c) :
    LowerSemicontinuous fun π : ProbabilityMeasure Z => ∫⁻ z, c z ∂(π : Measure Z) := by
  -- Truncations `min n c`, continuous and real-valued.
  set f : ℕ → Z → ℝ := fun n z => ENNReal.truncateToReal n (c z)
  have hf_cont : ∀ n, Continuous (f n) := fun n =>
    (ENNReal.continuous_truncateToReal (ENNReal.natCast_ne_top n)).comp hc
  have hf_nn : ∀ n, 0 ≤ f n := fun n z => ENNReal.toReal_nonneg
  have hf_of : ∀ n z, ENNReal.ofReal (f n z) = min (n : ℝ≥0∞) (c z) := by
    intro n z
    exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_left _ _))
  have hsup : ∀ π : ProbabilityMeasure Z, ∫⁻ z, c z ∂(π : Measure Z) =
      ⨆ n : ℕ, ∫⁻ z, ENNReal.ofReal (f n z) ∂(π : Measure Z) := by
    intro π
    simp_rw [hf_of]
    rw [← lintegral_iSup]
    · congr 1
      ext z
      rw [← iSup_inf_eq, ENNReal.iSup_natCast]
      exact (top_inf_eq _).symm
    · intro n
      exact (measurable_const.min hc.measurable)
    · intro m n hmn z
      exact min_le_min_right _ (Nat.cast_le.2 hmn)
  simp_rw [hsup]
  refine lowerSemicontinuous_iSup fun n => ?_
  -- Each truncated functional is lower semicontinuous: sequential argument and portmanteau.
  intro π y hy
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨πs, hπs, hle⟩ := frequently_iff_seq_forall.1 hcon
  have hopen : ∀ G, IsOpen G → (π : Measure Z) G ≤
      atTop.liminf (fun i => ((πs i : ProbabilityMeasure Z) : Measure Z) G) :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hπs hG
  have key := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (hf_cont n) (hf_nn n) hopen
  have hlim : atTop.liminf (fun i => ∫⁻ z, ENNReal.ofReal (f n z)
      ∂((πs i : ProbabilityMeasure Z) : Measure Z)) ≤ y :=
    liminf_le_of_frequently_le' (Frequently.of_forall fun i => not_lt.1 (hle i))
  exact absurd (key.trans hlim) (not_le.2 hy)

/-- **Existence of an optimal coupling.** Let `X` and `Y` be Polish spaces with Borel probability
measures `μ` and `ν`, and let `c : X × Y → [0, ∞]` be continuous. Then some coupling `π` of `μ` and
`ν` minimizes the total cost `∫ c dπ` among all couplings
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Theorem 4.1, in the case
`a = b = 0` with a continuous cost).

It is stated with `IsCoupling` and `ProbabilityMeasure`; the formulation with
`Couplings` and `kantorovichCost`,
`MathlibExt.Analysis.OptimalTransportWanted.Analysis.monge_kantorovich_exists`, is deduced from it
in `MathlibExt.MeasureTheory.OptimalTransport.MongeKantorovich`. -/
theorem exists_isCoupling_forall_lintegral_le (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) {c : X × Y → ℝ≥0∞} (hc : Continuous c) :
    ∃ π : ProbabilityMeasure (X × Y), IsCoupling μ ν π ∧
      ∀ π' : ProbabilityMeasure (X × Y), IsCoupling μ ν π' →
        ∫⁻ z, c z ∂(π : Measure (X × Y)) ≤ ∫⁻ z, c z ∂(π' : Measure (X × Y)) := by
  set S := {π : ProbabilityMeasure (X × Y) | IsCoupling μ ν π}
  have hS : IsCompact S := by
    have h := isCompact_closure_of_isTightMeasureSet (S := S)
      (isTightMeasureSet_setOf_isCoupling μ ν)
    rwa [(isClosed_setOf_isCoupling μ ν).closure_eq] at h
  have hne : S.Nonempty := ⟨μ.prod ν, isCoupling_prod μ ν⟩
  obtain ⟨π, hπ, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hS
    ((lowerSemicontinuous_lintegral hc).lowerSemicontinuousOn S)
  exact ⟨π, hπ, fun π' hπ' => isMinOn_iff.1 hmin π' hπ'⟩

/-- **Optimal couplings exist for the Wasserstein cost.** On a Polish extended metric space with
its Borel σ-algebra, for every real `p` there is a coupling `π` of `μ` and `ν` with
`∫ d(x, y)^p dπ = inf_π' ∫ d^p dπ'`, so the infimum in the definition of `W_p` is a minimum
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Theorem 4.1 applied to the
continuous cost `c = d^p`, as used after Definition 6.1). -/
theorem exists_isCoupling_lintegral_eq_transportCost {X : Type*} [EMetricSpace X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X] (p : ℝ)
    (μ ν : ProbabilityMeasure X) :
    ∃ π : ProbabilityMeasure (X × X), IsCoupling μ ν π ∧
      ∫⁻ z, edist z.1 z.2 ^ p ∂(π : Measure (X × X)) = transportCost p μ ν := by
  have hc : Continuous fun z : X × X => edist z.1 z.2 ^ p :=
    (ENNReal.continuous_rpow_const).comp continuous_edist
  obtain ⟨π, hπ, hmin⟩ := exists_isCoupling_forall_lintegral_le μ ν hc
  exact ⟨π, hπ, le_antisymm (le_iInf₂ fun π' hπ' => hmin π' hπ')
    (transportCost_le_of_isCoupling hπ)⟩

end MathlibExt.MeasureTheory.OptimalTransport.Existence
