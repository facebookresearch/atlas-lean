/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Order.Compact

@[expose] public section

section
open MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/-!
# Kantorovich duality on compact metric spaces

Strong Kantorovich duality on products of nonempty compact
metric Borel probability spaces with continuous cost.
-/

/-- **Coupling of two probability measures.** Let $\mu$ and $\nu$ be probability measures on
measurable spaces $X$ and $Y$. A probability measure $\pi$ on $X \times Y$ is a coupling of
$\mu$ and $\nu$ when its marginals are $\mu$ and $\nu$, that is, when the pushforward of $\pi$
under the projection $X \times Y \to X$ is $\mu$ and the pushforward of $\pi$ under the
projection $X \times Y \to Y$ is $\nu$. -/
def IsCoupling {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (π : ProbabilityMeasure (X × Y)) : Prop :=
  (μ : Measure X) = (π : Measure (X × Y)).map Prod.fst ∧
    (ν : Measure Y) = (π : Measure (X × Y)).map Prod.snd

/-- **Values of the transport cost over couplings.** Let $\mu$ and $\nu$ be probability measures
on measurable spaces $X$ and $Y$, and let $c : X \times Y \to \mathbb{R}$. The primal values of
$c$ for $\mu$ and $\nu$ form the set of real numbers $\int c \, d\pi$, where $\pi$ ranges over
the couplings of $\mu$ and $\nu$.

Here $\int c \, d\pi$ is the Bochner integral, which is $0$ when $c$ is not $\pi$-integrable. -/
def primalValues {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) : Set ℝ :=
  {r : ℝ | ∃ π : ProbabilityMeasure (X × Y),
    IsCoupling μ ν π ∧ r = ∫ p, c p ∂(π : Measure (X × Y))}

/-- **Dual feasible pair of potentials.** Let $X$ and $Y$ be topological spaces and let
$c : X \times Y \to \mathbb{R}$. A pair of functions $\varphi : X \to \mathbb{R}$ and
$\psi : Y \to \mathbb{R}$ is dual feasible for the cost $c$ when $\varphi$ and $\psi$ are
continuous and $\varphi(x) + \psi(y) \le c(x, y)$ for all $x \in X$ and $y \in Y$. -/
def DualFeasible {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (c : X × Y → ℝ) (φ : X → ℝ) (ψ : Y → ℝ) : Prop :=
  Continuous φ ∧ Continuous ψ ∧ ∀ x y, φ x + ψ y ≤ c (x, y)

/-- A continuous real function on a compact space is integrable w.r.t. any finite measure. -/
private lemma integrable_continuous_compact
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X → ℝ) (hf : Continuous f) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable f μ := by
  rw [← integrableOn_univ]
  exact ContinuousOn.integrableOn_compact isCompact_univ hf.continuousOn

/-- The product of `μ` and `ν` is a coupling of `μ` and `ν`. -/
private lemma isCoupling_prod
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    IsCoupling μ ν (μ.prod ν) := by
  refine ⟨?_, ?_⟩
  · have h : ((μ.prod ν).map Prod.fst : ProbabilityMeasure X) = μ :=
      ProbabilityMeasure.map_fst_prod μ ν
    have h2 := congrArg (fun π : ProbabilityMeasure X => (π : Measure X)) h
    rw [ProbabilityMeasure.toMeasure_map] at h2
    exact h2.symm
  · have h : ((μ.prod ν).map Prod.snd : ProbabilityMeasure Y) = ν :=
      ProbabilityMeasure.map_snd_prod μ ν
    have h2 := congrArg (fun π : ProbabilityMeasure Y => (π : Measure Y)) h
    rw [ProbabilityMeasure.toMeasure_map] at h2
    exact h2.symm

/-- Weak duality: any dual-feasible value is below any primal (coupling) value. -/
private lemma dual_le_primal_of_isCoupling
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c) (φ : X → ℝ) (ψ : Y → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hle : ∀ x y, φ x + ψ y ≤ c (x, y))
    (π : ProbabilityMeasure (X × Y)) (hπ : IsCoupling μ ν π) :
    (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)
      ≤ ∫ p, c p ∂(π : Measure (X × Y)) := by
  obtain ⟨hμ, hν⟩ := hπ
  have hφπ : Integrable (fun p : X × Y => φ p.1) (π : Measure (X × Y)) :=
    integrable_continuous_compact _ (hφ.comp continuous_fst) _
  have hψπ : Integrable (fun p : X × Y => ψ p.2) (π : Measure (X × Y)) :=
    integrable_continuous_compact _ (hψ.comp continuous_snd) _
  have hcπ : Integrable c (π : Measure (X × Y)) :=
    integrable_continuous_compact _ hc _
  have eφ : (∫ x, φ x ∂(μ : Measure X))
      = ∫ p : X × Y, φ p.1 ∂(π : Measure (X × Y)) := by
    rw [hμ, integral_map measurable_fst.aemeasurable hφ.aestronglyMeasurable]
  have eψ : (∫ y, ψ y ∂(ν : Measure Y))
      = ∫ p : X × Y, ψ p.2 ∂(π : Measure (X × Y)) := by
    rw [hν, integral_map measurable_snd.aemeasurable hψ.aestronglyMeasurable]
  rw [eφ, eψ, ← integral_add hφπ hψπ]
  exact integral_mono_ae (hφπ.add hψπ) hcπ
    (Filter.Eventually.of_forall fun p => hle p.1 p.2)

/-- The primal problem is feasible: the product coupling always exists. -/
private lemma primalValues_nonempty
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) :
    (primalValues μ ν c).Nonempty :=
  ⟨∫ p, c p ∂((μ.prod ν) : Measure (X × Y)),
    μ.prod ν, isCoupling_prod μ ν, rfl⟩

/-- The dual problem is feasible: halved-minimum constants always work. -/
private lemma dualValues_nonempty
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c) :
    {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)}.Nonempty := by
  obtain ⟨p₀, -, hp₀⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  have hmin : ∀ x : X, ∀ y : Y, c p₀ ≤ c (x, y) :=
    fun x y => isMinOn_iff.mp hp₀ (x, y) (Set.mem_univ _)
  refine ⟨c p₀, (fun _ => c p₀ / 2), (fun _ => c p₀ / 2),
    ⟨continuous_const, continuous_const, fun x y => ?_⟩, ?_⟩
  · have h := hmin x y
    change c p₀ / 2 + c p₀ / 2 ≤ c (x, y)
    linarith
  · have h1 : (∫ _ : X, c p₀ / 2 ∂(μ : Measure X)) = c p₀ / 2 := by simp
    have h2 : (∫ _ : Y, c p₀ / 2 ∂(ν : Measure Y)) = c p₀ / 2 := by simp
    rw [h1, h2]
    ring

/-- A continuous real function on a nonempty compact space as a bounded continuous function. -/
private noncomputable def mkBCF
    {W : Type*} [TopologicalSpace W] [CompactSpace W] [Nonempty W]
    (f : W → ℝ) (hf : Continuous f) : W →ᵇ ℝ where
  toContinuousMap := ⟨f, hf⟩
  map_bounded' := by
    obtain ⟨z₁, -, hz₁⟩ :=
      isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
    obtain ⟨z₀, -, hz₀⟩ :=
      isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuousOn
    refine ⟨|f z₁| + |f z₀|, fun x y => ?_⟩
    rw [dist_eq_norm, Real.norm_eq_abs]
    have hx1 : f x ≤ f z₁ := isMaxOn_iff.mp hz₁ x (Set.mem_univ _)
    have hx0 : f z₀ ≤ f x := isMinOn_iff.mp hz₀ x (Set.mem_univ _)
    have hy1 : f y ≤ f z₁ := isMaxOn_iff.mp hz₁ y (Set.mem_univ _)
    have hy0 : f z₀ ≤ f y := isMinOn_iff.mp hz₀ y (Set.mem_univ _)
    have g1 : f z₁ ≤ |f z₁| := le_abs_self _
    have g2 : -(f z₀) ≤ |f z₀| := neg_le_abs _
    rw [abs_le]
    constructor <;> linarith

private theorem mkBCF_apply
    {W : Type*} [TopologicalSpace W] [CompactSpace W] [Nonempty W]
    (f : W → ℝ) (hf : Continuous f) (x : W) : mkBCF f hf x = f x := rfl

/-- A bounded continuous function on a nonempty compact space attains its maximum. -/
private theorem exists_max_attain
    {W : Type*} [TopologicalSpace W] [CompactSpace W] [Nonempty W]
    (f : W →ᵇ ℝ) : ∃ z₀, ∀ z, f z ≤ f z₀ := by
  obtain ⟨z₀, -, hz₀⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty f.continuous.continuousOn
  exact ⟨z₀, fun z => isMaxOn_iff.mp hz₀ z (Set.mem_univ _)⟩

/-- ENNReal subtraction reverses strict inequality on compacta: helper for outer regularity. -/
private theorem ennreal_sub_lt_of_lt {a b r : ℝ≥0∞}
    (ha : a ≠ ∞) (hb : b ≠ ∞) (hr : r ≠ ∞) (hbr : b < r) (hra : r ≤ a) :
    a - r < a - b := by
  have hba : b ≤ a := hbr.le.trans hra
  have h1 : (a - r).toReal < (a - b).toReal := by
    rw [ENNReal.toReal_sub_of_le hra ha, ENNReal.toReal_sub_of_le hba ha]
    have hbr' : b.toReal < r.toReal := (ENNReal.toReal_lt_toReal hb hr).mpr hbr
    linarith
  have h2 : a - r ≠ ∞ := ne_top_of_le_ne_top ha tsub_le_self
  have h3 : a - b ≠ ∞ := ne_top_of_le_ne_top ha tsub_le_self
  exact (ENNReal.toReal_lt_toReal h2 h3).mp h1

/-- A finite Borel measure on a compact metric space is regular. -/
private instance regular_of_finite_compact_metric
    {W : Type*} [MetricSpace W] [CompactSpace W]
    [MeasurableSpace W] [BorelSpace W]
    {μ : Measure W} [IsFiniteMeasure μ] : μ.Regular := by
  have hfin : IsFiniteMeasureOnCompacts μ := ⟨by
    intro K hK
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (measure_lt_top μ _)⟩
  have hinner_open : μ.InnerRegularWRT IsCompact IsOpen :=
    innerRegularWRT_isCompact_isOpen μ
  have hinner_meas : μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet :=
    innerRegular_isCompact_isClosed_measurableSet_of_finite μ
  have houter : μ.OuterRegular := ⟨fun {A} hA r hr => by
    by_cases hrU : r ≤ μ Set.univ
    · have hAfin : μ A ≠ ∞ := measure_ne_top μ A
      have hUfin : μ Set.univ ≠ ∞ := measure_ne_top μ Set.univ
      have hrfin : r ≠ ∞ := ne_top_of_le_ne_top hUfin hrU
      have hcompl : μ Aᶜ = μ Set.univ - μ A := measure_compl hA hAfin
      have hr'lt : μ Set.univ - r < μ Aᶜ := by
        rw [hcompl]
        exact ennreal_sub_lt_of_lt hUfin hAfin hrfin hr hrU
      obtain ⟨K, hKA, ⟨hKcomp, hKclosed⟩, hr'K⟩ :=
        hinner_meas hA.compl (μ Set.univ - r) hr'lt
      have hKfin : μ K ≠ ∞ := measure_ne_top μ K
      have hKmeas : MeasurableSet K := hKclosed.measurableSet
      have hKU : μ K ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      refine ⟨Kᶜ, fun x hx => ?_, hKclosed.isOpen_compl, ?_⟩
      · simp only [Set.mem_compl_iff]
        exact fun hKx => hKA hKx hx
      · rw [measure_compl hKmeas hKfin]
        have h1 : (μ Set.univ - μ K).toReal < r.toReal := by
          rw [ENNReal.toReal_sub_of_le hKU hUfin]
          have hr'K' : (μ Set.univ - r).toReal < (μ K).toReal := by
            have hsub : μ Set.univ - r ≠ ∞ :=
              ne_top_of_le_ne_top hUfin tsub_le_self
            exact (ENNReal.toReal_lt_toReal hsub hKfin).mpr hr'K
          rw [ENNReal.toReal_sub_of_le hrU hUfin] at hr'K'
          linarith
        have h2 : μ Set.univ - μ K ≠ ∞ := ne_top_of_le_ne_top hUfin tsub_le_self
        exact (ENNReal.toReal_lt_toReal h2 hrfin).mp h1
    · exact ⟨Set.univ, Set.subset_univ _, isOpen_univ, lt_of_not_ge hrU⟩⟩
  exact Measure.Regular.mk (toIsFiniteMeasureOnCompacts := hfin)
    (toOuterRegular := houter) hinner_open

/-- Sum of a pair of bounded continuous functions as a function on the product. -/
private noncomputable def phiPlusPsi
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) : (X × Y) →ᵇ ℝ :=
  mkBCF (fun z => d.1 z.1 + d.2 z.2)
    ((d.1.continuous.comp continuous_fst).add (d.2.continuous.comp continuous_snd))

private theorem phiPlusPsi_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (z : X × Y) :
    phiPlusPsi d z = d.1 z.1 + d.2 z.2 := rfl

/-- The sum map as a linear map into bounded continuous functions on the product. -/
private noncomputable def PhiLM
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y] :
    ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) →ₗ[ℝ] ((X × Y) →ᵇ ℝ) where
  toFun := phiPlusPsi
  map_add' d e := by
    apply BoundedContinuousFunction.ext
    intro z
    have h1 : (d + e).1 z.1 = d.1 z.1 + e.1 z.1 := rfl
    have h2 : (d + e).2 z.2 = d.2 z.2 + e.2 z.2 := rfl
    simp only [phiPlusPsi_apply, BoundedContinuousFunction.add_apply, h1, h2]
    ring
  map_smul' c d := by
    apply BoundedContinuousFunction.ext
    intro z
    have h1 : (c • d).1 z.1 = c • d.1 z.1 := rfl
    have h2 : (c • d).2 z.2 = c • d.2 z.2 := rfl
    simp only [phiPlusPsi_apply, BoundedContinuousFunction.smul_apply, h1, h2, smul_add,
      RingHom.id_apply]

/-- The dual objective as a linear map on pairs of bounded continuous functions. -/
private noncomputable def dualValLM
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) →ₗ[ℝ] ℝ where
  toFun d := (∫ x, d.1 x ∂μ) + ∫ y, d.2 y ∂ν
  map_add' d e := by
    have hφ1 : Integrable (fun x => d.1 x) μ :=
      integrable_continuous_compact _ d.1.continuous _
    have hφ2 : Integrable (fun x => e.1 x) μ :=
      integrable_continuous_compact _ e.1.continuous _
    have hψ1 : Integrable (fun y => d.2 y) ν :=
      integrable_continuous_compact _ d.2.continuous _
    have hψ2 : Integrable (fun y => e.2 y) ν :=
      integrable_continuous_compact _ e.2.continuous _
    have e1 : (fun x => (d + e).1 x) = (fun x => d.1 x + e.1 x) := rfl
    have e2 : (fun y => (d + e).2 y) = (fun y => d.2 y + e.2 y) := rfl
    change (∫ x, (d + e).1 x ∂μ) + ∫ y, (d + e).2 y ∂ν = _
    rw [e1, e2, integral_add hφ1 hφ2, integral_add hψ1 hψ2]
    ring
  map_smul' c d := by
    have e1 : (fun x => (c • d).1 x) = (fun x => c • d.1 x) := rfl
    have e2 : (fun y => (c • d).2 y) = (fun y => c • d.2 y) := rfl
    change (∫ x, (c • d).1 x ∂μ) + ∫ y, (c • d).2 y ∂ν = _
    simp only [e1, e2, integral_smul, smul_add, RingHom.id_apply]

private theorem PhiLM_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (z : X × Y) :
    (PhiLM d) z = d.1 z.1 + d.2 z.2 := rfl

/-- Dual values are bounded above (by any primal value). -/
private theorem dual_bddAbove
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c) :
    BddAbove {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} := by
  refine ⟨∫ p, c p ∂((μ.prod ν) : Measure (X × Y)), ?_⟩
  rintro r ⟨φ, ψ, hfeas, rfl⟩
  obtain ⟨hφ, hψ, hle⟩ := hfeas
  exact dual_le_primal_of_isCoupling μ ν c hc φ ψ hφ hψ hle _ (isCoupling_prod μ ν)

/-- Primal values are bounded below (by the minimum of `c`). -/
private theorem primal_bddBelow
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c) :
    BddBelow (primalValues μ ν c) := by
  obtain ⟨p₀, -, hp₀⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  refine ⟨c p₀, ?_⟩
  rintro q ⟨π, hπ, rfl⟩
  have hmin : ∀ z, c p₀ ≤ c z := fun z => isMinOn_iff.mp hp₀ z (Set.mem_univ _)
  have h1 : Integrable c (π : Measure (X × Y)) :=
    integrable_continuous_compact _ hc _
  have h2 : Integrable (fun _ : X × Y => c p₀) (π : Measure (X × Y)) :=
    integrable_const _
  have hle := integral_mono_ae h2 h1 (Filter.Eventually.of_forall hmin)
  simpa using hle

/-- Key estimate: shifting a pair down by an upper bound on the violation stays
below the dual supremum. -/
private theorem key_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c)
    (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (m : ℝ) (hm : ∀ z, (PhiLM d) z - c z ≤ m) :
    (dualValLM (μ : Measure X) (ν : Measure Y) d) - m ≤ sSup {r : ℝ | ∃ φ : X → ℝ,
      ∃ ψ : Y → ℝ, DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} := by
  have hbdd := dual_bddAbove μ ν c hc
  have hmem : (dualValLM (μ : Measure X) (ν : Measure Y) d) - m ∈ {r : ℝ | ∃ φ : X → ℝ,
      ∃ ψ : Y → ℝ, DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} := by
    refine ⟨⇑(d.1 - BoundedContinuousFunction.const X m), ⇑d.2,
      ⟨(d.1 - BoundedContinuousFunction.const X m).continuous, d.2.continuous, ?_⟩, ?_⟩
    · intro x y
      have h := hm (x, y)
      rw [PhiLM_apply] at h
      have hc1 : (d.1 - BoundedContinuousFunction.const X m) x = d.1 x - m := rfl
      rw [hc1]
      linarith
    · have hint1 : Integrable (fun x => d.1 x) (μ : Measure X) :=
        integrable_continuous_compact _ d.1.continuous _
      have hcm : Integrable (fun _ : X => m) (μ : Measure X) := integrable_const _
      have eφ : (∫ x, (d.1 - BoundedContinuousFunction.const X m) x ∂(μ : Measure X))
          = (∫ x, d.1 x ∂(μ : Measure X)) - m := by
        have e : (fun x => (d.1 - BoundedContinuousFunction.const X m) x)
            = (fun x => d.1 x - m) := rfl
        rw [e, integral_sub hint1 hcm]
        congr 1
        simp
      have hval : (dualValLM (μ : Measure X) (ν : Measure Y) d)
          = (∫ x, d.1 x ∂(μ : Measure X)) + ∫ y, d.2 y ∂(ν : Measure Y) := rfl
      rw [hval, eφ]
      ring
  exact le_csSup hbdd hmem

/-- Strictly negative bounded continuous functions form an open set. -/
private theorem isOpen_negBCF
    {W : Type*} [TopologicalSpace W] [CompactSpace W] [Nonempty W] :
    IsOpen {w : W →ᵇ ℝ | ∀ z, w z < 0} := by
  rw [Metric.isOpen_iff]
  intro w hw
  obtain ⟨z₀, hz₀⟩ := exists_max_attain w
  have hneg : w z₀ < 0 := hw z₀
  refine ⟨-(w z₀), by linarith, fun w' hw' => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hw'
  intro z
  have h3 : w' z - w z ≤ ‖w' - w‖ := by
    have hnorm := (w' - w).norm_coe_le_norm z
    rw [BoundedContinuousFunction.sub_apply, Real.norm_eq_abs] at hnorm
    exact le_trans (le_abs_self _) hnorm
  have h4 : w z ≤ w z₀ := hz₀ z
  linarith

/-- Strictly negative bounded continuous functions form a convex set. -/
private theorem convex_negBCF
    {W : Type*} [TopologicalSpace W] :
    Convex ℝ {w : W →ᵇ ℝ | ∀ z, w z < 0} := by
  intro w₁ hw₁ w₂ hw₂ a b ha hb hab z
  have e : (a • w₁ + b • w₂) z = a * w₁ z + b * w₂ z := by
    rw [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [e]
  have h1 : a * w₁ z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (le_of_lt (hw₁ z))
  have h2 : b * w₂ z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (le_of_lt (hw₂ z))
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    rw [ha0, hb1]
    simp only [zero_mul, one_mul, zero_add]
    exact hw₂ z
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hlt : a * w₁ z < 0 := mul_neg_of_pos_of_neg hapos (hw₁ z)
    linarith

/-- The affine map whose sublevel set (at `0`) is the separating set. -/
private noncomputable def sepMap
    {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ) :
    ((W →ᵇ ℝ) × ℝ) → (W →ᵇ ℝ) := fun p => p.1 - cb - (p.2 - t) • 1

private theorem sepMap_apply
    {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ)
    (p : (W →ᵇ ℝ) × ℝ) (z : W) :
    sepMap cb t p z = p.1 z - cb z - (p.2 - t) := by
  change (p.1 - cb - (p.2 - t) • 1) z = _
  rw [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.smul_apply]
  congr 1
  have h1 : (1 : (W →ᵇ ℝ)) z = 1 := rfl
  rw [h1, smul_eq_mul, mul_one]

private theorem sepMap_continuous
    {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ) :
    Continuous (sepMap cb t) := by
  have h1 : Continuous (fun p : (W →ᵇ ℝ) × ℝ => p.1 - cb) :=
    continuous_fst.sub continuous_const
  have h2 : Continuous (fun p : (W →ᵇ ℝ) × ℝ => (p.2 - t) • (1 : (W →ᵇ ℝ))) :=
    (continuous_snd.sub continuous_const).smul continuous_const
  have h3 := h1.sub h2
  exact h3

/-- The separating open convex set: pairs strictly below the cost-shifted threshold. -/
private noncomputable def sepSet
    {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ) :
    Set ((W →ᵇ ℝ) × ℝ) := sepMap cb t ⁻¹' {w | ∀ z, w z < 0}

private theorem sepSet_mem
    {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ)
    (p : (W →ᵇ ℝ) × ℝ) :
    p ∈ sepSet cb t ↔ ∀ z, p.1 z - cb z - (p.2 - t) < 0 := by
  constructor
  · intro h z
    have h2 := h z
    rwa [sepMap_apply] at h2
  · intro h z
    show (sepMap cb t p) z < 0
    rw [sepMap_apply]
    exact h z

private theorem isOpen_sepSet
    {W : Type*} [TopologicalSpace W] [CompactSpace W] [Nonempty W]
    (cb : W →ᵇ ℝ) (t : ℝ) : IsOpen (sepSet cb t) :=
  isOpen_negBCF.preimage (sepMap_continuous cb t)

private theorem sepMap_affine
    {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ)
    (p q : (W →ᵇ ℝ) × ℝ) (a b : ℝ) (hab : a + b = 1) :
    sepMap cb t (a • p + b • q) = a • sepMap cb t p + b • sepMap cb t q := by
  apply BoundedContinuousFunction.ext
  intro z
  have e1 : ((a • p + b • q).1) z = a • p.1 z + b • q.1 z := rfl
  have e2 : (a • p + b • q).2 = a • p.2 + b • q.2 := rfl
  rw [sepMap_apply, e1, e2, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.smul_apply,
    sepMap_apply, sepMap_apply]
  simp only [smul_eq_mul]
  linear_combination (cb z - t) * hab

private theorem convex_sepSet
    {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ) :
    Convex ℝ (sepSet cb t) := by
  intro p hp q hq a b ha hb hab
  have hp' : sepMap cb t p ∈ {w : W →ᵇ ℝ | ∀ z, w z < 0} := hp
  have hq' : sepMap cb t q ∈ {w : W →ᵇ ℝ | ∀ z, w z < 0} := hq
  have haff := sepMap_affine cb t p q a b hab
  change sepMap cb t (a • p + b • q) ∈ {w : W →ᵇ ℝ | ∀ z, w z < 0}
  rw [haff]
  exact convex_negBCF hp' hq' ha hb hab

private theorem nonempty_sepSet
    {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ) :
    (sepSet cb t).Nonempty := by
  refine ⟨(cb - 1, t + 1), ?_⟩
  rw [sepSet_mem]
  intro z
  have e : (cb - 1) z = cb z - 1 := rfl
  rw [e]
  linarith

/-- The graph of the dual objective over the sum map, as a submodule. -/
private noncomputable def graphSub
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Submodule ℝ (((X × Y) →ᵇ ℝ) × ℝ) :=
  LinearMap.range (LinearMap.prod PhiLM (dualValLM μ ν))

/-- The graph is disjoint from the separating set. -/
private theorem disjoint_graph_sepSet
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c)
    (Dstar ε : ℝ) (hε : 0 < ε)
    (hD : ∀ (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (m : ℝ),
      (∀ z, (PhiLM d) z - c z ≤ m) →
      (dualValLM (μ : Measure X) (ν : Measure Y) d) - m ≤ Dstar) :
    Disjoint (sepSet (mkBCF c hc) (Dstar + ε))
      (↑(graphSub (μ : Measure X) (ν : Measure Y))) := by
  have eprod : ∀ dd, (LinearMap.prod PhiLM (dualValLM (μ : Measure X) (ν : Measure Y))) dd
      = (PhiLM dd, dualValLM (μ : Measure X) (ν : Measure Y) dd) := fun dd => rfl
  rw [Set.disjoint_left]
  rintro p hpU hpmem
  obtain ⟨d, rfl⟩ := hpmem
  rw [eprod] at hpU
  rw [sepSet_mem] at hpU
  have hpU' : ∀ z, (PhiLM d) z - (mkBCF c hc) z
      - ((dualValLM (μ : Measure X) (ν : Measure Y) d) - (Dstar + ε)) < 0 := hpU
  obtain ⟨z₀, hz₀⟩ := exists_max_attain (PhiLM d - mkBCF c hc)
  have hmax : ∀ z, (PhiLM d) z - c z ≤ (PhiLM d) z₀ - c z₀ := by
    intro z
    have h := hz₀ z
    have e : ∀ w : X × Y, (PhiLM d - mkBCF c hc) w = (PhiLM d) w - c w :=
      fun w => rfl
    rwa [e z, e z₀] at h
  have hkey := hD d ((PhiLM d) z₀ - c z₀) hmax
  have hlt := hpU' z₀
  have e0 : (mkBCF c hc) z₀ = c z₀ := rfl
  rw [e0] at hlt
  linarith

/-- Separation produces a positive linear functional dominating the dual objective. -/
private theorem exists_posFunctional
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Pim : ((X × Y) →ᵇ ℝ) →ₗ[ℝ] ℝ,
      (∀ w, (∀ z, 0 ≤ w z) → 0 ≤ Pim w) ∧
      (∀ d, Pim (PhiLM d) = dualValLM (μ : Measure X) (ν : Measure Y) d) ∧
      Pim (mkBCF c hc) ≤ sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
        DualFeasible c φ ψ ∧
        r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} + ε ∧
      Pim 1 = 1 := by
  set Dstar : ℝ := sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)}
  have hD : ∀ (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (m : ℝ),
      (∀ z, (PhiLM d) z - c z ≤ m) →
      (dualValLM (μ : Measure X) (ν : Measure Y) d) - m ≤ Dstar :=
    fun d m hm => key_le μ ν c hc d m hm
  have hdisj := disjoint_graph_sepSet μ ν c hc Dstar ε hε hD
  have hUopen : IsOpen (sepSet (mkBCF c hc) (Dstar + ε)) := isOpen_sepSet _ _
  have hUconv : Convex ℝ (sepSet (mkBCF c hc) (Dstar + ε)) := convex_sepSet _ _
  have hMconv := Submodule.convex (graphSub (μ : Measure X) (ν : Measure Y))
  obtain ⟨F, γ, hUs, hMt⟩ := geometric_hahn_banach_open hUconv hUopen hMconv hdisj
  have hF0 : ∀ m : ((X × Y) →ᵇ ℝ) × ℝ,
      m ∈ (graphSub (μ : Measure X) (ν : Measure Y)) → F m = 0 := by
    intro m hm
    by_contra hne
    have hmem : ((γ - 1) / F m) • m ∈ (graphSub (μ : Measure X) (ν : Measure Y)) :=
      Submodule.smul_mem _ _ hm
    have hle := hMt _ hmem
    have hFm : F (((γ - 1) / F m) • m) = γ - 1 := by
      rw [F.map_smul, smul_eq_mul, div_mul_cancel₀ _ hne]
    linarith
  set Λ : ((X × Y) →ᵇ ℝ) →ₗ[ℝ] ℝ := F.toLinearMap.comp (LinearMap.inl ℝ _ _)
  have hΛeq : ∀ v, Λ v = F (v, 0) := fun v => rfl
  have hdecomp : ∀ p : ((X × Y) →ᵇ ℝ) × ℝ, F p = Λ p.1 + p.2 * F (0, 1) := by
    intro p
    have e : p = (p.1, 0) + p.2 • (0, 1) := by
      rw [Prod.ext_iff]
      constructor
      · change p.1 = p.1 + p.2 • (0 : (X × Y) →ᵇ ℝ)
        rw [smul_zero, add_zero]
      · change p.2 = (0 : ℝ) + p.2 • (1 : ℝ)
        rw [smul_eq_mul, mul_one, zero_add]
    conv_lhs => rw [e]
    rw [map_add, F.map_smul, smul_eq_mul, hΛeq]
  have h0mem : (0 : ((X × Y) →ᵇ ℝ) × ℝ)
      ∈ (graphSub (μ : Measure X) (ν : Measure Y)) := ⟨0, map_zero _⟩
  have hγ0 : γ ≤ 0 := by
    have hle := hMt _ h0mem
    rw [map_zero] at hle
    exact hle
  have hFne : F ≠ 0 := by
    intro hF0'
    obtain ⟨p₀, hp₀⟩ := nonempty_sepSet (mkBCF c hc) (Dstar + ε)
    have h1 := hUs p₀ hp₀
    have h2 := hMt _ h0mem
    rw [hF0'] at h1 h2
    simp at h1 h2
    linarith
  have hmemCB : ∀ t : ℝ, Dstar + ε < t →
      (mkBCF c hc, t) ∈ sepSet (mkBCF c hc) (Dstar + ε) := by
    intro t ht
    rw [sepSet_mem]
    intro z
    linarith
  have hα0 : F (0, 1) ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set T : ℝ := max (Dstar + ε + 1) ((γ - F (mkBCF c hc, 0) + 1) / F (0, 1)) with hT
    have hT1 : Dstar + ε < T := by
      rw [hT]
      exact lt_max_iff.mpr (Or.inl (by linarith))
    have hlt := hUs _ (hmemCB T hT1)
    rw [hdecomp] at hlt
    have hlt' : Λ (mkBCF c hc) + T * F (0, 1) < γ := hlt
    have hT2 : ((γ - F (mkBCF c hc, 0) + 1) / F (0, 1)) ≤ T := by
      rw [hT]
      exact le_max_right _ _
    have hmul : ((γ - F (mkBCF c hc, 0) + 1) / F (0, 1)) * F (0, 1)
        = γ - F (mkBCF c hc, 0) + 1 := div_mul_cancel₀ _ (ne_of_gt hpos)
    have hge : γ - F (mkBCF c hc, 0) + 1 ≤ T * F (0, 1) := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_right hT2 (le_of_lt hpos)
    have hΛcb : Λ (mkBCF c hc) = F (mkBCF c hc, 0) := hΛeq _
    linarith
  have hpos : ∀ w : (X × Y) →ᵇ ℝ, (∀ z, 0 ≤ w z) → 0 ≤ F (w, 0) := by
    intro w hw
    by_contra hneg
    push Not at hneg
    have hmem : ∀ s : ℝ, 0 ≤ s →
        (mkBCF c hc - s • w, Dstar + ε + 1)
          ∈ sepSet (mkBCF c hc) (Dstar + ε) := by
      intro s hs
      rw [sepSet_mem]
      intro z
      have e1 : (mkBCF c hc - s • w) z = (mkBCF c hc) z - s * w z := by
        rw [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
          smul_eq_mul]
      rw [e1]
      have hsw : 0 ≤ s * w z := mul_nonneg hs (hw z)
      have hD' : (Dstar + ε + 1) - (Dstar + ε) = 1 := by ring
      rw [hD']
      linarith
    set K : ℝ := |F (mkBCF c hc, 0) + (Dstar + ε + 1) * F (0, 1) - γ| + 1 with hK
    have hKpos : 0 < K := by
      rw [hK]
      linarith [abs_nonneg (F (mkBCF c hc, 0) + (Dstar + ε + 1) * F (0, 1) - γ)]
    set s : ℝ := K / (-F (w, 0)) with hs
    have hne : -F (w, 0) ≠ 0 := neg_ne_zero.mpr (ne_of_lt hneg)
    have hs0 : 0 ≤ s := by
      rw [hs]
      exact div_nonneg (le_of_lt hKpos) (le_of_lt (neg_pos.mpr hneg))
    have hlt := hUs _ (hmem s hs0)
    rw [hdecomp] at hlt
    have hlt' : Λ (mkBCF c hc - s • w) + (Dstar + ε + 1) * F (0, 1) < γ := hlt
    have hdec : Λ (mkBCF c hc - s • w)
        = Λ (mkBCF c hc) - s * Λ w := by
      simp only [map_sub, map_smulₛₗ, RingHom.id_apply, smul_eq_mul]
    rw [hdec] at hlt'
    have hsk : s * (-F (w, 0)) = K := by rw [hs]; exact div_mul_cancel₀ _ hne
    have hsk2 : -(s * F (w, 0)) = K := by rw [← hsk]; ring
    have hΛw : Λ w = F (w, 0) := hΛeq _
    have hsk3 : Λ (mkBCF c hc) - s * Λ w = Λ (mkBCF c hc) + K := by
      rw [hΛw, ← hsk2]; ring
    rw [hsk3, hK] at hlt'
    have habs := neg_le_abs (F (mkBCF c hc, 0) + (Dstar + ε + 1) * F (0, 1) - γ)
    have hΛcb : Λ (mkBCF c hc) = F (mkBCF c hc, 0) := hΛeq _
    linarith
  have hgraph : ∀ d : (X →ᵇ ℝ) × (Y →ᵇ ℝ),
      Λ (PhiLM d) + (dualValLM (μ : Measure X) (ν : Measure Y) d) * F (0, 1) = 0 := by
    intro d
    have hm : (PhiLM d, dualValLM (μ : Measure X) (ν : Measure Y) d)
        ∈ (graphSub (μ : Measure X) (ν : Measure Y)) := ⟨d, rfl⟩
    have h0 := hF0 _ hm
    rw [hdecomp] at h0
    have h0' : Λ (PhiLM d)
        + (dualValLM (μ : Measure X) (ν : Measure Y) d) * F (0, 1) = 0 := h0
    exact h0'
  have hαne : F (0, 1) ≠ 0 := by
    intro hα0
    have hΛlt : ∀ v : (X × Y) →ᵇ ℝ, F (v, 0) < γ := by
      intro v
      obtain ⟨z₀, hz₀⟩ := exists_max_attain (v - mkBCF c hc)
      have hmem : (v, Dstar + ε + (v - mkBCF c hc) z₀ + 1)
          ∈ sepSet (mkBCF c hc) (Dstar + ε) := by
        rw [sepSet_mem]
        intro z
        have hle : v z - (mkBCF c hc) z ≤ (v - mkBCF c hc) z₀ := by
          have h := hz₀ z
          have e : ∀ w : X × Y, (v - mkBCF c hc) w = v w - (mkBCF c hc) w :=
            fun w => rfl
          rwa [e z] at h
        linarith
      have h := hUs _ hmem
      rw [hdecomp] at h
      have h' : Λ v + (Dstar + ε + (v - mkBCF c hc) z₀ + 1) * F (0, 1) < γ := h
      rw [hα0, mul_zero, add_zero] at h'
      rw [hΛeq] at h'
      exact h'
    have hΛ0 : ∀ v : (X × Y) →ᵇ ℝ, F (v, 0) = 0 := by
      intro v
      by_contra hnev
      have hlt := hΛlt (((γ + 1) / F (v, 0)) • v)
      have hsc : F ((((γ + 1) / F (v, 0)) • v), 0) = γ + 1 := by
        have e1 : F ((((γ + 1) / F (v, 0)) • v), 0)
            = Λ ((((γ + 1) / F (v, 0)) • v)) := (hΛeq _).symm
        rw [e1, map_smulₛₗ, RingHom.id_apply, smul_eq_mul, hΛeq]
        exact div_mul_cancel₀ _ hnev
      linarith
    have hFall : F = 0 := by
      apply ContinuousLinearMap.ext
      intro p
      rw [hdecomp]
      have h1 : Λ p.1 = 0 := by rw [hΛeq]; exact hΛ0 p.1
      rw [h1, hα0, mul_zero, add_zero]
      rfl
    exact hFne hFall
  have hαneg : F (0, 1) < 0 := lt_of_le_of_ne hα0 hαne
  have hsmul : ∀ v : (X × Y) →ᵇ ℝ,
      (((-F (0, 1))⁻¹ • Λ) v) = (-F (0, 1))⁻¹ * Λ v := by
    intro v
    rw [LinearMap.smul_apply, smul_eq_mul]
  have hPimPhi : ∀ d : (X →ᵇ ℝ) × (Y →ᵇ ℝ),
      (((-F (0, 1))⁻¹ • Λ) (PhiLM d))
        = dualValLM (μ : Measure X) (ν : Measure Y) d := by
    intro d
    rw [hsmul]
    have hgr := hgraph d
    have hF0' : Λ (PhiLM d)
        = -((dualValLM (μ : Measure X) (ν : Measure Y) d) * F (0, 1)) := by
      linarith
    rw [hF0']
    have hαne' : -F (0, 1) ≠ 0 := neg_ne_zero.mpr hαne
    have hinv : (-F (0, 1))⁻¹ * (-F (0, 1)) = 1 := inv_mul_cancel₀ hαne'
    linear_combination (dualValLM (μ : Measure X) (ν : Measure Y) d) * hinv
  have hposPim : ∀ w : (X × Y) →ᵇ ℝ, (∀ z, 0 ≤ w z)
      → 0 ≤ (((-F (0, 1))⁻¹ • Λ) w) := by
    intro w hw
    rw [hsmul]
    have hΛw : 0 ≤ Λ w := by rw [hΛeq]; exact hpos w hw
    have hpos2 : (0:ℝ) ≤ (-F (0, 1))⁻¹ :=
      le_of_lt (inv_pos.mpr (neg_pos.mpr hαneg))
    exact mul_nonneg hpos2 hΛw
  have hlePim : (((-F (0, 1))⁻¹ • Λ) (mkBCF c hc)) ≤ Dstar + ε := by
    have hpos2 : (0:ℝ) < (-F (0, 1))⁻¹ := inv_pos.mpr (neg_pos.mpr hαneg)
    have hlt : ∀ t : ℝ, Dstar + ε < t
        → Λ (mkBCF c hc) + t * F (0, 1) < γ := by
      intro t ht
      have h := hUs _ (hmemCB t ht)
      rw [hdecomp] at h
      have h' : Λ (mkBCF c hc) + t * F (0, 1) < γ := h
      exact h'
    have hPimlt : ∀ t : ℝ, Dstar + ε < t →
        (((-F (0, 1))⁻¹ • Λ) (mkBCF c hc)) < t + (-F (0, 1))⁻¹ * γ := by
      intro t ht
      rw [hsmul]
      have h := hlt t ht
      have hmul := mul_lt_mul_of_pos_left h hpos2
      have hαne' : -F (0, 1) ≠ 0 := neg_ne_zero.mpr hαne
      have hinv : (-F (0, 1))⁻¹ * (-F (0, 1)) = 1 := inv_mul_cancel₀ hαne'
      have h2 : (-F (0, 1))⁻¹ * (t * F (0, 1)) = -t := by
        linear_combination (-t) * hinv
      have heq : (-F (0, 1))⁻¹ * (Λ (mkBCF c hc) + t * F (0, 1))
          = (-F (0, 1))⁻¹ * Λ (mkBCF c hc) - t := by
        calc (-F (0, 1))⁻¹ * (Λ (mkBCF c hc) + t * F (0, 1))
            = (-F (0, 1))⁻¹ * Λ (mkBCF c hc)
              + (-F (0, 1))⁻¹ * (t * F (0, 1)) := by ring
          _ = (-F (0, 1))⁻¹ * Λ (mkBCF c hc) + (-t) := by rw [h2]
          _ = (-F (0, 1))⁻¹ * Λ (mkBCF c hc) - t := by ring
      linarith
    have hle1 : (((-F (0, 1))⁻¹ • Λ) (mkBCF c hc))
        ≤ Dstar + ε + (-F (0, 1))⁻¹ * γ := by
      apply le_of_forall_gt_imp_ge_of_dense
      intro b hb
      have ht : Dstar + ε
          < Dstar + ε + (b - (Dstar + ε + (-F (0, 1))⁻¹ * γ)) / 2 := by
        have hδ : (0:ℝ) < b - (Dstar + ε + (-F (0, 1))⁻¹ * γ) := by linarith
        linarith
      have h := hPimlt _ ht
      linarith
    have hcorr : (-F (0, 1))⁻¹ * γ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos2) hγ0
    linarith
  have h1Pim : (((-F (0, 1))⁻¹ • Λ) 1) = 1 := by
    have h1 : (1 : (X × Y) →ᵇ ℝ) = PhiLM (1, 0) := by
      apply BoundedContinuousFunction.ext
      intro z
      rw [PhiLM_apply]
      have e1 : ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).1 z.1 = 1 := rfl
      have e2 : ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).2 z.2 = 0 := rfl
      have e3 : (1 : (X × Y) →ᵇ ℝ) z = 1 := rfl
      rw [e1, e2, e3]
      ring
    rw [h1]
    rw [hPimPhi]
    have hL1 : (dualValLM (μ : Measure X) (ν : Measure Y) (1, 0)) = 1 := by
      have e : (dualValLM (μ : Measure X) (ν : Measure Y) (1, 0))
          = (∫ x, ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).1 x ∂(μ : Measure X))
            + ∫ y, ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).2 y ∂(ν : Measure Y) := rfl
      rw [e]
      have e1 : (fun x => ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).1 x)
          = (fun _ => (1:ℝ)) := rfl
      have e2 : (fun y => ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).2 y)
          = (fun _ => (0:ℝ)) := rfl
      rw [e1, e2]
      have i1 : (∫ _, (1:ℝ) ∂(μ : Measure X)) = 1 := by simp
      have i0 : (∫ _, (0:ℝ) ∂(ν : Measure Y)) = 0 := by simp
      rw [i1, i0, add_zero]
    exact hL1
  exact ⟨(-F (0, 1))⁻¹ • Λ, hposPim, hPimPhi, hlePim, h1Pim⟩

/-- The first marginal of a finite measure is finite. -/
private instance isFiniteMeasure_map_fst
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.map Prod.fst) :=
  Measure.isFiniteMeasure_map μ Prod.fst

/-- The second marginal of a finite measure is finite. -/
private instance isFiniteMeasure_map_snd
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.map Prod.snd) :=
  Measure.isFiniteMeasure_map μ Prod.snd

/-- Pullback of a compactly supported function along `Prod.fst`. -/
private noncomputable def fstCC
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y]
    (f : C_c(X, ℝ)) : C_c(X × Y, ℝ) :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    ⟨fun z => f z.1, f.toBoundedContinuousFunction.continuous.comp continuous_fst⟩

/-- Pullback of a compactly supported function along `Prod.snd`. -/
private noncomputable def sndCC
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y]
    (g : C_c(Y, ℝ)) : C_c(X × Y, ℝ) :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    ⟨fun z => g z.2, g.toBoundedContinuousFunction.continuous.comp continuous_snd⟩

/-- A positive functional on the product gives a coupling via Riesz representation. -/
private theorem coupling_of_posFunctional
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c)
    (Dstar ε : ℝ)
    (Pim : ((X × Y) →ᵇ ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀ w, (∀ z, 0 ≤ w z) → 0 ≤ Pim w)
    (hPhi : ∀ d, Pim (PhiLM d) = dualValLM (μ : Measure X) (ν : Measure Y) d)
    (hcost : Pim (mkBCF c hc) ≤ Dstar + ε)
    (hone : Pim 1 = 1) :
    ∃ π : ProbabilityMeasure (X × Y), IsCoupling μ ν π ∧
      (∫ p, c p ∂(π : Measure (X × Y))) ≤ Dstar + ε := by
  have eadd : ∀ g h : C_c(X × Y, ℝ), (g + h).toBoundedContinuousFunction
      = g.toBoundedContinuousFunction + h.toBoundedContinuousFunction := by
    intro g h
    apply BoundedContinuousFunction.ext
    intro z
    rfl
  have esmul : ∀ (a : ℝ) (g : C_c(X × Y, ℝ)), (a • g).toBoundedContinuousFunction
      = a • g.toBoundedContinuousFunction := by
    intro a g
    apply BoundedContinuousFunction.ext
    intro z
    rfl
  let ΛR : C_c(X × Y, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun g => Pim (g.toBoundedContinuousFunction)
      map_add' := fun g h => by
        change Pim ((g + h).toBoundedContinuousFunction)
          = Pim (g.toBoundedContinuousFunction) + Pim (h.toBoundedContinuousFunction)
        rw [eadd, map_add]
      map_smul' := fun a g => by
        change Pim ((a • g).toBoundedContinuousFunction)
          = a • Pim (g.toBoundedContinuousFunction)
        rw [esmul, map_smulₛₗ, RingHom.id_apply]
      monotone' := fun g h hgh => by
        change Pim (g.toBoundedContinuousFunction) ≤ Pim (h.toBoundedContinuousFunction)
        have hle : ∀ z, (g.toBoundedContinuousFunction) z
            ≤ (h.toBoundedContinuousFunction) z :=
          fun z => CompactlySupportedContinuousMap.le_def.mp hgh z
        have hnonneg : 0
            ≤ Pim (h.toBoundedContinuousFunction - g.toBoundedContinuousFunction) :=
          hpos _ (fun z => by
            rw [BoundedContinuousFunction.sub_apply]
            linarith [hle z])
        have hadd : Pim (h.toBoundedContinuousFunction - g.toBoundedContinuousFunction)
            = Pim (h.toBoundedContinuousFunction) - Pim (g.toBoundedContinuousFunction) := by
          rw [map_sub]
        linarith }
  have hΛR : ∀ g : C_c(X × Y, ℝ), ΛR g = Pim (g.toBoundedContinuousFunction) :=
    fun g => rfl
  set πM : Measure (X × Y) := RealRMK.rieszMeasure ΛR with hπM
  set one_cc : C_c(X × Y, ℝ) :=
    CompactlySupportedContinuousMap.continuousMapEquiv 1 with honecc
  have eBCFone : one_cc.toBoundedContinuousFunction = 1 := by
    apply BoundedContinuousFunction.ext
    intro z
    rfl
  have hmass : πM Set.univ = 1 := by
    have e1 : (∫ _, (1:ℝ) ∂πM) = (πM Set.univ).toReal := by
      rw [integral_const, smul_eq_mul, mul_one, measureReal_def]
    have e2 : (∫ _, (1:ℝ) ∂πM) = ΛR one_cc := by
      have hriesz := RealRMK.integral_rieszMeasure ΛR one_cc
      have e : (fun x : X × Y => one_cc x) = (fun _ => (1:ℝ)) :=
        funext fun z => rfl
      rw [← e]
      exact hriesz
    have h1 : (πM Set.univ).toReal = 1 := by
      rw [← e1, e2, hΛR, eBCFone]
      exact hone
    have hne : πM Set.univ ≠ ∞ := measure_ne_top πM _
    have h := ENNReal.ofReal_toReal hne
    rw [h1, ENNReal.ofReal_one] at h
    exact h.symm
  refine ⟨⟨πM, ⟨hmass⟩⟩, ?_, ?_⟩
  · constructor
    · change (μ : Measure X) = πM.map Prod.fst
      have hinter : ∀ f : C_c(X, ℝ), (∫ x, f x ∂(μ : Measure X))
          = ∫ x, f x ∂(πM.map Prod.fst) := by
        intro f
        have hfcont : Continuous (⇑f) := f.toBoundedContinuousFunction.continuous
        have hfmeas : AEStronglyMeasurable (⇑f) (πM.map Prod.fst) :=
          hfcont.aestronglyMeasurable
        have hmap : (∫ x, f x ∂(πM.map Prod.fst)) = ∫ z, f z.1 ∂πM :=
          integral_map measurable_fst.aemeasurable hfmeas
        have hriesz : (∫ z, f z.1 ∂πM) = ΛR (fstCC (Y := Y) f) :=
          RealRMK.integral_rieszMeasure ΛR (fstCC (Y := Y) f)
        have eBCF : (fstCC (Y := Y) f).toBoundedContinuousFunction
            = PhiLM (f.toBoundedContinuousFunction, 0) := by
          apply BoundedContinuousFunction.ext
          intro z
          change f z.1 = (PhiLM (f.toBoundedContinuousFunction, 0)) z
          rw [PhiLM_apply]
          change f z.1 = f z.1 + 0
          ring
        have hΛ : ΛR (fstCC (Y := Y) f)
            = Pim (PhiLM (f.toBoundedContinuousFunction, 0)) := by
          rw [hΛR, eBCF]
        have hPhi' := hPhi (f.toBoundedContinuousFunction, 0)
        have hL : (dualValLM (μ : Measure X) (ν : Measure Y)
            (f.toBoundedContinuousFunction, 0)) = ∫ x, f x ∂(μ : Measure X) := by
          have e : (dualValLM (μ : Measure X) (ν : Measure Y)
              (f.toBoundedContinuousFunction, 0))
              = (∫ x, f.toBoundedContinuousFunction x ∂(μ : Measure X))
                + ∫ y, (0 : Y →ᵇ ℝ) y ∂(ν : Measure Y) := rfl
          have z0 : (∫ y, (0 : Y →ᵇ ℝ) y ∂(ν : Measure Y)) = 0 := by
            have e0 : (fun y => (0 : Y →ᵇ ℝ) y) = (fun _ => (0:ℝ)) := rfl
            rw [e0]
            simp
          have ef : (fun x => f.toBoundedContinuousFunction x) = (fun x => f x) := rfl
          rw [e, z0, add_zero, ef]
        rw [hmap, hriesz, hΛ, hPhi']
        exact hL.symm
      exact MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported hinter
    · change (ν : Measure Y) = πM.map Prod.snd
      have hinter : ∀ g : C_c(Y, ℝ), (∫ y, g y ∂(ν : Measure Y))
          = ∫ y, g y ∂(πM.map Prod.snd) := by
        intro g
        have hgcont : Continuous (⇑g) := g.toBoundedContinuousFunction.continuous
        have hgmeas : AEStronglyMeasurable (⇑g) (πM.map Prod.snd) :=
          hgcont.aestronglyMeasurable
        have hmap : (∫ y, g y ∂(πM.map Prod.snd)) = ∫ z, g z.2 ∂πM :=
          integral_map measurable_snd.aemeasurable hgmeas
        have hriesz : (∫ z, g z.2 ∂πM) = ΛR (sndCC (X := X) g) :=
          RealRMK.integral_rieszMeasure ΛR (sndCC (X := X) g)
        have eBCF : (sndCC (X := X) g).toBoundedContinuousFunction
            = PhiLM (0, g.toBoundedContinuousFunction) := by
          apply BoundedContinuousFunction.ext
          intro z
          change g z.2 = (PhiLM (0, g.toBoundedContinuousFunction)) z
          rw [PhiLM_apply]
          change g z.2 = 0 + g z.2
          ring
        have hΛ : ΛR (sndCC (X := X) g)
            = Pim (PhiLM (0, g.toBoundedContinuousFunction)) := by
          rw [hΛR, eBCF]
        have hPhi' := hPhi (0, g.toBoundedContinuousFunction)
        have hL : (dualValLM (μ : Measure X) (ν : Measure Y)
            (0, g.toBoundedContinuousFunction)) = ∫ y, g y ∂(ν : Measure Y) := by
          have e : (dualValLM (μ : Measure X) (ν : Measure Y)
              (0, g.toBoundedContinuousFunction))
              = (∫ x, (0 : X →ᵇ ℝ) x ∂(μ : Measure X))
                + ∫ y, g.toBoundedContinuousFunction y ∂(ν : Measure Y) := rfl
          have z0 : (∫ x, (0 : X →ᵇ ℝ) x ∂(μ : Measure X)) = 0 := by
            have e0 : (fun x => (0 : X →ᵇ ℝ) x) = (fun _ => (0:ℝ)) := rfl
            rw [e0]
            simp
          have ef : (fun y => g.toBoundedContinuousFunction y) = (fun y => g y) := rfl
          rw [e, z0, zero_add, ef]
        rw [hmap, hriesz, hΛ, hPhi']
        exact hL.symm
      exact MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported hinter
  · change (∫ z, c z ∂πM) ≤ Dstar + ε
    set costCC : C_c(X × Y, ℝ) :=
      CompactlySupportedContinuousMap.continuousMapEquiv ⟨c, hc⟩ with hcostCC
    have hriesz : (∫ z, c z ∂πM) = ΛR costCC :=
      RealRMK.integral_rieszMeasure ΛR costCC
    have eBCF : costCC.toBoundedContinuousFunction = mkBCF c hc := by
      apply BoundedContinuousFunction.ext
      intro z
      rfl
    rw [hriesz, hΛR, eBCF]
    exact hcost

/--
**Kantorovich duality on compact metric spaces.** Let $X$ and $Y$ be nonempty compact metric
spaces, each carrying its Borel $\sigma$-algebra, let $\mu$ and $\nu$ be probability measures on
$X$ and $Y$, and let $c : X \times Y \to \mathbb{R}$ be continuous. Then the infimum of
$\int c \, d\pi$ over all couplings $\pi$ of $\mu$ and $\nu$ equals the supremum of
$\int \varphi \, d\mu + \int \psi \, d\nu$ over all pairs of continuous functions
$\varphi : X \to \mathbb{R}$ and $\psi : Y \to \mathbb{R}$ such that
$\varphi(x) + \psi(y) \le c(x, y)$ for all $x \in X$ and $y \in Y$.

Proves `Wanted` entry `kantorovich_duality_compact`.

Source: L. V. Kantorovich, On the Translocation of Masses (1942); English transl. J. Math. Sci. 133
(2006), 1381-1382, DOI 10.1007/S10958-006-0049-2; modern ref C. Villani, Topics in Optimal
Transportation (2003).
-/
theorem kantorovich_duality_compact
    {X Y : Type*}
    [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c) :
    sInf (primalValues μ ν c) =
    sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} := by
  have hP : (primalValues μ ν c).Nonempty := primalValues_nonempty μ ν c
  have hD : {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)}.Nonempty :=
    dualValues_nonempty μ ν c hc
  apply le_antisymm
  · have hε : ∀ ε : ℝ, 0 < ε → sInf (primalValues μ ν c) ≤ sSup {r : ℝ |
        ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
        DualFeasible c φ ψ ∧
        r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} + ε := by
      intro ε hε
      obtain ⟨Pim, hpos, hPhi, hcost, hone⟩ := exists_posFunctional μ ν c hc ε hε
      obtain ⟨π, hcoup, hle⟩ :=
        coupling_of_posFunctional μ ν c hc _ ε Pim hpos hPhi hcost hone
      have hmem : (∫ p, c p ∂(π : Measure (X × Y))) ∈ primalValues μ ν c :=
        ⟨π, hcoup, rfl⟩
      have hbdd := primal_bddBelow μ ν c hc
      exact le_trans (csInf_le hbdd hmem) hle
    apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    have h := hε (b - sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)}) (by linarith)
    linarith
  · apply csSup_le hD
    rintro r ⟨φ, ψ, hfeas, rfl⟩
    apply le_csInf hP
    rintro q ⟨π, hπ, rfl⟩
    obtain ⟨hφ, hψ, hle⟩ := hfeas
    exact dual_le_primal_of_isCoupling μ ν c hc φ ψ hφ hψ hle π hπ

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end
