/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Foundations.Ergodicity
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

open Filter MeasureTheory Topology

namespace StatMech
namespace FrontierB



abbrev InfiniteCurrentConfig (E : Type*) := E → ℕ


def WeakCurrentConverges {E : Type*} [Countable E]
    (mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E))
    (nu : ProbabilityMeasure (InfiniteCurrentConfig E)) : Prop :=
  Tendsto mu atTop (nhds nu)


def restrictCurrent {E : Type*} (S : Finset E) (n : InfiniteCurrentConfig E) :
    ↑S → ℕ := fun e => n e.1

theorem continuous_restrictCurrent {E : Type*} (S : Finset E) :
    Continuous (restrictCurrent S : InfiniteCurrentConfig E → (↑S → ℕ)) :=
  continuous_pi fun e => continuous_apply e.1


noncomputable def currentMarginal {E : Type*} [Countable E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) (S : Finset E) :
    ProbabilityMeasure (↑S → ℕ) :=
  mu.map (continuous_restrictCurrent S).measurable.aemeasurable




theorem WeakCurrentConverges.marginal {E : Type*} [Countable E]
    {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (h : WeakCurrentConverges mu nu) (S : Finset E) :
    Tendsto (fun k => currentMarginal (mu k) S) atTop
      (nhds (currentMarginal nu S)) := by
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    mu nu h (continuous_restrictCurrent S)



def currentTrace {E : Type*} (n : InfiniteCurrentConfig E) : ConfigSpace E :=
  fun e => decide (0 < n e)

theorem currentTrace_apply {E : Type*} (n : InfiniteCurrentConfig E) (e : E) :
    currentTrace n e = true ↔ 0 < n e := by
  simp [currentTrace]



theorem continuous_currentTrace {E : Type*} :
    Continuous (currentTrace : InfiniteCurrentConfig E → ConfigSpace E) := by
  refine continuous_pi fun e => ?_
  exact (continuous_of_discreteTopology (f := fun k : ℕ => decide (0 < k))).comp
    (continuous_apply e)


noncomputable def currentTraceLaw {E : Type*} [Countable E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) :
    ProbabilityMeasure (ConfigSpace E) :=
  mu.map continuous_currentTrace.measurable.aemeasurable




theorem WeakCurrentConverges.trace {E : Type*} [Countable E]
    {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (h : WeakCurrentConverges mu nu) :
    Tendsto (fun k => currentTraceLaw (mu k)) atTop
      (nhds (currentTraceLaw nu)) := by
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    mu nu h continuous_currentTrace


def superposedCurrentTrace {E : Type*}
    (n : InfiniteCurrentConfig E × InfiniteCurrentConfig E) : ConfigSpace E :=
  fun e => decide (0 < n.1 e + n.2 e)

theorem superposedCurrentTrace_apply {E : Type*}
    (n : InfiniteCurrentConfig E × InfiniteCurrentConfig E) (e : E) :
    superposedCurrentTrace n e = true ↔ 0 < n.1 e + n.2 e := by
  simp [superposedCurrentTrace]

theorem continuous_superposedCurrentTrace {E : Type*} :
    Continuous
      (superposedCurrentTrace :
        InfiniteCurrentConfig E × InfiniteCurrentConfig E → ConfigSpace E) := by
  refine continuous_pi fun e => ?_
  exact (continuous_of_discreteTopology
    (f := fun k : ℕ => decide (0 < k))).comp
      (((continuous_apply e).comp continuous_fst).add
        ((continuous_apply e).comp continuous_snd))


noncomputable def independentSuperposedTraceLaw {E : Type*} [Countable E]
    (mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)) :
    ProbabilityMeasure (ConfigSpace E) :=
  (mu.prod nu).map continuous_superposedCurrentTrace.measurable.aemeasurable


theorem independentSuperposedTraceLaw_comm {E : Type*} [Countable E]
    (mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)) :
    independentSuperposedTraceLaw mu nu =
      independentSuperposedTraceLaw nu mu := by
  unfold independentSuperposedTraceLaw
  apply Subtype.ext
  change Measure.map (@superposedCurrentTrace E)
      ((mu : Measure _).prod (nu : Measure _)) =
    Measure.map (@superposedCurrentTrace E)
      ((nu : Measure _).prod (mu : Measure _))
  rw [← Measure.prod_swap]
  rw [Measure.map_map continuous_superposedCurrentTrace.measurable measurable_swap]
  congr 1
  funext z e
  rcases z with ⟨a, b⟩
  simp [Function.comp_apply, superposedCurrentTrace, Nat.add_comm]



theorem independentSuperposedTraceLaw_tendsto {E : Type*} [Countable E]
    {mu nu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {muLim nuLim : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (hmu : WeakCurrentConverges mu muLim)
    (hnu : WeakCurrentConverges nu nuLim) :
    Tendsto (fun k => independentSuperposedTraceLaw (mu k) (nu k)) atTop
      (nhds (independentSuperposedTraceLaw muLim nuLim)) := by
  have hpair : Tendsto (fun k => (mu k, nu k)) atTop (nhds (muLim, nuLim)) :=
    hmu.prodMk_nhds hnu
  have hprod : Tendsto (fun k => (mu k).prod (nu k)) atTop
      (nhds (muLim.prod nuLim)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpair
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun k => (mu k).prod (nu k)) (muLim.prod nuLim) hprod
      continuous_superposedCurrentTrace





def currentShift {E H : Type*} [Group H] [MulAction H E]
    (g : H) (n : InfiniteCurrentConfig E) : InfiniteCurrentConfig E :=
  fun e => n (g⁻¹ • e)

theorem measurable_currentShift {E H : Type*} [Group H] [MulAction H E]
    (g : H) : Measurable (currentShift g : InfiniteCurrentConfig E → InfiniteCurrentConfig E) :=
  measurable_pi_lambda _ fun e => measurable_pi_apply (g⁻¹ • e)

theorem continuous_currentShift {E H : Type*} [Group H] [MulAction H E]
    (g : H) : Continuous (currentShift g : InfiniteCurrentConfig E → InfiniteCurrentConfig E) :=
  continuous_pi fun e => continuous_apply (g⁻¹ • e)


def CurrentIsTranslationInvariant {E H : Type*} [Group H] [MulAction H E]
    (mu : Measure (InfiniteCurrentConfig E)) : Prop :=
  ∀ g : H, MeasurePreserving (currentShift g) mu mu



def CurrentIsErgodic {E H : Type*} [Group H] [MulAction H E]
    (mu : Measure (InfiniteCurrentConfig E)) : Prop :=
  CurrentIsTranslationInvariant (H := H) mu ∧
    ∀ s : Set (InfiniteCurrentConfig E), MeasurableSet s →
      (∀ g : H, (currentShift g) ⁻¹' s = s) →
        mu s = 0 ∨ mu s = mu Set.univ



theorem currentTrace_semiconj {E H : Type*} [Group H] [MulAction H E]
    (g : H) : Function.Semiconj
      (currentTrace : InfiniteCurrentConfig E → ConfigSpace E)
      (currentShift g) (ConfigSpace.shift g) := by
  intro n
  rfl



theorem currentTrace_measurePreserving {E : Type*} [Countable E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) :
    MeasurePreserving currentTrace (mu : Measure (InfiniteCurrentConfig E))
      (currentTraceLaw mu : Measure (ConfigSpace E)) := by
  change MeasurePreserving currentTrace (mu : Measure (InfiniteCurrentConfig E))
    (Measure.map currentTrace (mu : Measure (InfiniteCurrentConfig E)))
  exact continuous_currentTrace.measurable.measurePreserving _



theorem CurrentIsTranslationInvariant.trace {E H : Type*} [Countable E]
    [Group H] [MulAction H E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (h : CurrentIsTranslationInvariant (H := H)
      (mu : Measure (InfiniteCurrentConfig E))) :
    ConfigSpace.IsTranslationInvariant (G := H)
      (currentTraceLaw mu : Measure (ConfigSpace E)) := by
  intro g
  exact (currentTrace_measurePreserving mu).of_semiconj (h g)
    (currentTrace_semiconj g) (ConfigSpace.measurable_shift g)


theorem CurrentIsErgodic.trace {E H : Type*} [Countable E]
    [Group H] [MulAction H E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (h : CurrentIsErgodic (H := H)
      (mu : Measure (InfiniteCurrentConfig E))) :
    ConfigSpace.IsErgodic (G := H)
      (currentTraceLaw mu : Measure (ConfigSpace E)) := by
  refine ⟨h.1.trace mu, ?_⟩
  intro s hs hinv
  have hfactor := currentTrace_measurePreserving mu
  have hpre : MeasurableSet (currentTrace ⁻¹' s) :=
    continuous_currentTrace.measurable hs
  have hpreInv : ∀ g : H, (currentShift g) ⁻¹' (currentTrace ⁻¹' s) =
      currentTrace ⁻¹' s := by
    intro g
    ext n
    change ConfigSpace.shift g (currentTrace n) ∈ s ↔ currentTrace n ∈ s
    exact Set.ext_iff.mp (hinv g) (currentTrace n)
  rcases h.2 (currentTrace ⁻¹' s) hpre hpreInv with hzero | hfull
  · left
    rw [← hfactor.measure_preimage hs.nullMeasurableSet]
    exact hzero
  · right
    rw [← hfactor.measure_preimage hs.nullMeasurableSet,
      ← hfactor.measure_preimage MeasurableSet.univ.nullMeasurableSet]
    exact hfull

end FrontierB
end StatMech
