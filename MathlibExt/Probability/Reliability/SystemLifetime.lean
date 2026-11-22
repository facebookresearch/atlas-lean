/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.IncreasingEvent
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable lifetime of a monotone Boolean system

Event/lifetime bridge for a monotone Boolean system on a finite
component type `E`, reusing `StatMech.ConfigSpace` and `StatMech.IsIncreasing`.

Component lifetimes take values in `ENNReal`, so zero and infinity are genuine
values. Observation time `t` is `NNReal`, hence finite. Up at `t` means
`(t : ENNReal) < T e` with strict inequality.

* C1 defines `Reliability.configLifetime` as the finite minimum of `T e`
  over components with `x e = true` (empty minimum is `⊤`), and
  `Reliability.systemLifetime` as the finite maximum over `x ∈ A` of those
  minima (empty maximum is `0`). All configurations in `A` are used.
* C2 is `Reliability.lt_systemLifetime_iff`: for every `T` and finite `t`,
  `t < systemLifetime` iff the strictly-up configuration lies in `A`, assuming
  `StatMech.IsIncreasing A`. Strict ties, zero and infinite lifetimes included.
* C3 is `Reliability.measurable_systemLifetime`: for fixed `A` and
  measurable component functions, the system lifetime is measurable.
* C4 is `Reliability.systemLifetime_series` and
  `Reliability.systemLifetime_parallel`, with empty-component cases.
* C5 is `Reliability.systemLifetime_empty` and
  `Reliability.systemLifetime_univ`, plus series/parallel membership equations.
-/

@[expose] public section

namespace Reliability

/-- Source C2: up-configuration at finite time `t`. A component `e` is up iff
`(t : ENNReal) < T e` with strict inequality, so ties with `t` are down. Zero
and infinite lifetimes are included via the `ENNReal` order. -/
noncomputable def upConfig (E : Type*) (T : E → ENNReal) (t : NNReal) :
    StatMech.ConfigSpace E :=
  fun e => @decide ((t : ENNReal) < T e) (Classical.propDecidable ((t : ENNReal) < T e))

/-- Source C2: characterization of `upConfig`. The `Bool` is `true` exactly for
strictly-up components. -/
theorem upConfig_apply_eq_true (E : Type*) (T : E → ENNReal) (t : NNReal) (e : E) :
    (upConfig E T t e = true ↔ (t : ENNReal) < T e) :=
  ⟨@of_decide_eq_true _ (Classical.propDecidable _),
    @decide_eq_true _ (Classical.propDecidable _)⟩

/-- Source C1: per-configuration lifetime, the finite minimum of `T e` over
components `e` with `x e = true`. The minimum over no selected components is
`⊤` by the `Finset.inf` empty convention. -/
noncomputable def configLifetime (E : Type*) [Fintype E]
    (x : StatMech.ConfigSpace E) (T : E → ENNReal) : ENNReal :=
  (Finset.univ.filter (fun e => x e = true)).inf T

/-- Source C1: the all-down configuration selects no components, so its lifetime
is infinity. -/
theorem configLifetime_allFalse (E : Type*) [Fintype E] (T : E → ENNReal) :
    configLifetime E (fun _ => false) T = ⊤ := by
  unfold configLifetime
  have h : ∀ e ∈ (Finset.univ : Finset E), ¬ ((fun _ => false) e = true) := by
    intro e _
    simp
  rw [Finset.filter_false_of_mem h, Finset.inf_empty]

/-- Source C1/C2: finite-time characterization of `configLifetime`. For finite
`t`, `t` is below the minimum iff it is below every selected component. The
`ENNReal` cast of `t` is strictly below `⊤`, discharging the empty-infimum
premise. -/
theorem lt_configLifetime_iff (E : Type*) [Fintype E]
    (x : StatMech.ConfigSpace E) (T : E → ENNReal) (t : NNReal) :
    ((t : ENNReal) < configLifetime E x T ↔
      ∀ e, x e = true → (t : ENNReal) < T e) := by
  unfold configLifetime
  rw [Finset.lt_inf_iff ENNReal.coe_lt_top]
  constructor
  · intro h e he
    exact h e (Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩)
  · intro h e he
    rw [Finset.mem_filter] at he
    exact h e he.2

/-- Source C1: system lifetime, the finite maximum over `x ∈ A` of
`configLifetime`. The maximum over the empty event is `0` by the `Finset.sup`
empty convention. All configurations in `A` are used; this is not stated as a
minimal-path-set theorem. -/
noncomputable def systemLifetime (E : Type*) [Fintype E]
    (A : Set (StatMech.ConfigSpace E))
    (T : E → ENNReal) : ENNReal :=
  let _ft : Fintype (StatMech.ConfigSpace E) := Fintype.ofFinite _
  let _dp : DecidablePred (fun x : StatMech.ConfigSpace E => x ∈ A) :=
    fun x => Classical.propDecidable (x ∈ A)
  (Finset.univ.filter (fun x => x ∈ A)).sup (fun x => configLifetime E x T)

/-- Source C2: event identity for an increasing event. For every lifetime vector
`T` and finite time `t`, `t` is strictly below the system lifetime iff the
strictly-up configuration lies in `A`, under `StatMech.IsIncreasing A`. This is
an event identity, not an independence assertion. Stated only at finite `t`. -/
theorem lt_systemLifetime_iff (E : Type*) [Fintype E]
    (A : Set (StatMech.ConfigSpace E))
    (T : E → ENNReal) (t : NNReal) (hA : StatMech.IsIncreasing A) :
    ((t : ENNReal) < systemLifetime E A T ↔ upConfig E T t ∈ A) := by
  let _ft : Fintype (StatMech.ConfigSpace E) := Fintype.ofFinite _
  let _dp : DecidablePred (fun x : StatMech.ConfigSpace E => x ∈ A) :=
    fun x => Classical.propDecidable (x ∈ A)
  unfold systemLifetime
  rw [Finset.lt_sup_iff]
  constructor
  · rintro ⟨x, hxmem, hlt⟩
    rw [Finset.mem_filter] at hxmem
    rw [lt_configLifetime_iff] at hlt
    have hle : x ≤ upConfig E T t := fun e =>
      Bool.le_iff_imp.mpr (fun he => (upConfig_apply_eq_true E T t e).mpr (hlt e he))
    exact hA hle hxmem.2
  · intro hmem
    refine ⟨upConfig E T t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩, ?_⟩
    rw [lt_configLifetime_iff]
    intro e he
    exact (upConfig_apply_eq_true E T t e).mp he

/-- Source C3: measurability of the system lifetime. `A` is fixed; no
probability measure or independence hypothesis is needed. Each `T e` is a
measurable `Ω → ENNReal` function. -/
theorem measurable_systemLifetime (E : Type*) [Fintype E]
    (A : Set (StatMech.ConfigSpace E))
    (Ω : Type*) [MeasurableSpace Ω] (T : E → Ω → ENNReal)
    (hT : ∀ e, Measurable (T e)) :
    Measurable (fun ω => systemLifetime E A (fun e => T e ω)) := by
  unfold systemLifetime configLifetime
  simp only [Finset.sup_eq_iSup, Finset.inf_eq_iInf, ← Finset.mem_coe]
  exact Measurable.biSup _ (Finset.countable_toSet _)
    (fun x _ => Measurable.biInf _ (Finset.countable_toSet _) (fun e _ => hT e))

/-- Source C4: all-components-up (series) event. -/
def seriesEvent (E : Type*) : Set (StatMech.ConfigSpace E) :=
  {x | ∀ e, x e = true}

/-- Source C4: some-component-up (parallel) event. -/
def parallelEvent (E : Type*) : Set (StatMech.ConfigSpace E) :=
  {x | ∃ e, x e = true}

/-- Source C4: membership characterization of the series event. -/
theorem mem_seriesEvent (E : Type*) (x : StatMech.ConfigSpace E) :
    (x ∈ seriesEvent E ↔ ∀ e, x e = true) :=
  Iff.rfl

/-- Source C4: membership characterization of the parallel event. -/
theorem mem_parallelEvent (E : Type*) (x : StatMech.ConfigSpace E) :
    (x ∈ parallelEvent E ↔ ∃ e, x e = true) :=
  Iff.rfl

/-- Source C4: the series event is increasing: a pointwise-larger configuration
is also all-up. Applies to the generic survival identity. -/
theorem isIncreasing_seriesEvent (E : Type*) :
    StatMech.IsIncreasing (seriesEvent E) := by
  intro x y hle hmem
  rw [mem_seriesEvent] at hmem ⊢
  intro e
  exact (Bool.le_iff_imp.mp (hle e)) (hmem e)

/-- Source C4: the parallel event is increasing: a pointwise-larger
configuration keeps the witnessing up-component. Applies to the generic
survival identity. -/
theorem isIncreasing_parallelEvent (E : Type*) :
    StatMech.IsIncreasing (parallelEvent E) := by
  intro x y hle hmem
  rw [mem_parallelEvent] at hmem ⊢
  obtain ⟨e₀, he₀⟩ := hmem
  exact ⟨e₀, (Bool.le_iff_imp.mp (hle e₀)) he₀⟩

/-- Source C4: series lifetime is the minimum component lifetime. -/
theorem systemLifetime_series (E : Type*) [Fintype E] (T : E → ENNReal) :
    systemLifetime E (seriesEvent E) T = Finset.univ.inf T := by
  let _ft : Fintype (StatMech.ConfigSpace E) := Fintype.ofFinite _
  let _dp : DecidablePred (fun x : StatMech.ConfigSpace E => x ∈ seriesEvent E) :=
    fun x => Classical.propDecidable (x ∈ seriesEvent E)
  have hmem : (fun _ => true) ∈
      Finset.univ.filter (fun x : StatMech.ConfigSpace E => x ∈ seriesEvent E) := by
    rw [Finset.mem_filter, mem_seriesEvent]
    exact ⟨Finset.mem_univ _, fun _ => rfl⟩
  have hle : ∀ x ∈ Finset.univ.filter (fun x : StatMech.ConfigSpace E => x ∈ seriesEvent E),
      configLifetime E x T ≤ configLifetime E (fun _ => true) T := by
    intro x hx
    rw [Finset.mem_filter, mem_seriesEvent] at hx
    have hxeq : x = (fun _ => true) := funext fun e => hx.2 e
    rw [hxeq]
  have hsup : (Finset.univ.filter (fun x : StatMech.ConfigSpace E => x ∈ seriesEvent E)).sup
      (fun x => configLifetime E x T) = configLifetime E (fun _ => true) T := by
    apply le_antisymm
    · exact Finset.sup_le hle
    · exact Finset.le_sup (f := fun x => configLifetime E x T) hmem
  have huniv : Finset.univ.filter (fun e : E => (fun _ => true) e = true) = Finset.univ :=
    Finset.filter_true_of_mem (fun e _ => rfl)
  unfold systemLifetime
  rw [hsup]
  unfold configLifetime
  rw [huniv]

/-- Source C4: parallel lifetime is the maximum component lifetime. -/
theorem systemLifetime_parallel (E : Type*) [Fintype E] (T : E → ENNReal) :
    systemLifetime E (parallelEvent E) T = Finset.univ.sup T := by
  let _ft : Fintype (StatMech.ConfigSpace E) := Fintype.ofFinite _
  let _dp : DecidablePred (fun x : StatMech.ConfigSpace E => x ∈ parallelEvent E) :=
    fun x => Classical.propDecidable (x ∈ parallelEvent E)
  let _de : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  have hle : ∀ x ∈ Finset.univ.filter (fun x : StatMech.ConfigSpace E => x ∈ parallelEvent E),
      configLifetime E x T ≤ Finset.univ.sup T := by
    intro x hx
    rw [Finset.mem_filter, mem_parallelEvent] at hx
    obtain ⟨e₀, he₀⟩ := hx.2
    have hmem : e₀ ∈ Finset.univ.filter (fun e : E => x e = true) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ e₀, he₀⟩
    unfold configLifetime
    exact le_trans (Finset.inf_le hmem) (Finset.le_sup (Finset.mem_univ e₀))
  have hge : ∀ e ∈ (Finset.univ : Finset E),
      T e ≤ (Finset.univ.filter (fun x : StatMech.ConfigSpace E => x ∈ parallelEvent E)).sup
        (fun x => configLifetime E x T) := by
    intro e _
    let c : StatMech.ConfigSpace E := fun e' => decide (e' = e)
    have hcT : configLifetime E c T = T e := by
      have hset : Finset.univ.filter (fun e' : E => c e' = true) = {e} := by
        ext e'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨of_decide_eq_true, decide_eq_true⟩
      unfold configLifetime
      rw [hset, Finset.inf_singleton]
    have hcmem : c ∈
        Finset.univ.filter (fun x : StatMech.ConfigSpace E => x ∈ parallelEvent E) := by
      rw [Finset.mem_filter, mem_parallelEvent]
      exact ⟨Finset.mem_univ c, e, decide_eq_true rfl⟩
    calc T e = configLifetime E c T := hcT.symm
      _ ≤ _ := Finset.le_sup (f := fun x => configLifetime E x T) hcmem
  unfold systemLifetime
  exact le_antisymm (Finset.sup_le hle) (Finset.sup_le hge)

/-- Source C4: with no components the series event is universal (always up). -/
theorem seriesEvent_empty (E : Type*) [IsEmpty E] :
    seriesEvent E = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [mem_seriesEvent]
  intro e
  exact IsEmpty.elim inferInstance e

/-- Source C4: with no components the parallel event is empty (never up). -/
theorem parallelEvent_empty (E : Type*) [IsEmpty E] :
    parallelEvent E = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x
  rw [mem_parallelEvent]
  rintro ⟨e, _⟩
  exact IsEmpty.elim inferInstance e

/-- Source C4: with no components the series lifetime is infinity. -/
theorem systemLifetime_series_empty (E : Type*) [Fintype E]
    [IsEmpty E] (T : E → ENNReal) :
    systemLifetime E (seriesEvent E) T = ⊤ := by
  rw [systemLifetime_series, Finset.univ_eq_empty, Finset.inf_empty]

/-- Source C4: with no components the parallel lifetime is zero. -/
theorem systemLifetime_parallel_empty (E : Type*) [Fintype E]
    [IsEmpty E] (T : E → ENNReal) :
    systemLifetime E (parallelEvent E) T = 0 := by
  rw [systemLifetime_parallel, Finset.univ_eq_empty, Finset.sup_empty]
  exact ENNReal.bot_eq_zero

/-- Source C5/C1: never-up (empty) event boundary equation. The maximum over the
empty event is zero. -/
theorem systemLifetime_empty (E : Type*) [Fintype E]
    (T : E → ENNReal) :
    systemLifetime E ∅ T = 0 := by
  let _ft : Fintype (StatMech.ConfigSpace E) := Fintype.ofFinite _
  let _dp : DecidablePred
      (fun x : StatMech.ConfigSpace E => x ∈ (∅ : Set (StatMech.ConfigSpace E))) :=
    fun x => Classical.propDecidable (x ∈ (∅ : Set (StatMech.ConfigSpace E)))
  have h : Finset.univ.filter
      (fun x : StatMech.ConfigSpace E => x ∈ (∅ : Set (StatMech.ConfigSpace E))) = ∅ :=
    Finset.filter_false_of_mem (fun x _ => Set.notMem_empty x)
  change (Finset.univ.filter
      (fun x : StatMech.ConfigSpace E => x ∈ (∅ : Set (StatMech.ConfigSpace E)))).sup
      (fun x => configLifetime E x T) = 0
  rw [h, Finset.sup_empty]
  exact ENNReal.bot_eq_zero

/-- Source C5: always-up (universal) event boundary equation. The universal event
contains the all-down configuration with lifetime `⊤`, so the maximum is `⊤`. -/
theorem systemLifetime_univ (E : Type*) [Fintype E]
    (T : E → ENNReal) :
    systemLifetime E Set.univ T = ⊤ := by
  let _ft : Fintype (StatMech.ConfigSpace E) := Fintype.ofFinite _
  let _dp : DecidablePred
      (fun x : StatMech.ConfigSpace E =>
        x ∈ (Set.univ : Set (StatMech.ConfigSpace E))) :=
    fun x => Classical.propDecidable (x ∈ (Set.univ : Set (StatMech.ConfigSpace E)))
  have hmem : (fun _ => false) ∈ Finset.univ.filter
      (fun x : StatMech.ConfigSpace E => x ∈ (Set.univ : Set (StatMech.ConfigSpace E))) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Set.mem_univ _⟩
  unfold systemLifetime
  apply le_antisymm le_top
  calc (⊤ : ENNReal) = configLifetime E (fun _ => false) T := (configLifetime_allFalse E T).symm
    _ ≤ _ := Finset.le_sup (f := fun x => configLifetime E x T) hmem

end Reliability
