/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.ReimerIteratedCompression
public import MathlibExt.Probability.CorrelationInequalities.Reimer
public import MathlibExt.Probability.CorrelationInequalities.ReimerCompression

@[expose] public section

/-!
# Families of finsets as events

`StatMech.familyEvent 𝒜` is the event that the support of a configuration lies in `𝒜`. Lower and
upper sets of finsets give decreasing and increasing events, so for them Reimer's inequality is
the BK inequality.

## Main definitions

* `StatMech.familyEvent 𝒜`: `{ω | cfgSupport ω ∈ 𝒜}`.

## Main results

* `StatMech.fmarg_eq_wprob_familyEvent`: `fmarg w 𝒜 = wprob w (familyEvent 𝒜)`.
* `StatMech.reimer_wprob_familyEvent_of_isLowerSet`,
  `StatMech.reimer_wprob_familyEvent_of_isUpperSet`: Reimer's inequality for events of lower
  (respectively upper) families.
* `StatMech.reimer_fmarg_iterDownComp_of_isLowerSet`: the same for iterated compressions of lower
  families.
-/

open Finset MeasureTheory
open scoped NNReal FinsetFamily

namespace StatMech

open ConfigSpace

variable {α : Type*} [DecidableEq α]

/-- A family of finsets is a lower set iff it is closed under erasing any single element. -/
theorem isLowerSet_iff_isDownAt_all (𝒜 : Finset (Finset α)) :
    IsLowerSet (𝒜 : Set (Finset α)) ↔ ∀ i, IsDownAtCoord i 𝒜 := by
  constructor
  · exact fun h i _ hs => erase_mem_of_isLowerSet h hs i
  · intro h
    exact isLowerSet_of_erase_closed (fun s hs i => h i s hs)

section Bridge

variable [Fintype α]

/-- The event that the support of a configuration lies in the family `𝒜`. -/
def familyEvent (𝒜 : Finset (Finset α)) : Set (ConfigSpace α) := {ω | cfgSupport ω ∈ 𝒜}

@[simp] lemma mem_familyEvent {𝒜 : Finset (Finset α)} {ω : ConfigSpace α} :
    ω ∈ familyEvent 𝒜 ↔ cfgSupport ω ∈ 𝒜 := Iff.rfl

lemma fwt_eq_pweight_supportCfg (w : α → Bool → ℝ) (S : Finset α) :
    fwt w S = pweight w (supportCfg S) := rfl

theorem fmarg_eq_wprob_familyEvent (w : α → Bool → ℝ) (𝒜 : Finset (Finset α)) :
    fmarg w 𝒜 = wprob w (familyEvent 𝒜) := by
  classical
  unfold fmarg wprob
  rw [← Equiv.sum_comp cfgEquivFinset.symm
    (fun ω => (familyEvent 𝒜).indicator (fun _ => (1 : ℝ)) ω * pweight w ω)]
  simp only [cfgEquivFinset_symm_apply]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun S => S ∈ 𝒜)]
  have h1 : (∑ S ∈ Finset.univ.filter (fun S => S ∈ 𝒜),
      (familyEvent 𝒜).indicator (fun _ => (1 : ℝ)) (supportCfg S) * pweight w (supportCfg S))
      = ∑ S ∈ 𝒜, fwt w S := by
    rw [Finset.filter_univ_mem]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    rw [Set.indicator_of_mem, one_mul, fwt_eq_pweight_supportCfg]
    simp only [mem_familyEvent, cfgSupport_supportCfg]; exact hS
  have h2 : (∑ S ∈ Finset.univ.filter (fun S => ¬ S ∈ 𝒜),
      (familyEvent 𝒜).indicator (fun _ => (1 : ℝ)) (supportCfg S) * pweight w (supportCfg S))
      = 0 := by
    refine Finset.sum_eq_zero (fun S hS => ?_)
    rw [Finset.mem_filter] at hS
    rw [Set.indicator_of_notMem, zero_mul]
    simp only [mem_familyEvent, cfgSupport_supportCfg]; exact hS.2
  rw [h1, h2, add_zero]

lemma cfgSupport_subset_of_le {ω ω' : ConfigSpace α} (h : ω' ≤ ω) :
    cfgSupport ω' ⊆ cfgSupport ω := by
  intro i hi
  rw [mem_cfgSupport] at hi ⊢
  have := h i; rw [hi] at this; exact le_antisymm (Bool.le_true _) this

end Bridge

section BaseCase

variable [Fintype α]

theorem isDecreasing_familyEvent_of_isLowerSet {𝒜 : Finset (Finset α)}
    (h : IsLowerSet (𝒜 : Set (Finset α))) : IsDecreasing (familyEvent 𝒜) :=
  fun _ _ hle hω => h (Finset.coe_subset.mpr (cfgSupport_subset_of_le hle)) hω

theorem isIncreasing_familyEvent_of_isUpperSet {𝒜 : Finset (Finset α)}
    (h : IsUpperSet (𝒜 : Set (Finset α))) : IsIncreasing (familyEvent 𝒜) :=
  fun _ _ hle hω => h (Finset.coe_subset.mpr (cfgSupport_subset_of_le hle)) hω

/-- Reimer's inequality for the events of two lower families (the BK inequality for
decreasing events). -/
theorem reimer_wprob_familyEvent_of_isLowerSet (w : α → Bool → ℝ)
    (hw0 : ∀ x b, 0 ≤ w x b) (hw1 : ∀ x, w x false + w x true = 1)
    {𝒜 ℬ : Finset (Finset α)} (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ))
      ≤ wprob w (familyEvent 𝒜) * wprob w (familyEvent ℬ) :=
  bk_wprob_decreasing w hw0 hw1
    (isDecreasing_familyEvent_of_isLowerSet h𝒜)
    (isDecreasing_familyEvent_of_isLowerSet hℬ)

theorem reimer_fmarg_of_isLowerSet (w : α → Bool → ℝ)
    (hw0 : ∀ x b, 0 ≤ w x b) (hw1 : ∀ x, w x false + w x true = 1)
    {𝒜 ℬ : Finset (Finset α)} (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ))
      ≤ fmarg w 𝒜 * fmarg w ℬ := by
  rw [fmarg_eq_wprob_familyEvent, fmarg_eq_wprob_familyEvent]
  exact reimer_wprob_familyEvent_of_isLowerSet w hw0 hw1 h𝒜 hℬ

/-- Reimer's inequality for the events of two upper families (the BK inequality). -/
theorem reimer_wprob_familyEvent_of_isUpperSet (w : α → Bool → ℝ)
    (hw0 : ∀ x b, 0 ≤ w x b) (hw1 : ∀ x, w x false + w x true = 1)
    {𝒜 ℬ : Finset (Finset α)} (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ))
      ≤ wprob w (familyEvent 𝒜) * wprob w (familyEvent ℬ) :=
  bk_wprob_general w hw0 hw1
    (isIncreasing_familyEvent_of_isUpperSet h𝒜)
    (isIncreasing_familyEvent_of_isUpperSet hℬ)

omit [DecidableEq α] in
theorem isLowerSet_powerset_univ :
    IsLowerSet ((Finset.univ.powerset : Finset (Finset α)) : Set (Finset α)) := by
  intro t s hts hs
  simp only [Finset.mem_coe, Finset.mem_powerset] at hs ⊢
  exact hts.trans hs

theorem isLowerSet_principal (S : Finset α) :
    IsLowerSet ((Finset.univ.powerset.filter (· ⊆ S)) : Set (Finset α)) := by
  intro t u hut hu
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hu ⊢
  exact ⟨Finset.subset_univ _, hut.trans hu.2⟩

end BaseCase

section Endpoint

variable [Fintype α]

theorem reimer_fmarg_iterDownComp_of_isLowerSet (w : α → Bool → ℝ)
    (hw0 : ∀ x b, 0 ≤ w x b) (hw1 : ∀ x, w x false + w x true = 1) (cs ds : List α)
    {𝒜 ℬ : Finset (Finset α)} (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    wprob w (disjointOccurrence (familyEvent (iterDownComp cs 𝒜))
              (familyEvent (iterDownComp ds ℬ)))
      ≤ fmarg w (iterDownComp cs 𝒜) * fmarg w (iterDownComp ds ℬ) := by
  rw [iterDownComp_eq_self_of_isLowerSet h𝒜 cs, iterDownComp_eq_self_of_isLowerSet hℬ ds]
  exact reimer_fmarg_of_isLowerSet w hw0 hw1 h𝒜 hℬ

end Endpoint

end StatMech
