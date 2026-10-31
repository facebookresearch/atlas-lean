/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Order.UpperLower.Basic
public import MathlibExt.Probability.CorrelationInequalities.IncreasingEvent

/-!
# Local events as signed combinations of increasing events

The indicator of any event that depends on finitely many edges is a finite linear combination of
indicators of increasing events.

## i. Overview

Increasing events are closed under intersection, so the linear span of their indicators is closed
under products. The indicator that an edge is open is increasing, and the indicator that it is
closed is one minus it, so the indicator of a cylinder (a prescribed state on finitely many edges)
is a product of such factors and lies in the span. An event depending on a finite edge set `S` is
a finite union of cylinders on `S`, which gives the result. This is the linear-algebra step behind
extending inequalities from increasing events to all local events. The headline
`indicator_signedIncreasingCombo_of_dependsOn` is proved unconditionally.

## ii. Key results

- `signedIncreasingCombo_iff` : membership in the span is a finite signed sum of increasing
  indicators.
- `cyl_indicator_signedIncreasingCombo` : cylinder indicators lie in the span.
- `indicator_signedIncreasingCombo_of_dependsOn` : the indicator of an event depending on a finite
  edge set lies in the span.

## iii. Table of contents

- A. Increasing indicators and their span
- B. Products in the span
- C. Cylinders
- D. Events depending on finitely many edges

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

open StatMech ConfigSpace
open scoped BigOperators Pointwise

set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

variable {E : Type*}

/-! ## A. Increasing indicators and their span -/

/-- The set of indicator functions of increasing events. -/
def incrIndicators (E : Type*) : Set (ConfigSpace E → ℝ) :=
  {f | ∃ A : Set (ConfigSpace E), IsIncreasing A ∧ f = A.indicator 1}

/-- The constant function `1` is the indicator of the increasing event `univ`. -/
lemma one_mem_incrIndicators : (1 : ConfigSpace E → ℝ) ∈ incrIndicators E :=
  ⟨Set.univ, isUpperSet_univ, by simp⟩

/-- The event that edge `e` is open is increasing. -/
lemma openEvent_increasing (e : E) : IsIncreasing {ω : ConfigSpace E | ω e = true} := by
  intro x y hxy hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  exact Bool.le_iff_imp.mp (hxy e) hx

/-- The indicator that edge `e` is open is an increasing indicator. -/
lemma openIndicator_mem (e : E) :
    ({ω : ConfigSpace E | ω e = true}).indicator (1 : ConfigSpace E → ℝ) ∈ incrIndicators E :=
  ⟨_, openEvent_increasing e, rfl⟩

/-- A function is a signed increasing combination if it lies in the real linear span of indicators
of increasing events. -/
def SignedIncreasingCombo (f : ConfigSpace E → ℝ) : Prop :=
  f ∈ Submodule.span ℝ (incrIndicators E)

/-- A function is a signed increasing combination iff it is a finite real combination of
indicators of increasing events. -/
lemma signedIncreasingCombo_iff (f : ConfigSpace E → ℝ) :
    SignedIncreasingCombo f ↔
      ∃ (ι : Type) (s : Finset ι) (c : ι → ℝ) (A : ι → Set (ConfigSpace E)),
        (∀ i ∈ s, IsIncreasing (A i)) ∧
          f = ∑ i ∈ s, c i • (A i).indicator (1 : ConfigSpace E → ℝ) := by
  constructor
  · intro hf
    rw [SignedIncreasingCombo, Submodule.mem_span_set'] at hf
    obtain ⟨n, c, g, hsum⟩ := hf
    classical
    refine ⟨Fin n, Finset.univ, c,
      fun i => ((g i).2).choose, fun i _ => ((g i).2).choose_spec.1, ?_⟩
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ((g i).2).choose_spec.2]
  · rintro ⟨ι, s, c, A, hA, rfl⟩
    refine Submodule.sum_mem _ fun i hi => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨A i, hA i hi, rfl⟩)

/-! ## B. Products in the span -/

/-- The span of increasing indicators is closed under pointwise products. -/
lemma span_mul_mem {f g : ConfigSpace E → ℝ}
    (hf : f ∈ Submodule.span ℝ (incrIndicators E))
    (hg : g ∈ Submodule.span ℝ (incrIndicators E)) :
    f * g ∈ Submodule.span ℝ (incrIndicators E) := by
  have hmul : incrIndicators E * incrIndicators E ⊆ incrIndicators E := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    obtain ⟨A, hA, rfl⟩ := ha
    obtain ⟨B, hB, rfl⟩ := hb
    exact ⟨A ∩ B, IsUpperSet.inter hA hB, Set.inter_indicator_one.symm⟩
  have h : f * g ∈ Submodule.span ℝ (incrIndicators E) * Submodule.span ℝ (incrIndicators E) :=
    Submodule.mul_mem_mul hf hg
  rw [Submodule.span_mul_span] at h
  exact Submodule.span_mono hmul h

/-- The span of increasing indicators is closed under finite products. -/
lemma prod_mem_span {ι : Type*} (s : Finset ι) (f : ι → ConfigSpace E → ℝ)
    (hf : ∀ i ∈ s, f i ∈ Submodule.span ℝ (incrIndicators E)) :
    (∏ i ∈ s, f i) ∈ Submodule.span ℝ (incrIndicators E) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact Submodule.subset_span one_mem_incrIndicators
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact span_mul_mem (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- The indicator that edge `e` is in state `b` lies in the span of increasing indicators. -/
lemma matcher_mem (e : E) (b : Bool) :
    (fun ω : ConfigSpace E => if ω e = b then (1 : ℝ) else 0)
      ∈ Submodule.span ℝ (incrIndicators E) := by
  cases b with
  | true =>
    have h : (fun ω : ConfigSpace E => if ω e = true then (1 : ℝ) else 0)
        = ({ω : ConfigSpace E | ω e = true}).indicator 1 := by
      ext ω; rw [Set.indicator_apply]; simp
    rw [h]; exact Submodule.subset_span (openIndicator_mem e)
  | false =>
    have h : (fun ω : ConfigSpace E => if ω e = false then (1 : ℝ) else 0)
        = (1 : ConfigSpace E → ℝ) - ({ω : ConfigSpace E | ω e = true}).indicator 1 := by
      ext ω
      simp only [Pi.sub_apply, Pi.one_apply, Set.indicator_apply, Set.mem_ofPred_eq]
      cases hb : ω e <;> simp
    rw [h]
    exact sub_mem (Submodule.subset_span one_mem_incrIndicators)
      (Submodule.subset_span (openIndicator_mem e))

/-! ## C. Cylinders -/

/-- The cylinder of configurations that agree with `ψ` on every edge of `S`. -/
def cyl (S : Finset E) (ψ : ConfigSpace E) : Set (ConfigSpace E) :=
  {ω | ∀ e ∈ S, ω e = ψ e}

/-- A cylinder indicator is the product over `S` of the single-edge state indicators. -/
lemma cyl_indicator_eq_prod (S : Finset E) (ψ : ConfigSpace E) :
    (cyl S ψ).indicator (1 : ConfigSpace E → ℝ)
      = ∏ e ∈ S, (fun ω : ConfigSpace E => if ω e = ψ e then (1 : ℝ) else 0) := by
  classical
  ext ω
  rw [Finset.prod_apply, Set.indicator_apply]
  by_cases h : ω ∈ cyl S ψ
  · rw [ite_eq_left h, Pi.one_apply]
    symm
    exact Finset.prod_eq_one fun e he => ite_eq_left (h e he)
  · rw [ite_eq_right h]
    symm
    obtain ⟨e, he, hne⟩ : ∃ e ∈ S, ω e ≠ ψ e := by
      by_contra hcon
      exact h fun e he => not_ne_iff.mp fun hne => hcon ⟨e, he, hne⟩
    exact Finset.prod_eq_zero (f := fun e => if ω e = ψ e then (1 : ℝ) else 0) he
      (ite_eq_right hne)

/-- Cylinder indicators are signed increasing combinations. -/
lemma cyl_indicator_signedIncreasingCombo (S : Finset E) (ψ : ConfigSpace E) :
    SignedIncreasingCombo ((cyl S ψ).indicator (1 : ConfigSpace E → ℝ)) := by
  rw [SignedIncreasingCombo, cyl_indicator_eq_prod]
  exact prod_mem_span S _ fun e _ => matcher_mem e (ψ e)

section Representatives

variable [DecidableEq E]

/-! ## D. Events depending on finitely many edges -/

/-- The configuration equal to `φ` on `S` and closed off `S`. -/
noncomputable def repOf (S : Finset E) (φ : ↥S → Bool) : ConfigSpace E :=
  fun e => if h : e ∈ S then φ ⟨e, h⟩ else false

/-- The representative `repOf S φ` agrees with `φ` on `S`. -/
lemma repOf_agree (S : Finset E) (φ : ↥S → Bool) {e : E} (he : e ∈ S) :
    repOf S φ e = φ ⟨e, he⟩ := by
  simp only [repOf, dite_eq_left he]

/-- The indicator of an event depending on `S` is the sum, over states `φ` on `S`, of its value at
`repOf S φ` times the indicator of the cylinder of `φ`. -/
lemma indicator_eq_sum_cyl (C : Set (ConfigSpace E)) (S : Finset E)
    (hC : DependsOn (C.indicator (1 : ConfigSpace E → ℝ)) (S : Set E)) :
    C.indicator (1 : ConfigSpace E → ℝ)
      = ∑ φ : ↥S → Bool,
          (C.indicator (1 : ConfigSpace E → ℝ) (repOf S φ)) •
            (cyl S (repOf S φ)).indicator 1 := by
  ext ω
  rw [Finset.sum_apply,
    Finset.sum_eq_single_of_mem (fun i : ↥S => ω i.1) (Finset.mem_univ _)]
  · have hmem : ω ∈ cyl S (repOf S (fun i : ↥S => ω i.1)) := by
      intro e he; rw [repOf_agree S _ he]
    rw [Pi.smul_apply, Set.indicator_of_mem hmem, Pi.one_apply, smul_eq_mul, mul_one]
    refine hC ?_
    intro e he
    rw [repOf_agree S _ he]
  · intro φ _ hne
    have hnmem : ω ∉ cyl S (repOf S φ) := by
      intro hmem
      apply hne
      funext i
      have hh := hmem i.1 i.2
      rw [repOf_agree S φ i.2] at hh
      rw [hh]
    rw [Pi.smul_apply, Set.indicator_of_notMem hnmem, smul_zero]

/-- The indicator of an event depending on a finite edge set is a finite signed combination of
indicators of increasing events. -/
theorem indicator_signedIncreasingCombo_of_dependsOn
    (C : Set (ConfigSpace E)) (S : Finset E)
    (hC : DependsOn (C.indicator (1 : ConfigSpace E → ℝ)) (S : Set E)) :
    SignedIncreasingCombo (C.indicator (1 : ConfigSpace E → ℝ)) := by
  rw [SignedIncreasingCombo, indicator_eq_sum_cyl C S hC]
  refine Submodule.sum_mem _ fun φ _ => Submodule.smul_mem _ _ ?_
  exact cyl_indicator_signedIncreasingCombo S (repOf S φ)

end Representatives

end FK

end StatMech
