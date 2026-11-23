/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.IncreasingEvent

@[expose] public section

/-!
# Opening and closing a coordinate; pivotal coordinates

For a configuration `ω : E → Bool` and a coordinate `e`, `setOpen e ω` and `setClosed e ω` are
`ω` with the value at `e` set to `true` and to `false`. A coordinate `e` is *pivotal* for an event
`A` at `ω` if changing the value at `e` changes whether the configuration is in `A`. Pivotality
is the quantity in Russo's formula and in the definition of influences.

## Main definitions

* `StatMech.setOpen`, `StatMech.setClosed`: `Function.update ω e true` and
  `Function.update ω e false`.
* `StatMech.IsPivotal e A ω`: `setOpen e ω ∈ A` and `setClosed e ω ∈ A` differ.

## Main results

* `StatMech.isPivotal_congr`: pivotality of `e` depends only on the values off `e`.
* `StatMech.isPivotal_iff_of_isIncreasing`: for an increasing event, `e` is pivotal iff the
  closed configuration is outside `A` and the opened configuration is inside `A`.
-/

namespace StatMech

open ConfigSpace Function

variable {E : Type*} [DecidableEq E]

/-- `setOpen e ω` is `ω` with coordinate `e` set to `true` (open). -/
def setOpen (e : E) (ω : ConfigSpace E) : ConfigSpace E := Function.update ω e true

/-- `setClosed e ω` is `ω` with coordinate `e` set to `false` (closed). -/
def setClosed (e : E) (ω : ConfigSpace E) : ConfigSpace E := Function.update ω e false

@[simp] lemma setOpen_self (e : E) (ω : ConfigSpace E) : setOpen e ω e = true :=
  Function.update_self _ _ _

@[simp] lemma setClosed_self (e : E) (ω : ConfigSpace E) : setClosed e ω e = false :=
  Function.update_self _ _ _

lemma setOpen_of_ne {e e' : E} (h : e' ≠ e) (ω : ConfigSpace E) :
    setOpen e ω e' = ω e' := Function.update_of_ne h _ _

lemma setClosed_of_ne {e e' : E} (h : e' ≠ e) (ω : ConfigSpace E) :
    setClosed e ω e' = ω e' := Function.update_of_ne h _ _

/-- Closing a coordinate gives a smaller configuration than opening it. -/
lemma setClosed_le_setOpen (e : E) (ω : ConfigSpace E) :
    setClosed e ω ≤ setOpen e ω := by
  unfold setClosed setOpen
  rw [update_le_update_iff']
  decide

/-- `setOpen e ω` depends only on the values of `ω` off `e`. -/
lemma setOpen_congr {e : E} {ω ω' : ConfigSpace E}
    (h : ∀ e', e' ≠ e → ω e' = ω' e') : setOpen e ω = setOpen e ω' := by
  funext e'
  by_cases he : e' = e
  · subst he; simp
  · rw [setOpen_of_ne he, setOpen_of_ne he, h e' he]

/-- `setClosed e ω` depends only on the values of `ω` off `e`. -/
lemma setClosed_congr {e : E} {ω ω' : ConfigSpace E}
    (h : ∀ e', e' ≠ e → ω e' = ω' e') : setClosed e ω = setClosed e ω' := by
  funext e'
  by_cases he : e' = e
  · subst he; simp
  · rw [setClosed_of_ne he, setClosed_of_ne he, h e' he]

@[simp] lemma setOpen_setClosed (e : E) (ω : ConfigSpace E) :
    setOpen e (setClosed e ω) = setOpen e ω := by
  unfold setOpen setClosed; rw [Function.update_idem]

@[simp] lemma setClosed_setOpen (e : E) (ω : ConfigSpace E) :
    setClosed e (setOpen e ω) = setClosed e ω := by
  unfold setOpen setClosed; rw [Function.update_idem]

@[simp] lemma setOpen_setOpen (e : E) (ω : ConfigSpace E) :
    setOpen e (setOpen e ω) = setOpen e ω := by
  unfold setOpen; rw [Function.update_idem]

@[simp] lemma setClosed_setClosed (e : E) (ω : ConfigSpace E) :
    setClosed e (setClosed e ω) = setClosed e ω := by
  unfold setClosed; rw [Function.update_idem]

/-- The coordinate `e` is *pivotal* for the event `A` at `ω` if exactly one of `setOpen e ω` and
`setClosed e ω` lies in `A`. The condition does not depend on `ω e`. -/
def IsPivotal (e : E) (A : Set (ConfigSpace E)) (ω : ConfigSpace E) : Prop :=
  (setOpen e ω ∈ A) ≠ (setClosed e ω ∈ A)

/-- Pivotality with the two sides swapped. -/
lemma isPivotal_comm (e : E) (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    IsPivotal e A ω ↔ (setClosed e ω ∈ A) ≠ (setOpen e ω ∈ A) :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/-- Pivotality of `e` depends only on the values of `ω` off `e`. -/
lemma isPivotal_congr {e : E} {A : Set (ConfigSpace E)} {ω ω' : ConfigSpace E}
    (h : ∀ e', e' ≠ e → ω e' = ω' e') : IsPivotal e A ω ↔ IsPivotal e A ω' := by
  unfold IsPivotal
  rw [setOpen_congr h, setClosed_congr h]

/-- Opening `e` does not change whether `e` is pivotal. -/
@[simp] lemma isPivotal_setOpen (e : E) (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    IsPivotal e A (setOpen e ω) ↔ IsPivotal e A ω := by
  unfold IsPivotal; rw [setOpen_setOpen, setClosed_setOpen]

/-- Closing `e` does not change whether `e` is pivotal. -/
@[simp] lemma isPivotal_setClosed (e : E) (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    IsPivotal e A (setClosed e ω) ↔ IsPivotal e A ω := by
  unfold IsPivotal; rw [setOpen_setClosed, setClosed_setClosed]

/-- For an increasing event `A`, the coordinate `e` is pivotal at `ω` iff `setClosed e ω ∉ A`
and `setOpen e ω ∈ A`. -/
theorem isPivotal_iff_of_isIncreasing {e : E} {A : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (ω : ConfigSpace E) :
    IsPivotal e A ω ↔ (setClosed e ω ∉ A ∧ setOpen e ω ∈ A) := by
  have hle : setClosed e ω ≤ setOpen e ω := setClosed_le_setOpen e ω
  unfold IsPivotal
  constructor
  · intro h
    by_cases hc : setClosed e ω ∈ A
    · exact absurd (h.symm) (by simp [hc, hA hle hc])
    · refine ⟨hc, ?_⟩
      by_contra ho
      exact h (by simp [hc, ho])
  · rintro ⟨hc, ho⟩
    simp [hc, ho]

end StatMech
