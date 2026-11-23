/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.ConfigSpace
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Topology.Constructions

/-!
# Translation invariance and ergodicity on configuration space

A group `G` acting on the index set `E` (for example `ℤ^d` acting on the sites of the lattice by
translation) acts on configurations by `shift g ω = ω ∘ (g⁻¹ • ·)`. A measure on `ConfigSpace E`
is translation invariant if every shift preserves it, and ergodic if moreover every measurable
set fixed by all shifts has measure `0` or full measure.

## Main definitions

* `StatMech.ConfigSpace.shift g`: the shift of configurations by `g : G`.
* `StatMech.ConfigSpace.IsTranslationInvariant μ`: every shift preserves `μ`.
* `StatMech.ConfigSpace.IsErgodic μ`: `μ` is translation invariant and shift-invariant measurable
  sets are trivial.

## Main results

* `StatMech.ConfigSpace.shift_mul`, `StatMech.ConfigSpace.shift_one`: `shift` is a left action.
* `StatMech.ConfigSpace.measurable_shift`, `StatMech.ConfigSpace.continuous_shift`.

`shift` is the action `arrowAction` of Mathlib, and `IsErgodic` is a strict-invariance variant of
Mathlib's `ErgodicSMul`, which asks for triviality of the a.e.-invariant sets.
-/

@[expose] public section

open MeasureTheory

namespace StatMech

namespace ConfigSpace

variable {E : Type*} {G : Type*}

section Group

variable [Group G] [MulAction G E]

/-- The shift of a configuration by `g : G`: `(shift g ω) e = ω (g⁻¹ • e)`. This is the action
`arrowAction` of Mathlib on functions out of `E`. -/
def shift (g : G) (ω : ConfigSpace E) : ConfigSpace E := fun e => ω (g⁻¹ • e)

@[simp] lemma shift_apply (g : G) (ω : ConfigSpace E) (e : E) :
    shift g ω e = ω (g⁻¹ • e) := rfl

/-- `shift` is Mathlib's `arrowAction` of `G` on functions `E → Bool`. -/
lemma shift_eq_arrowAction_smul (g : G) (ω : ConfigSpace E) :
    letI := arrowAction (G := G) (A := E) (B := Bool)
    shift g ω = g • ω := rfl

@[simp] lemma shift_one : (shift (1 : G) : ConfigSpace E → ConfigSpace E) = id := by
  funext ω e
  simp [shift]

lemma shift_mul (g h : G) :
    (shift (g * h) : ConfigSpace E → ConfigSpace E) = shift g ∘ shift h := by
  funext ω e
  simp [shift, mul_smul]

theorem measurable_shift (g : G) : Measurable (shift g : ConfigSpace E → ConfigSpace E) :=
  measurable_pi_iff.mpr fun e => measurable_pi_apply (g⁻¹ • e)

theorem continuous_shift (g : G) : Continuous (shift g : ConfigSpace E → ConfigSpace E) :=
  continuous_pi fun e => continuous_apply (g⁻¹ • e)

@[simp] lemma shift_inv_comp (g : G) :
    (shift g⁻¹ : ConfigSpace E → ConfigSpace E) ∘ shift g = id := by
  rw [← shift_mul]; simp

@[simp] lemma shift_comp_inv (g : G) :
    (shift g : ConfigSpace E → ConfigSpace E) ∘ shift g⁻¹ = id := by
  rw [← shift_mul]; simp

/-- A measure on `ConfigSpace E` is translation invariant if every shift `shift g`, `g : G`,
preserves it. -/
def IsTranslationInvariant (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ g : G, MeasureTheory.MeasurePreserving (shift g : ConfigSpace E → ConfigSpace E) μ μ

/-- A measure on `ConfigSpace E` is ergodic for the shift action of `G` if it is translation
invariant and every measurable set with `shift g ⁻¹' s = s` for all `g` has measure `0` or
`μ univ`. See also Mathlib's `ErgodicSMul`, which asks the same for a.e.-invariant sets. -/
def IsErgodic (μ : Measure (ConfigSpace E)) : Prop :=
  IsTranslationInvariant (G := G) μ ∧
    ∀ s : Set (ConfigSpace E), MeasurableSet s →
      (∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) →
        μ s = 0 ∨ μ s = μ Set.univ

variable {μ : Measure (ConfigSpace E)}

lemma IsErgodic.isTranslationInvariant (h : IsErgodic (G := G) μ) :
    IsTranslationInvariant (G := G) μ := h.1

lemma IsTranslationInvariant.map_eq (h : IsTranslationInvariant (G := G) μ) (g : G) :
    Measure.map (shift g : ConfigSpace E → ConfigSpace E) μ = μ := (h g).map_eq

lemma IsTranslationInvariant.measure_preimage (h : IsTranslationInvariant (G := G) μ)
    (g : G) {s : Set (ConfigSpace E)} (hs : MeasurableSet s) :
    μ ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s) = μ s :=
  (h g).measure_preimage hs.nullMeasurableSet

end Group

end ConfigSpace

end StatMech
