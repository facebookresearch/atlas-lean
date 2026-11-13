/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Mathlib
import Code.Foundations.ConfigSpace

open MeasureTheory

namespace StatMech

namespace ConfigSpace

variable {E : Type*} {G : Type*}

section Group

variable [Group G] [MulAction G E]








def shift (g : G) (ω : ConfigSpace E) : ConfigSpace E := fun e => ω (g⁻¹ • e)

@[simp] lemma shift_apply (g : G) (ω : ConfigSpace E) (e : E) :
    shift g ω e = ω (g⁻¹ • e) := rfl


@[simp] lemma shift_one : (shift (1 : G) : ConfigSpace E → ConfigSpace E) = id := by
  funext ω e
  simp [shift]


lemma shift_mul (g h : G) :
    (shift (g * h) : ConfigSpace E → ConfigSpace E) = shift g ∘ shift h := by
  funext ω e
  simp [shift, mul_smul]



theorem measurable_shift (g : G) : Measurable (shift g : ConfigSpace E → ConfigSpace E) :=
  measurable_pi_lambda _ fun e => measurable_pi_apply (g⁻¹ • e)


theorem continuous_shift (g : G) : Continuous (shift g : ConfigSpace E → ConfigSpace E) :=
  continuous_pi fun e => continuous_apply (g⁻¹ • e)


@[simp] lemma shift_inv_comp (g : G) :
    (shift g⁻¹ : ConfigSpace E → ConfigSpace E) ∘ shift g = id := by
  rw [← shift_mul]; simp


@[simp] lemma shift_comp_inv (g : G) :
    (shift g : ConfigSpace E → ConfigSpace E) ∘ shift g⁻¹ = id := by
  rw [← shift_mul]; simp



def IsTranslationInvariant (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ g : G, MeasureTheory.MeasurePreserving (shift g : ConfigSpace E → ConfigSpace E) μ μ



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
