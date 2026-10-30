/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.StochasticOrder.StochasticDomination

/-!
# Tests for `MathlibExt.Probability.StochasticOrder.StochasticDomination`

* `StatMech.StochasticallyDominated`: the Dirac mass at the empty configuration `⊥` is dominated
  by the Dirac mass at the full configuration `⊤`, on any index set; on `Fin 1` the converse
  domination fails (witnessed by the increasing event `{⊤}`), so the relation is not trivial.
* Reflexivity and transitivity are applied.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.StochasticOrder.StochasticDomination

open MeasureTheory
open _root_.StatMech

/-- `δ_⊥ ≼ δ_⊤` on every configuration space: an increasing event containing `⊥` contains `⊤`. -/
theorem dirac_bot_dominated_dirac_top (E : Type*) :
    StochasticallyDominated (Measure.dirac (⊥ : ConfigSpace E)) (Measure.dirac ⊤) := by
  intro A hA hinc
  simp only [measureReal_def, Measure.dirac_apply' _ hA]
  by_cases h : (⊥ : ConfigSpace E) ∈ A
  · have h' : (⊤ : ConfigSpace E) ∈ A := hinc bot_le h
    simp [h, h']
  · simp [h]

/-- The converse fails on `Fin 1`: the increasing event `{ω | ⊤ ≤ ω}` has mass `1` under `δ_⊤`
and `0` under `δ_⊥`. -/
example : ¬ StochasticallyDominated (Measure.dirac (⊤ : ConfigSpace (Fin 1)))
    (Measure.dirac ⊥) := by
  intro h
  have hA : MeasurableSet (Set.Ici (⊤ : ConfigSpace (Fin 1))) :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have := h _ hA (isUpperSet_Ici ⊤)
  simp [measureReal_def] at this
  norm_num at this

/-- Reflexivity and transitivity. -/
example (E : Type*) :
    StochasticallyDominated (Measure.dirac (⊥ : ConfigSpace E)) (Measure.dirac ⊤) :=
  (StochasticallyDominated.refl _).trans (dirac_bot_dominated_dirac_top E)

end MathlibExtTest.StatMech.Probability.StochasticOrder.StochasticDomination
