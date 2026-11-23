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
* The legacy `Measure.real` comparison accepts an infinite Dirac measure below zero, while the
  `ENNReal`-valued definition rejects that counterexample.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.StochasticOrder.StochasticDomination

open MeasureTheory
open _root_.StatMech

/-- The rejected real-valued formulation, retained only to exhibit its infinite-mass bug. -/
private def RealStochasticallyDominated {E : Type*}
    (μ ν : Measure (ConfigSpace E)) : Prop :=
  ∀ A : Set (ConfigSpace E), MeasurableSet A → IsIncreasing A → μ.real A ≤ ν.real A

/-- An infinite point mass on the singleton configuration space. -/
private noncomputable def infiniteDirac : Measure (ConfigSpace (Fin 0)) :=
  (⊤ : ENNReal) • Measure.dirac (⊥ : ConfigSpace (Fin 0))

/-- The rejected real-valued predicate loses the infinite mass and puts it below zero. -/
example : RealStochasticallyDominated infiniteDirac 0 := by
  intro A hAm _hA
  simp only [infiniteDirac, Measure.real, Measure.smul_apply,
    Measure.dirac_apply' _ hAm]
  by_cases h : (⊥ : ConfigSpace (Fin 0)) ∈ A <;> simp [Set.indicator, h]

/-- Actual masses reject the same infinite-Dirac-versus-zero counterexample. -/
example : ¬ StochasticallyDominated infiniteDirac 0 := by
  intro h
  have hu := h Set.univ MeasurableSet.univ (fun _ _ _ _ => Set.mem_univ _)
  simp [infiniteDirac, Measure.smul_apply] at hu

/-- `δ_⊥ ≼ δ_⊤` on every configuration space: an increasing event containing `⊥` contains `⊤`. -/
theorem dirac_bot_dominated_dirac_top (E : Type*) :
    StochasticallyDominated (Measure.dirac (⊥ : ConfigSpace E)) (Measure.dirac ⊤) := by
  intro A hA hinc
  simp only [Measure.dirac_apply' _ hA]
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
  simp at this

/-- Reflexivity and transitivity. -/
example (E : Type*) :
    StochasticallyDominated (Measure.dirac (⊥ : ConfigSpace E)) (Measure.dirac ⊤) :=
  (StochasticallyDominated.refl _).trans (dirac_bot_dominated_dirac_top E)

end MathlibExtTest.StatMech.Probability.StochasticOrder.StochasticDomination
