/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.GibbsSimplexInfinite

/-!
# Finite-upper stochastic domination on clopen events

The bridge needs only a finite upper measure. A probability measure supplies that instance;
an infinite scalar multiple of a Dirac measure shows why it cannot be omitted.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.GibbsSimplexInfinite

open MeasureTheory Set _root_.StatMech _root_.StatMech.Ising
open scoped ENNReal StatMech StatMech.Ising

-- No finiteness instance for the lower measure is required.
example {E : Type*} [Countable E] {μ ν : Measure (ConfigSpace E)}
    [IsFiniteMeasure ν] (h : μ ≼ ν) : μ ≼c ν :=
  _root_.StatMech.Ising.StochasticallyDominated.toClopen h

-- A concrete probability measure is a valid finite upper measure.
example : (Measure.dirac (fun _ : Unit => false) : Measure (ConfigSpace Unit))
    ≼c Measure.dirac (fun _ : Unit => false) := by
  apply _root_.StatMech.Ising.StochasticallyDominated.toClopen
  intro A _ _
  exact le_rfl

/-- ENNReal domination can reverse real-mass order when the upper measure is infinite. -/
theorem infinite_upper_obstruction :
    ∃ μ ν : Measure (ConfigSpace Unit),
      μ ≼ ν ∧ μ.real univ = 1 ∧ ν.real univ = 0 := by
  let μ : Measure (ConfigSpace Unit) := Measure.dirac (fun _ => false)
  let ν : Measure (ConfigSpace Unit) := (∞ : ℝ≥0∞) • μ
  refine ⟨μ, ν, ?_, ?_, ?_⟩
  · intro A _ _
    dsimp [ν]
    by_cases hz : μ A = 0
    · simp [hz]
    · rw [ENNReal.top_mul hz]
      exact le_top
  · simp [μ, Measure.real]
  · simp [ν, μ, Measure.real]

/-- The old unrestricted bridge is false, independently of the corrected theorem. -/
theorem not_toClopen_without_finite_upper :
    ¬ (∀ μ ν : Measure (ConfigSpace Unit), μ ≼ ν → μ ≼c ν) := by
  intro h
  obtain ⟨μ, ν, hdom, hμ, hν⟩ := infinite_upper_obstruction
  have hu : IsUpperSet (univ : Set (ConfigSpace Unit)) := by
    intro a b _ _
    trivial
  have hbad := h μ ν hdom univ ⟨isClosed_univ, isOpen_univ⟩ hu
  rw [hμ, hν] at hbad
  norm_num at hbad

end PhyslibExtTest.CondensedMatter.IsingModel.GibbsSimplexInfinite
