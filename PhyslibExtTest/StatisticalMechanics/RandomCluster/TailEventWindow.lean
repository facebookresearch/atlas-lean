/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TailEventWindow

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TailEventWindow`

In `ℤ²`:
* `fkTailEdgeWindow_mono`: the windows grow with the radius;
* `fkTailEdgeWindow_escape` for the single edge `s(0, (1, 0))` and radius `3`;
* `fk_invariant_event_ae_tail` for the (translation-invariant) Dirac measure at the all-open
  configuration and the invariant event `univ`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TailEventWindow

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice MeasureTheory

-- Windows are monotone in the radius.
example : fkTailEdgeWindow 2 1 ⊆ fkTailEdgeWindow 2 3 := fkTailEdgeWindow_mono (by norm_num)

-- A finite edge set can be translated out of any window.
example := fkTailEdgeWindow_escape (d := 2) one_le_two {s(0, ![1, 0])} 3

/-- The Dirac measure at the all-open configuration of `ℤ²`. -/
noncomputable def δ : Measure (ConfigSpace (Sym2 (Site 2))) := Measure.dirac (fun _ => true)

/-- `δ` is a finite measure. -/
instance : IsFiniteMeasure δ := by unfold δ; infer_instance

/-- `δ` is translation invariant. -/
theorem δ_invariant : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site 2)) δ := by
  intro g
  have hm : Measurable (ConfigSpace.shift (E := Sym2 (Site 2)) g) :=
    measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  refine ⟨hm, ?_⟩
  rw [δ, Measure.map_dirac' hm]
  rfl

-- An invariant event is a.s. a tail event.
example := fk_invariant_event_ae_tail one_le_two δ_invariant Set.univ MeasurableSet.univ
  fun _ => Set.preimage_univ

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TailEventWindow
