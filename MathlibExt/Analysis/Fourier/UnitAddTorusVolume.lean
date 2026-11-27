/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AutomorphicForm_bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn.lean`
and
`P2M/Sol/S_AutomorphicForm_bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Measure.Haar.Unique

import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

noncomputable section

open MeasureTheory

namespace UnitAddTorus

/-- **The volume on a unit torus is a probability measure.** For a finite index type `ι`, the
volume on `UnitAddTorus ι`, the product of the volumes on the unit additive circle, is a
probability measure. -/
instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (volume : Measure (UnitAddTorus ι)) :=
  have : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨by rw [AddCircle.measure_univ, ENNReal.ofReal_one]⟩
  inferInstance

/-- **Uniqueness of the volume on a unit torus.** For a finite index type `ι`, every probability
measure on `UnitAddTorus ι` that is invariant under left addition is the volume. -/
theorem eq_volume_of_isAddLeftInvariant {ι : Type*} [Fintype ι] (P : Measure (UnitAddTorus ι))
    [IsProbabilityMeasure P] [P.IsAddLeftInvariant] : P = volume := by
  have : P.IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_of_isCompact_nonempty_interior P Set.univ
      isCompact_univ (by rw [interior_univ]; exact Set.univ_nonempty)
      (by rw [measure_univ]; exact one_ne_zero)
      (by rw [measure_univ]; exact ENNReal.one_ne_top)
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure P volume

/-- **Invariant pushforwards to a unit torus.** Let `ι` be a finite index type, `Θ` an additive
map from an additive commutative group `A` to `UnitAddTorus ι`, and `P` a probability measure on
`A` for which `Θ` is almost everywhere measurable. If the pushforward of `P` along `Θ` is
invariant under left addition, it is the volume. -/
theorem map_eq_volume_of_isAddLeftInvariant {A : Type*} [AddCommGroup A]
    [MeasurableSpace A] {ι : Type*} [Fintype ι] {Θ : A →+ UnitAddTorus ι}
    {P : Measure A} [IsProbabilityMeasure P] (hΘm : AEMeasurable Θ P)
    (hinv : (Measure.map Θ P).IsAddLeftInvariant) :
    Measure.map Θ P = volume := by
  have : IsProbabilityMeasure (Measure.map Θ P) :=
    (Measure.isProbabilityMeasure_map_iff hΘm).mpr inferInstance
  have : (Measure.map Θ P).IsAddLeftInvariant := hinv
  exact eq_volume_of_isAddLeftInvariant _

end UnitAddTorus

end
