/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.ErgodicStructure

/-!
# Tests for `MathlibExt.Dynamics.Ergodic.ErgodicStructure`

* `ergodic_iff_invariantsTrivial` and `condExp_invariants_ae_eq_mean` for the identity on the
  one-point space with the Dirac measure.
-/

@[expose] public section

open MeasureTheory Filter StatMech.ErgodicStructure

namespace MathlibExtTest.StatMech.Dynamics.Ergodic.ErgodicStructure

/-- The identity on the one-point space is ergodic for the Dirac measure. -/
lemma ergodic_id_unit : Ergodic (id : Unit → Unit) (Measure.dirac ()) :=
  ⟨MeasurePreserving.id _, ⟨fun _ _ _ => Filter.EventuallyConst.of_subsingleton_left⟩⟩

example : InvariantsTrivial (id : Unit → Unit) (Measure.dirac ()) :=
  (ergodic_iff_invariantsTrivial.mp ergodic_id_unit).2

example : (Measure.dirac ())[(fun _ : Unit => (1 : ℝ)) | MeasurableSpace.invariants id]
    =ᵐ[Measure.dirac ()] fun _ => ∫ _, (1 : ℝ) ∂(Measure.dirac ()) :=
  condExp_invariants_ae_eq_mean ergodic_id_unit (integrable_const _)

end MathlibExtTest.StatMech.Dynamics.Ergodic.ErgodicStructure
