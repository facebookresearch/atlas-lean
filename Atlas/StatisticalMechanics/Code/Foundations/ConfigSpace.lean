/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Mathlib

open MeasureTheory TopologicalSpace

namespace StatMech





abbrev ConfigSpace (E : Type*) : Type _ := E → Bool

namespace ConfigSpace

variable {E : Type*}



def eval (e : E) (ω : ConfigSpace E) : Bool := ω e

@[simp] lemma eval_apply (e : E) (ω : ConfigSpace E) : eval e ω = ω e := rfl


theorem continuous_eval (e : E) : Continuous (eval e) := continuous_apply e



theorem measurable_eval (e : E) : Measurable (eval e) := measurable_pi_apply e





theorem measurableSpace_eq_iSup_comap :
    (inferInstance : MeasurableSpace (ConfigSpace E))
      = ⨆ e, MeasurableSpace.comap (eval e) inferInstance := rfl


theorem isCompact_univ : IsCompact (Set.univ : Set (ConfigSpace E)) :=
  CompactSpace.isCompact_univ

example : CompactSpace (ConfigSpace E) := inferInstance


theorem t2Space : T2Space (ConfigSpace E) := inferInstance



theorem metrizableSpace [Countable E] : MetrizableSpace (ConfigSpace E) := inferInstance


theorem secondCountableTopology [Countable E] :
    SecondCountableTopology (ConfigSpace E) := inferInstance

end ConfigSpace

end StatMech
