/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.Growth

/-!
# Counting the traces of a concept class

On a finite sample `s`, a concept class `C` realizes at most `2 ^ s.card` traces
(`traceFamily C s`), and it shatters `s` exactly when it realizes all of them. A finite class
is the special case where `C` is a finite set of hypotheses; for a list of hypotheses,
`finiteTraces_eq_traceFamily` rewrites the executable `finiteTraces` into this form.

## Main results

* `Cslib.MachineLearning.PACLearning.card_traceFamily_le_two_pow`: at most `2 ^ s.card`
  traces.
* `Cslib.MachineLearning.PACLearning.traceFamily_eq_univ_iff`: `C` realizes every trace on
  `s` iff it shatters `s`.
* `Cslib.MachineLearning.PACLearning.setShatters_iff_card_traceFamily`: `C` shatters `s` iff
  it realizes `2 ^ s.card` traces.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*}

/-- A concept class realizes at most `2 ^ s.card` traces on the finite sample `s`. -/
theorem card_traceFamily_le_two_pow (C : ConceptClass α Bool) (s : Finset α) :
    (traceFamily C s).card ≤ 2 ^ s.card := by
  calc (traceFamily C s).card ≤ Fintype.card (Finset s) := Finset.card_le_univ _
    _ = 2 ^ s.card := by rw [Fintype.card_finset, Fintype.card_coe]

/-- `C` realizes every trace on the finite sample `s` iff it shatters `s`. -/
theorem traceFamily_eq_univ_iff {C : ConceptClass α Bool} {s : Finset α} :
    traceFamily C s = Finset.univ ↔ SetShatters C ↑s := by
  classical
  rw [← Finset.shatters_univ, shatters_traceFamily_iff, Finset.coe_univ, Set.image_univ,
    Subtype.range_coe_subtype]
  rfl

/-- `C` shatters the finite sample `s` iff it realizes all `2 ^ s.card` traces. -/
theorem setShatters_iff_card_traceFamily {C : ConceptClass α Bool} {s : Finset α} :
    SetShatters C ↑s ↔ (traceFamily C s).card = 2 ^ s.card := by
  rw [← traceFamily_eq_univ_iff, ← Finset.card_eq_iff_eq_univ, Fintype.card_finset,
    Fintype.card_coe]

end Cslib.MachineLearning.PACLearning
