/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPackedData

/-! Every nonzero source retains its full preferred-Q and signed coefficient certificate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every nonzero source is checked in the original full preferred central section. -/
def generatedNinthLowerSpinShortSupportCondition (i : Fin 11) (a : Fin 98280) : Prop :=
  generatedNinthLowerSpinShortInputInteger (generatedNinthLowerSpinShortIndex a) ≠ 0 →
    generatedNinthLowerSpinShortPackedCondition i a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
