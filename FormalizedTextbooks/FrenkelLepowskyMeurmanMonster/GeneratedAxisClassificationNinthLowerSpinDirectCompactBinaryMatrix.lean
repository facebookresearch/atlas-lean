/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinCompactQConjugation

/-! The complete original binary column matrix of the corrected Q-image cache. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Every original binary column retains the exact complete corrected source Q base. -/
def generatedNinthLowerSpinDirectCompactBinaryMatrix (i : Fin 11) :
    Matrix (Fin 24) (Fin 24) (ZMod 2) := fun j k =>
  toAdd (qQuotHom (generatedNinthLowerSpinCorrection i *
    generatedNinthLowerSpinQImage i k * (generatedNinthLowerSpinCorrection i)⁻¹)) j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
