/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A corrected original-source derivation of the first rejected index equation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexCheck

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- The old source instruction at equation 148825 does not replay against its stated source. -/
theorem y322TCIndexRepairFirst_old_rejected : ¬ y322TCIndexCheckAt 148825 := by
  decide +kernel

/-- The claimed equation is exactly the reverse of original transversal definition T3. -/
theorem y322TCIndexRepairFirst_source :
    y322EquationsSameReduction (y322TCIndexProgram ⟨148825, by decide⟩).1
      (y322EquationOrient (y322TCIndexSource ⟨38616, by decide⟩) true false) := by
  unfold y322EquationsSameReduction
  decide +kernel

/-- Equation 148825 holds in the original presentation by its literal acyclic T3 definition. -/
theorem y322TCIndexRepairFirst_valid :
    (y322TCIndexProgram ⟨148825, by decide⟩).1.Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  exact y322WordEquation_transport _ _ _
    (y322EquationOrient_valid _ _ (y322TCIndexSource_valid ⟨38616, by decide⟩) true false)
    y322TCIndexRepairFirst_source.1 y322TCIndexRepairFirst_source.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
