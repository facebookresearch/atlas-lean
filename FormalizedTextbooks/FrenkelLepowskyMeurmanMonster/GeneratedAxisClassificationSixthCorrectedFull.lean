/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialFull
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiFull

/-! The five original corrected spatial generators fix the entire actual sixth axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- All five full original fibers fix the genuine sixth axis, retaining every original phase. -/
theorem generatedSixth_corrected_generator_full_fixed (k : Fin 5) :
    rhoLocal (localFiberIntoH (generatedSixthCorrectedGenerator k)) generatedSixthAxis =
      generatedSixthAxis := by
  refine Fin.addCases (m := 4) (n := 1)
    (motive := fun j =>
      rhoLocal (localFiberIntoH (generatedSixthCorrectedGenerator j))
        generatedSixthAxis = generatedSixthAxis)
    generatedSixth_monomial_full_fixed (fun j => ?_) k
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  have hi : Fin.natAdd 4 (0 : Fin 1) = (4 : Fin 5) := by decide
  rw [hi]
  exact generatedSixth_xi_full_fixed

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
