/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Smith
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyWeakEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkWeakSolutionSet
import MathlibExt.AlgebraicTopology.SimplicialSpace.WeakCobaseChange
import MathlibExt.AlgebraicTopology.SimplicialSpace.WeakTransfiniteComposition

/-!
# Smith-recognition inputs for Rezk weak equivalences

The literal Reedy boundary family and the genuine all-CSS Rezk weak class
satisfy the six hypotheses of the generatorwise Beke--Smith recognition
theorem.  The boundary left class is first identified with the original
monomorphisms, using the already named Reedy model only as a proved class
dictionary.

The solution-set field is the full strict generatorwise solution set.  No
localized model, replacement, accessibility of the weak class, or caller
supplied recognition packet is assumed.
-/

set_option autoImplicit false
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MorphismProperty

namespace SimplicialSpace

/-- The left orthogonal of the literal Reedy boundary RLP is exactly the
original monomorphism class. -/
theorem ReedyGeneratingFamilies.I_rlp_llp_eq_monomorphisms :
    ReedyGeneratingFamilies.I.{u}.rlp.llp =
      monomorphisms SimplicialSpace.{u} := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  rw [ReedyGeneratingFamilies.I_rlp_eq_trivialFibrations,
    trivialFibrations_llp]
  apply MorphismProperty.ext
  intro X Y f
  exact (HomotopicalAlgebra.cofibration_iff f).symm.trans
    (ReedyModel.cofibration_iff f)

/-- The literal Reedy boundaries and genuine Rezk weak equivalences satisfy
all six concrete Smith-recognition hypotheses. -/
theorem rezkSmithRecognitionInput :
    SmithRecognitionInput.{u} (C := SimplicialSpace.{u})
      ReedyGeneratingFamilies.I.{u} rezkWeakEquivalences.{u} := by
  let W := rezkWeakEquivalences.{u}
  let _ : W.HasTwoOutOfThreeProperty := inferInstance
  let _ : W.IsStableUnderRetracts := inferInstance
  refine
    { weak_two_out_of_three := inferInstance
      weak_retracts := inferInstance
      trivial_fibrations_weak := ?_
      trivial_cofibrations_cobase := ?_
      trivial_cofibrations_transfinite := ?_
      solution_set := rezkWeakEquivalences_boundary_solution_set }
  · intro X Y p hp
    let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    have hpTF : trivialFibrations SimplicialSpace.{u} p := by
      rw [← ReedyGeneratingFamilies.I_rlp_eq_trivialFibrations]
      exact hp
    exact reedyWeak_le_rezkWeak p hpTF.2
  · rw [ReedyGeneratingFamilies.I_rlp_llp_eq_monomorphisms]
    exact monomorphisms_inf_rezkWeakEquivalences_isStableUnderCobaseChange
  · rw [ReedyGeneratingFamilies.I_rlp_llp_eq_monomorphisms]
    exact
      monomorphisms_inf_rezkWeakEquivalences_isStableUnderTransfiniteComposition

end SimplicialSpace
