/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness

/-! The actual symmetric matrix action depends only on the genuine Co1 projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Both genuine scalar lattice signs act trivially on the entire physical matrix space. -/
theorem generatedAxisGlobalMatrixAction_signs : signsSubgroup ≤ conwayMatrixAction.ker := by
  intro e he
  change conwayMatrixAction e = 1
  rcases he with he | he
  · apply conwayMatrixAction_scalar e 0
    intro x
    simp only [he, LinearEquiv.coe_one, id_eq, qSign_zero, one_smul]
  · apply conwayMatrixAction_scalar e 1
    intro x
    simp only [qSign_one, neg_one_smul]
    exact he x

/-- The full actual matrix representation descends through the genuine lattice signs. -/
def generatedAxisGlobalCo1MatrixAction : Co1 →*
    (Matrix (Fin 24) (Fin 24) ℝ ≃ₗ[ℝ] Matrix (Fin 24) (Fin 24) ℝ) :=
  QuotientGroup.lift signsSubgroup conwayMatrixAction generatedAxisGlobalMatrixAction_signs

/-- A lattice representative induces exactly the descended actual matrix action. -/
theorem generatedAxisGlobalCo1MatrixAction_mk (e : leechIsomSubgroup) :
    generatedAxisGlobalCo1MatrixAction (QuotientGroup.mk e) = conwayMatrixAction e := rfl

/-- Equal genuine Co1 projections give equal complete actual matrix operators. -/
theorem generatedAxisGlobalMatrixAction_eq_of_projection (e f : leechIsomSubgroup)
    (h : (QuotientGroup.mk e : Co1) = QuotientGroup.mk f) :
    conwayMatrixAction e = conwayMatrixAction f :=
  congrArg generatedAxisGlobalCo1MatrixAction h

/-- The physical matrix constituent of an actual local fiber uses its genuine Co1 projection. -/
theorem generatedAxisGlobalRaw_matrix_projection (f : localFiberSubgroup) (x : ConwayRawSpace) :
    (localConwayRawRepresentation f x).1 =
      generatedAxisGlobalCo1MatrixAction (projH (QuotientGroup.mk f : H)) x.1 := by
  change conwayMatrixAction f.val.2 x.1 =
    generatedAxisGlobalCo1MatrixAction (QuotientGroup.mk f.val.2) x.1
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
