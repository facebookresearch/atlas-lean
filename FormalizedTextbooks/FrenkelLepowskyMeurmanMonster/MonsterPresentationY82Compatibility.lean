/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact binary compatibility of the explicit y82 spin candidate and genuine Leech sign. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82Leech
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinBinaryAction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
-- Compare all 576 columns entries of the proved Q image with the actual lattice binary matrix.
/-- The explicit full Q conjugation formula matches the actual Leech binary action. -/
theorem monsterSourceY82_spin_binary_certificate : ∀ i j : Fin 24,
    toAdd (monsterSourceY82Image (xiSpinBinaryBasisLift j)).base i =
      monsterSourceY82Binary i j := by
  decide +kernel

/-- Every binary basis vector is acted on by the checked actual source sign. -/
theorem monsterSourceY82Spin_binary_column (j : Fin 24) :
    spinBinaryAction monsterSourceY82Spin (Pi.single j 1) = monsterSourceY82Binary.col j := by
  have h := qBinaryAction_apply (spinConjugation monsterSourceY82Spin) (xiSpinBinaryBasisLift j)
  change spinBinaryAction monsterSourceY82Spin (Pi.single j 1) =
    toAdd (spinConjugation monsterSourceY82Spin (xiSpinBinaryBasisLift j)).base at h
  rw [monsterSourceY82Spin_conjugation] at h
  rw [h]
  funext i
  exact monsterSourceY82_spin_binary_certificate i j

/-- The explicit spin and lattice operators agree on every actual vector of Lambda/2Lambda. -/
theorem monsterSourceY82Spin_binary (v : Fin 24 → ZMod 2) :
    spinBinaryAction monsterSourceY82Spin v = leechBinaryAction monsterSourceY82Isometry v := by
  have h : (spinBinaryAction monsterSourceY82Spin).toLinearMap =
      monsterSourceY82Binary.mulVecLin := by
    apply (Pi.basisFun (ZMod 2) (Fin 24)).ext
    intro j
    simpa only [Pi.basisFun_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
      Matrix.mulVec_single_one] using monsterSourceY82Spin_binary_column j
  rw [monsterSourceY82Isometry_binary]
  exact LinearMap.congr_fun h v

/-- The explicit spin candidate pairs with the genuine lattice sign before quotienting. -/
noncomputable def monsterSourceY82Fiber : localFiberSubgroup :=
  ⟨(monsterSourceY82Spin, monsterSourceY82Isometry), by
    apply LinearEquiv.ext
    exact monsterSourceY82Spin_binary⟩

/-- Its simultaneous-sign quotient is a genuine element of the actual local group H. -/
noncomputable def monsterSourceY82Local : H := QuotientGroup.mk' localDiagonalSubgroup
  monsterSourceY82Fiber

/-- This source-coordinate candidate is an actual named-group element.
Its equality with the literal extra*x82*extra inverse word remains a separate obligation. -/
noncomputable def monsterSourceY82Generated : ↥G := localIntoGenerated monsterSourceY82Local

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
