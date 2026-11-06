/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact matrix certificates compose actual Conway transport words without changing their values. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryFiveQuotient

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The operator alphabet consists of actual Xi, twelve actual signs, and both permutations. -/
def monsterCo1GeometryTransportOperator (k : Fin 15) : Co1 :=
  if h : k.val = 0 then monsterCo1FiveGenerator 0
  else if h : k.val < 13 then monsterCo1GeometryBasisSignClass ⟨k.val - 1, by omega⟩
  else if k.val = 13 then monsterCo1FiveGenerator 3 else monsterCo1FiveGenerator 4

/-- Literal binary matrices for the same fifteen genuine Conway classes. -/
def monsterCo1GeometryTransportOperatorMatrix (k : Fin 15) :
    Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  if h : k.val = 0 then omegaOrbitBinaryMatrices 0
  else if h : k.val < 13 then monsterCo1GeometrySignBinary ⟨k.val - 1, by omega⟩
  else if k.val = 13 then omegaOrbitBinaryMatrices 3 else omegaOrbitBinaryMatrices 4

/-- Each literal operator matrix is the actual class action, including all twelve source signs. -/
theorem monsterCo1GeometryTransportOperator_binary (k : Fin 15) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (monsterCo1GeometryTransportOperator k) v =
      monsterCo1GeometryTransportOperatorMatrix k *ᵥ v := by
  unfold monsterCo1GeometryTransportOperator monsterCo1GeometryTransportOperatorMatrix
  split_ifs
  · exact omegaOrbitIsometry_binary 0 v
  · exact monsterCo1GeometrySign_binary _ v
  · exact omegaOrbitIsometry_binary 3 v
  · exact omegaOrbitIsometry_binary 4 v

/-- A product certificate retains the literal actual Conway word. -/
theorem monsterCo1GeometryTransport_matrix_mul (g h : Co1)
    (A B C : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hg : ∀ v, co1BinaryAction g v = A *ᵥ v)
    (hh : ∀ v, co1BinaryAction h v = B *ᵥ v) (hc : A * B = C) :
    ∀ v, co1BinaryAction (g * h) v = C *ᵥ v := by
  intro v
  rw [map_mul, LinearEquiv.mul_apply, hg, hh, Matrix.mulVec_mulVec, hc]

/-- A checked right inverse matrix determines the inverse of the actual Conway action. -/
theorem monsterCo1GeometryTransport_matrix_inv (g : Co1)
    (A B : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hg : ∀ v, co1BinaryAction g v = A *ᵥ v) (hab : A * B = 1) :
    ∀ v, co1BinaryAction g⁻¹ v = B *ᵥ v := by
  intro v
  apply (co1BinaryAction g).injective
  rw [map_inv]
  change (co1BinaryAction g) ((co1BinaryAction g).symm v) =
    (co1BinaryAction g) (B *ᵥ v)
  rw [LinearEquiv.apply_symm_apply, hg, Matrix.mulVec_mulVec, hab, Matrix.one_mulVec]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
