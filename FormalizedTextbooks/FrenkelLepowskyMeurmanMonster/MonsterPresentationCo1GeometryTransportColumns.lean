/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual transport actions follow from checked coordinate columns. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryTransportMatrices
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Checking all twenty-four actual coordinate columns certifies the full actual binary action. -/
theorem monsterCo1GeometryTransport_matrix_of_columns (g : Co1)
    (A : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (h : ∀ j : Fin 24, co1BinaryAction g (Pi.single j 1) = A *ᵥ Pi.single j 1) :
    ∀ v, co1BinaryAction g v = A *ᵥ v := by
  have he : (co1BinaryAction g).toLinearMap = A.mulVecLin := by
    apply LinearMap.pi_ext
    intro j x
    have hs : Pi.single j x = x • (Pi.single j 1 : Fin 24 → ZMod 2) := by
      ext i
      simp [Pi.single_apply]
    rw [hs, map_smul, map_smul]
    exact congrArg (fun v => x • v) (h j)
  intro v
  exact LinearMap.congr_fun he v

/-- A line-witness transport keeps its literal actual conjugation word and cached matrices. -/
theorem monsterCo1GeometryTransport_matrix_line (g h : Co1) (k : Fin 15)
    (A Ai B C : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hg : ∀ v, co1BinaryAction g v = A *ᵥ v)
    (hgi : ∀ v, co1BinaryAction g⁻¹ v = Ai *ᵥ v)
    (hh : ∀ v, co1BinaryAction h v = B *ᵥ v)
    (hc : A * monsterCo1GeometryTransportOperatorMatrix k * Ai * B = C) :
    ∀ v, co1BinaryAction (g * monsterCo1GeometryTransportOperator k * g⁻¹ * h) v =
      C *ᵥ v := by
  intro v
  simp only [map_mul, LinearEquiv.mul_apply]
  rw [hg, monsterCo1GeometryTransportOperator_binary, hgi, hh,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
