/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine Leech code sign paired with the explicit source y82 spin candidate.
The displayed integral and binary matrices are mathematical certificates computed
from the repository's actual Leech basis. No external implementation data are used. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82Spin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual encoded source codeword whose coordinate sign is used by y82. -/
def monsterSourceY82SignCode : golayCode :=
  ⟨golayEncoder monsterSourceY82Code, ⟨monsterSourceY82Code, rfl⟩⟩

/-- Its physical sign change preserves the actual integral Leech lattice. -/
def monsterSourceY82Isometry : leechIsomSubgroup := golaySignIsometry monsterSourceY82SignCode

/-- The physical integer coordinate matrix of the source code sign. -/
def monsterSourceY82Physical : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  if i = j then if golayEncoder monsterSourceY82Code i = 0 then 1 else -1 else 0

/-- Its exact integral action in the displayed Leech basis. -/
def monsterSourceY82Integral : Matrix (Fin 24) (Fin 24) ℤ :=
![![1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1,
    0, 2, 1, 1, 1, 2, 2, -2, -2, 1, -2, -4],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1],
  ![0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0,
    0, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0,
    0, -1, 0, -1, 0, -1, -1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1,
    0, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1,
    0, -1, 0, -1, 0, -1, 0, 0, 0, -1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, -1, -1, -1, 0, 0, -1, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 16000000 in
-- Exact arithmetic checks all 576 entries of the genuine integral basis change.
/-- The displayed matrix is an actual integral lattice action. -/
theorem monsterSourceY82_integral_certificate :
    monsterSourceY82Physical * leechBasisMatrix = leechBasisMatrix * monsterSourceY82Integral := by
  decide +kernel

/-- The actual coordinate embedding intertwines this physical source sign. -/
theorem monsterSourceY82_embedding (u : Fin 24 → ℤ) :
    monsterSourceY82Isometry.val (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding (monsterSourceY82Physical *ᵥ u) := by
  ext i
  simp [monsterSourceY82Isometry, golaySignIsometry, golayRealSign_apply,
    monsterSourceY82Physical, monsterSourceY82SignCode, leechCoordinateEmbedding,
    Matrix.mulVec, dotProduct, qSign, ite_mul]
  split_ifs <;> simp [neg_div]

/-- The exact source sign therefore acts by the checked integral basis matrix. -/
theorem monsterSourceY82_embedding_basis (u : Fin 24 → ℤ) :
    monsterSourceY82Isometry.val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ u)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ (monsterSourceY82Integral *ᵥ u)) := by
  rw [monsterSourceY82_embedding, Matrix.mulVec_mulVec,
    monsterSourceY82_integral_certificate, ← Matrix.mulVec_mulVec]

/-- The source sign in the exact hyperbolic binary frame used by Q. -/
def monsterSourceY82Binary : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
    0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
  ![1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 20000000 in
-- Exact binary arithmetic compares all entries with reduction of the actual lattice action.
/-- This binary certificate is grounded in the genuine integral Leech lattice. -/
theorem monsterSourceY82_binary_certificate :
    monsterSourceY82Binary = leechHyperbolicInverse *
      monsterSourceY82Integral.map (Int.castRingHom (ZMod 2)) * leechHyperbolicMatrix := by
  decide +kernel

/-- Every actual binary vector is acted on by the checked source sign matrix. -/
theorem monsterSourceY82Isometry_binary (v : Fin 24 → ZMod 2) :
    leechBinaryAction monsterSourceY82Isometry v = monsterSourceY82Binary *ᵥ v := by
  rw [leechBinaryAction_of_basis_certificate _ _ monsterSourceY82_embedding_basis,
    ← monsterSourceY82_binary_certificate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
