/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryPolarDuality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryIrreducibleData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryConnected

/-! A finite original-word path in the actual Conway point polar graph. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual point edges mean nonzero genuine polar pairing. -/
def monsterCo1GeometryPolarAdjacent (p q : MonsterCo1GeometryPoint) : Prop :=
  co1BinaryPolar p.val q.val = 1

/-- Original chronological generator letters for the concrete intermediate point. -/
def monsterCo1PolarPathLetters : Fin 8 → Fin 5 :=
  ![0, 3, 0, 4, 3, 4, 0, 0]

/-- Complete binary coordinates for every stage of the original eight-letter word. -/
def monsterCo1PolarPathMasks : Fin 9 → ℕ :=
  ![2048, 4194304, 5181440, 5183502, 7392240, 3146646, 3176342, 11539352, 11560862]

/-- Each complete recorded vector is the actual generator image of the preceding vector. -/
theorem monsterCo1PolarPath_certificate : ∀ k : Fin 8,
    omegaOrbitBinaryMatrices (monsterCo1PolarPathLetters k) *ᵥ
      co1IrreducibleBitVector (monsterCo1PolarPathMasks (Fin.castSucc k)) =
        co1IrreducibleBitVector (monsterCo1PolarPathMasks k.succ) := by
  decide +kernel

/-- The whole original point word, formed with actual Conway generators. -/
def monsterCo1PolarPathPoint : ℕ → MonsterCo1GeometryPoint
  | 0 => monsterCo1GeometryBasePoint
  | n + 1 => if h : n < 8 then
      monsterCo1FiveGenerator (monsterCo1PolarPathLetters ⟨n, h⟩) • monsterCo1PolarPathPoint n
    else monsterCo1PolarPathPoint n

/-- Every recorded coordinate vector is bound to its actual original-word point. -/
theorem monsterCo1PolarPathPoint_binary (n : ℕ) (hn : n < 9) :
    (monsterCo1PolarPathPoint n).val =
      co1IrreducibleBitVector (monsterCo1PolarPathMasks ⟨n, hn⟩) := by
  induction n with
  | zero =>
    rw [monsterCo1PolarPathPoint, monsterCo1GeometryBasePoint_binary]
    change Pi.single 11 1 = co1IrreducibleBitVector (monsterCo1PolarPathMasks 0)
    decide +kernel
  | succ n ih =>
    have h8 : n < 8 := by omega
    rw [monsterCo1PolarPathPoint, dite_eq_left h8]
    change leechBinaryAction (omegaOrbitIsometry (monsterCo1PolarPathLetters ⟨n, h8⟩))
      (monsterCo1PolarPathPoint n).val = _
    rw [omegaOrbitIsometry_binary, ih (by omega)]
    exact monsterCo1PolarPath_certificate ⟨n, h8⟩

/-- The literal intermediate point is joined by polar edges to base and its actual Xi image. -/
theorem monsterCo1PolarPath_edges :
    monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint (monsterCo1PolarPathPoint 8) ∧
      monsterCo1GeometryPolarAdjacent (monsterCo1PolarPathPoint 8)
        (monsterCo1FiveGenerator 0 • monsterCo1GeometryBasePoint) := by
  have hw := monsterCo1PolarPathPoint_binary 8 (by omega)
  constructor
  · change co1BinaryPolar monsterCo1GeometryBasePoint.val (monsterCo1PolarPathPoint 8).val = 1
    rw [hw, monsterCo1GeometryBasePoint_binary]
    decide +kernel
  · change co1BinaryPolar (monsterCo1PolarPathPoint 8).val
      (leechBinaryAction (omegaOrbitIsometry 0) monsterCo1GeometryBasePoint.val) = 1
    rw [hw, monsterCo1GeometryBasePoint_binary, omegaOrbitIsometry_binary]
    decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
