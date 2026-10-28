/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors

/-! The root-two spin models evaluated by bounded bit parities. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Endpoint coordinate rows of the five root-two words. -/
def generatedFeasibleAmbientTenthMonomialCoordinateRows : Fin 5 → Fin 12 → ℕ :=
  ![![685, 1035, 727, 62, 2032, 1360, 256, 512, 1152, 1216, 1024, 2127], ![1147, 1239, 1615,
      1197, 1342, 1077, 1360, 323, 64, 1217, 846, 3840], ![1654, 2032, 1075, 1360, 1948, 8,
      1509, 491, 1127, 1000, 488, 3328], ![1207, 267, 1310, 1965, 332, 480, 1999, 128, 1039,
      1536, 640, 2191], ![225, 852, 610, 536, 32, 1854, 1466, 972, 1280, 768, 1806, 3086]]

/-- Endpoint quadratic phase rows of the five root-two words. -/
def generatedFeasibleAmbientTenthMonomialPhaseRows : Fin 5 → Fin 12 → ℕ :=
  ![![1072, 1698, 4, 1752, 496, 928, 448, 896, 1280, 1536, 1024, 0], ![1746, 1136, 0, 176,
      1120, 224, 320, 1152, 256, 1024, 0, 0], ![922, 1944, 2044, 16, 16, 1920, 1088, 768, 768,
      512, 0, 0], ![877, 1886, 816, 0, 816, 1984, 1216, 1280, 1536, 1536, 0, 0], ![801, 1954,
      1428, 728, 512, 512, 1792, 128, 1280, 1024, 1024, 0]]

/-- The bounded coordinate rows are the certified endpoint matrix. -/
theorem generatedFeasibleAmbientTenthMonomialCoordinateRows_actual (k : Fin 5) :
    (generatedFeasibleAmbientTenthMonomialModel k).coordinate =
      monsterCo1GeometryBinaryMaskMatrix (generatedFeasibleAmbientTenthMonomialCoordinateRows k)
          := by
  have h : ∀ (k : Fin 5) (i j : Fin 12),
      (generatedFeasibleAmbientTenthMonomialModel k).coordinate i j =
        monsterCo1GeometryBinaryMaskMatrix (generatedFeasibleAmbientTenthMonomialCoordinateRows k)
            i j := by
    decide +kernel
  funext i j
  exact h k i j

/-- The bounded phase rows are the certified endpoint quadratic matrix. -/
theorem generatedFeasibleAmbientTenthMonomialPhaseRows_actual (k : Fin 5) :
    (generatedFeasibleAmbientTenthMonomialModel k).phase =
      monsterCo1GeometryBinaryMaskMatrix (generatedFeasibleAmbientTenthMonomialPhaseRows k) := by
  have h : ∀ (k : Fin 5) (i j : Fin 12),
      (generatedFeasibleAmbientTenthMonomialModel k).phase i j =
        monsterCo1GeometryBinaryMaskMatrix (generatedFeasibleAmbientTenthMonomialPhaseRows k) i j
            := by
    decide +kernel
  funext i j
  exact h k i j

/-- The spin pullback from twelve row parities. -/
def generatedFeasibleAmbientTenthMonomialBitPull (k : Fin 5) (a : Fin 4096) : SpinIndex :=
  fun i => if (monsterCo1GeometryBinaryMaskDot 12
    (generatedFeasibleAmbientTenthMonomialCoordinateRows k i) a.val).testBit 0 then 1 else 0

/-- The quadratic phase from finite bit parity. -/
def generatedFeasibleAmbientTenthMonomialBitPhase (k : Fin 5) (a : Fin 4096) : ZMod 2 :=
  if (monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 12 =>
    if a.val.testBit i.val then monsterCo1GeometryBinaryMaskDot 12
      (generatedFeasibleAmbientTenthMonomialPhaseRows k i) a.val else 0))).testBit 0 then 1 else 0

/-- Row parities give the endpoint spin pullback. -/
theorem generatedFeasibleAmbientTenthMonomialBitPull_actual (k : Fin 5) (a : Fin 4096) :
    generatedFeasibleAmbientTenthMonomialBitPull k a =
      (generatedFeasibleAmbientTenthMonomialModel k).coordinate *ᵥ golayLabelCoefficients a := by
  rw [generatedFeasibleAmbientTenthMonomialCoordinateRows_actual]
  change _ = monsterCo1GeometryBinaryMaskMatrix _ *ᵥ monsterCo1GeometryBinaryMaskDecode a.val
  exact (monsterCo1GeometryBinaryMaskMatrix_mulVec _ _).symm

/-- Bit parities give the endpoint Parker phase at every spin label. -/
theorem generatedFeasibleAmbientTenthMonomialBitPhase_actual (k : Fin 5) (a : Fin 4096) :
    generatedFeasibleAmbientTenthMonomialBitPhase k a =
      monsterMonomialQuadratic (generatedFeasibleAmbientTenthMonomialModel k).phase
          (golayLabelCoefficients a) := by
  rw [generatedFeasibleAmbientTenthMonomialPhaseRows_actual]
  change generatedFeasibleAmbientTenthMonomialBitPhase k a =
    monsterMonomialQuadratic (monsterCo1GeometryBinaryMaskMatrix
      (generatedFeasibleAmbientTenthMonomialPhaseRows k)) (monsterCo1GeometryBinaryMaskDecode a.val)
  unfold generatedFeasibleAmbientTenthMonomialBitPhase monsterMonomialQuadratic
  rw [monsterCo1GeometryBinaryMaskSum_parity, List.map_ofFn, List.sum_ofFn]
  dsimp only [Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases hi : a.val.testBit i.val
  · simp [hi, monsterCo1GeometryBinaryMaskDecode]
  · simp only [hi, ↓reduceIte, monsterCo1GeometryBinaryMaskDot_decode,
      monsterCo1GeometryBinaryMaskDecode, one_mul]
    apply Finset.sum_congr rfl
    intro j _
    change monsterCo1GeometryBinaryMaskDecode
        (generatedFeasibleAmbientTenthMonomialPhaseRows k i) j *
      monsterCo1GeometryBinaryMaskDecode a.val j = monsterCo1GeometryBinaryMaskDecode a.val j *
        monsterCo1GeometryBinaryMaskDecode (generatedFeasibleAmbientTenthMonomialPhaseRows k i) j
    exact mul_comm _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
