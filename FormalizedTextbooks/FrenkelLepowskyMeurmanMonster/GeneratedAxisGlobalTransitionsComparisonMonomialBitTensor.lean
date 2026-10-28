/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialPlanSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors

/-! Complete original comparison spin models evaluated by exact bounded bit parities. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Exact original endpoint coordinate rows of all eight signed source plans. -/
def generatedAxisGlobalComparisonMonomialCoordinateRows : Fin 8 → Fin 12 → ℕ :=
![
    ![1652, 172, 1403, 912, 643, 1702, 923, 252, 1096, 519, 647, 2255],
    ![2034, 390, 2035, 1021, 1935, 256, 1510, 1942, 409, 48, 1408, 3079],
    ![519, 775, 1081, 8, 1898, 652, 1915, 1789, 923, 685, 129, 2487],
    ![519, 775, 1081, 8, 1898, 652, 1915, 1789, 923, 685, 129, 2487],
    ![145, 1043, 889, 30, 225, 1056, 1073, 1088, 1366, 1008, 1120, 2971],
    ![241, 402, 1218, 1220, 1897, 1639, 727, 79, 1706, 1453, 599, 3069],
    ![3, 269, 6, 1059, 469, 1854, 1197, 1147, 312, 145, 731, 3069],
    ![652, 469, 1259, 292, 1719, 439, 1061, 48, 882, 2034, 1488, 2733]]

/-- Exact original endpoint quadratic rows, retaining every Parker sign coefficient. -/
def generatedAxisGlobalComparisonMonomialPhaseRows : Fin 8 → Fin 12 → ℕ :=
![
    ![1021, 1998, 44, 984, 1536, 1760, 1024, 1792, 512, 0, 1024, 0],
    ![801, 144, 148, 672, 1984, 480, 192, 1664, 0, 0, 1024, 0],
    ![1241, 1970, 592, 1368, 1776, 288, 640, 1664, 1280, 1536, 1024, 0],
    ![1241, 1970, 592, 1368, 1776, 288, 640, 1664, 1280, 1536, 1024, 0],
    ![854, 1120, 912, 1792, 624, 1728, 1472, 256, 0, 512, 0, 0],
    ![1656, 174, 1192, 184, 80, 736, 768, 768, 1536, 512, 0, 0],
    ![1231, 868, 376, 576, 1040, 576, 192, 1408, 512, 0, 0, 0],
    ![784, 50, 788, 952, 1632, 1952, 960, 512, 1536, 1024, 0, 0]]

/-- The bounded coordinate rows are the full original certified endpoint matrix. -/
theorem generatedAxisGlobalComparisonMonomialCoordinateRows_actual (k : Fin 8) :
    (generatedAxisGlobalComparisonMonomialModel k).coordinate =
      monsterCo1GeometryBinaryMaskMatrix (generatedAxisGlobalComparisonMonomialCoordinateRows k) := by
  have h : ∀ (k : Fin 8) (i j : Fin 12),
      (generatedAxisGlobalComparisonMonomialModel k).coordinate i j =
        monsterCo1GeometryBinaryMaskMatrix (generatedAxisGlobalComparisonMonomialCoordinateRows k) i j := by
    decide +kernel
  funext i j
  exact h k i j

/-- The bounded phase rows are the full original certified endpoint quadratic matrix. -/
theorem generatedAxisGlobalComparisonMonomialPhaseRows_actual (k : Fin 8) :
    (generatedAxisGlobalComparisonMonomialModel k).phase =
      monsterCo1GeometryBinaryMaskMatrix (generatedAxisGlobalComparisonMonomialPhaseRows k) := by
  have h : ∀ (k : Fin 8) (i j : Fin 12),
      (generatedAxisGlobalComparisonMonomialModel k).phase i j =
        monsterCo1GeometryBinaryMaskMatrix (generatedAxisGlobalComparisonMonomialPhaseRows k) i j := by
    decide +kernel
  funext i j
  exact h k i j

/-- The complete original spin pullback from twelve exact row parities. -/
def generatedAxisGlobalComparisonMonomialBitPull (k : Fin 8) (a : Fin 4096) : SpinIndex :=
  fun i => if (monsterCo1GeometryBinaryMaskDot 12
    (generatedAxisGlobalComparisonMonomialCoordinateRows k i) a.val).testBit 0 then 1 else 0

/-- The complete original quadratic phase from exact finite bit parity. -/
def generatedAxisGlobalComparisonMonomialBitPhase (k : Fin 8) (a : Fin 4096) : ZMod 2 :=
  if (monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 12 =>
    if a.val.testBit i.val then monsterCo1GeometryBinaryMaskDot 12
      (generatedAxisGlobalComparisonMonomialPhaseRows k i) a.val else 0))).testBit 0 then 1 else 0

/-- Exact row parities give the entire actual original endpoint spin pullback. -/
theorem generatedAxisGlobalComparisonMonomialBitPull_actual (k : Fin 8) (a : Fin 4096) :
    generatedAxisGlobalComparisonMonomialBitPull k a =
      (generatedAxisGlobalComparisonMonomialModel k).coordinate *ᵥ golayLabelCoefficients a := by
  rw [generatedAxisGlobalComparisonMonomialCoordinateRows_actual]
  change _ = monsterCo1GeometryBinaryMaskMatrix _ *ᵥ monsterCo1GeometryBinaryMaskDecode a.val
  exact (monsterCo1GeometryBinaryMaskMatrix_mulVec _ _).symm

/-- Exact bit parities give every original endpoint Parker phase at all 4096 physical spin labels. -/
theorem generatedAxisGlobalComparisonMonomialBitPhase_actual (k : Fin 8) (a : Fin 4096) :
    generatedAxisGlobalComparisonMonomialBitPhase k a =
      monsterMonomialQuadratic (generatedAxisGlobalComparisonMonomialModel k).phase
        (golayLabelCoefficients a) := by
  rw [generatedAxisGlobalComparisonMonomialPhaseRows_actual]
  change generatedAxisGlobalComparisonMonomialBitPhase k a =
    monsterMonomialQuadratic (monsterCo1GeometryBinaryMaskMatrix
      (generatedAxisGlobalComparisonMonomialPhaseRows k)) (monsterCo1GeometryBinaryMaskDecode a.val)
  unfold generatedAxisGlobalComparisonMonomialBitPhase monsterMonomialQuadratic
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
    change monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalComparisonMonomialPhaseRows k i) j *
      monsterCo1GeometryBinaryMaskDecode a.val j = monsterCo1GeometryBinaryMaskDecode a.val j *
        monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalComparisonMonomialPhaseRows k i) j
    exact mul_comm _ _

/-- The complete original compact tensor formula with exact bounded spin bit evaluation. -/
def generatedAxisGlobalComparisonMonomialBitTensor (k : Fin 8)
    (T : GeneratedAxisGlobalRationalTensor) (a : Fin 4096) (i : Fin 24) : ℚ :=
  (generatedAxisGlobalIntSign (generatedAxisGlobalComparisonMonomialBitPhase k a) : ℚ) *
    T (generatedAxisGlobalSpinLabel (generatedAxisGlobalComparisonMonomialBitPull k a))
      ((((generatedAxisGlobalComparisonMonomialWord k).map
        generatedFourthMonomialPermutationLetter).prod).val.symm i)

/-- The bounded bit tensor is the entire previously certified original tensor formula. -/
theorem generatedAxisGlobalComparisonMonomialBitTensor_eq (k : Fin 8)
    (T : GeneratedAxisGlobalRationalTensor) :
    generatedAxisGlobalComparisonMonomialBitTensor k T = generatedAxisGlobalComparisonMonomialTensor k T := by
  funext a i
  simp only [generatedAxisGlobalComparisonMonomialBitTensor, generatedAxisGlobalComparisonMonomialTensor,
    generatedAxisGlobalComparisonMonomialBitPhase_actual, generatedAxisGlobalComparisonMonomialBitPull_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
