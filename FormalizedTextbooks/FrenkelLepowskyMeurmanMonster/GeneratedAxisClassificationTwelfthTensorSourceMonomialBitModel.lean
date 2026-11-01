/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceMonomialPlanSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors

/-! Complete actual original source spin models evaluated by exact bounded bit parities. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Complete actual endpoint coordinate rows for both original source words. -/
def generatedTwelfthTensorSourceMonomialCoordinateRows : Fin 2 → Fin 12 → ℕ :=
  ![![782, 1941, 1089, 1072, 458, 841, 145, 613, 1259, 1508, 1764, 3584],
    ![393, 556, 504, 234, 1000, 546, 3, 1218, 1280, 768, 379, 2683]]

/-- Complete actual endpoint quadratic phases, including every original Parker sign. -/
def generatedTwelfthTensorSourceMonomialPhaseRows : Fin 2 → Fin 12 → ℕ :=
  ![![1748, 592, 432, 696, 624, 672, 64, 896, 256, 1536, 0, 0],
    ![817, 338, 144, 696, 0, 544, 1024, 1152, 768, 512, 0, 0]]

/-- The bounded coordinate rows are the full original certified endpoint matrix. -/
theorem generatedTwelfthTensorSourceMonomialCoordinateRows_actual (k : Fin 2) :
    (generatedTwelfthTensorSourceMonomialModel k).coordinate =
      monsterCo1GeometryBinaryMaskMatrix
        (generatedTwelfthTensorSourceMonomialCoordinateRows k) := by
  have h : ∀ (k : Fin 2) (i j : Fin 12),
      (generatedTwelfthTensorSourceMonomialModel k).coordinate i j =
        monsterCo1GeometryBinaryMaskMatrix
          (generatedTwelfthTensorSourceMonomialCoordinateRows k) i j := by
    decide +kernel
  funext i j
  exact h k i j

/-- The bounded phase rows are the full original certified endpoint quadratic matrix. -/
theorem generatedTwelfthTensorSourceMonomialPhaseRows_actual (k : Fin 2) :
    (generatedTwelfthTensorSourceMonomialModel k).phase =
      monsterCo1GeometryBinaryMaskMatrix (generatedTwelfthTensorSourceMonomialPhaseRows k) := by
  have h : ∀ (k : Fin 2) (i j : Fin 12),
      (generatedTwelfthTensorSourceMonomialModel k).phase i j =
        monsterCo1GeometryBinaryMaskMatrix
          (generatedTwelfthTensorSourceMonomialPhaseRows k) i j := by
    decide +kernel
  funext i j
  exact h k i j

/-- The complete original spin pullback from twelve exact row parities. -/
def generatedTwelfthTensorSourceMonomialBitPull (k : Fin 2) (a : Fin 4096) : SpinIndex :=
  fun i => if (monsterCo1GeometryBinaryMaskDot 12
    (generatedTwelfthTensorSourceMonomialCoordinateRows k i) a.val).testBit 0 then 1 else 0

/-- The complete original quadratic phase from exact finite bit parity. -/
def generatedTwelfthTensorSourceMonomialBitPhase (k : Fin 2) (a : Fin 4096) : ZMod 2 :=
  if (monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 12 =>
    if a.val.testBit i.val then monsterCo1GeometryBinaryMaskDot 12
      (generatedTwelfthTensorSourceMonomialPhaseRows k i) a.val else 0))).testBit 0 then 1 else 0

/-- Exact row parities give the entire actual original endpoint spin pullback. -/
theorem generatedTwelfthTensorSourceMonomialBitPull_actual (k : Fin 2) (a : Fin 4096) :
    generatedTwelfthTensorSourceMonomialBitPull k a =
      (generatedTwelfthTensorSourceMonomialModel k).coordinate *ᵥ golayLabelCoefficients a := by
  rw [generatedTwelfthTensorSourceMonomialCoordinateRows_actual]
  change _ = monsterCo1GeometryBinaryMaskMatrix _ *ᵥ monsterCo1GeometryBinaryMaskDecode a.val
  exact (monsterCo1GeometryBinaryMaskMatrix_mulVec _ _).symm

/-- Exact bit parities retain every original endpoint Parker phase at all physical spin labels. -/
theorem generatedTwelfthTensorSourceMonomialBitPhase_actual (k : Fin 2) (a : Fin 4096) :
    generatedTwelfthTensorSourceMonomialBitPhase k a =
      monsterMonomialQuadratic (generatedTwelfthTensorSourceMonomialModel k).phase
        (golayLabelCoefficients a) := by
  rw [generatedTwelfthTensorSourceMonomialPhaseRows_actual]
  change generatedTwelfthTensorSourceMonomialBitPhase k a =
    monsterMonomialQuadratic (monsterCo1GeometryBinaryMaskMatrix
      (generatedTwelfthTensorSourceMonomialPhaseRows k)) (monsterCo1GeometryBinaryMaskDecode a.val)
  unfold generatedTwelfthTensorSourceMonomialBitPhase monsterMonomialQuadratic
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
        (generatedTwelfthTensorSourceMonomialPhaseRows k i) j *
      monsterCo1GeometryBinaryMaskDecode a.val j = monsterCo1GeometryBinaryMaskDecode a.val j *
        monsterCo1GeometryBinaryMaskDecode (generatedTwelfthTensorSourceMonomialPhaseRows k i) j
    exact mul_comm _ _


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
