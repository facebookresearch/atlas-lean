/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100MaximalPointStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2ThreePointWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightXiMoves

/-! Literal original permutation words, Golay signs, and complete vector certificates for a canonical point mover. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Four literal words in the two original Mathieu generators and their inverses. -/
def leechNormSixHS100PointMoverPermutationWords : Fin 4 → List (Fin 4) :=
  ![[2, 2, 1, 2, 2, 1],
    [2, 2, 1, 2, 2, 1, 2, 1, 0, 1, 2, 2, 1, 0, 0, 2, 1, 0, 2, 2, 1, 0, 0, 2, 1, 0, 3, 0, 0, 3, 0, 0],
    [2, 2, 1, 2, 2, 1, 2, 3, 0, 2, 2, 3, 0, 0, 2, 3, 0, 2, 2, 3, 0, 0, 3, 2, 3, 0, 2, 2, 3, 0, 0, 3, 2, 2, 3, 0, 0, 3, 2, 3, 0, 2, 2, 3, 0, 0, 2, 3, 0, 3, 2, 2, 3, 0, 0, 3, 2, 2, 3, 0, 0, 2, 3, 0, 3, 2, 2, 3, 0, 0, 2, 3, 0, 2, 2, 3, 0, 0, 2, 3, 0, 3, 2, 2, 3, 0, 0, 3, 2, 3, 0, 3, 2, 2, 3, 0, 0, 2, 3, 0, 2, 2, 3, 0, 0, 2, 3, 0, 3, 2, 2, 3, 0, 0, 3, 3, 0, 0, 3, 0, 0],
    [3, 0, 0, 3, 0, 0]]

/-- Complete physical inverse coordinate arrays of those four original words. -/
def leechNormSixHS100PointMoverPermutationInverse : Fin 4 → Fin 24 → Fin 24 :=
  ![![8, 0, 1, 6, 2, 17, 13, 20, 14, 15, 7, 9, 11, 19, 4, 16, 23, 10, 5, 21, 18, 22, 3, 12],
    ![15, 1, 2, 3, 4, 11, 19, 23, 20, 9, 6, 18, 8, 17, 7, 22, 16, 21, 5, 10, 12, 13, 0, 14],
    ![19, 1, 2, 10, 4, 17, 8, 5, 23, 9, 18, 21, 16, 12, 14, 11, 13, 7, 3, 20, 0, 15, 22, 6],
    ![1, 2, 4, 22, 14, 18, 3, 10, 0, 11, 17, 12, 23, 6, 8, 9, 15, 5, 20, 13, 7, 19, 21, 16]]

/-- Every displayed inverse coordinate is certified by its literal original forward word. -/
theorem leechNormSixHS100PointMover_permutation_certificate : ∀ k : Fin 4, ∀ i : Fin 24,
    golayGeneratingWordArray (leechNormSixHS100PointMoverPermutationWords k)
      (leechNormSixHS100PointMoverPermutationInverse k i) = i := by
  decide +kernel

/-- The actual original Golay sign code selected by a literal encoder label. -/
def leechNormSixHS100PointMoverSign (d : Fin 4096) : golayCode :=
  ⟨golayEncoder (golayLabelCoefficients d), ⟨_, rfl⟩⟩

/-- All complete original root, companion, and positive-pair vectors through the nine literal steps. -/
def leechNormSixHS100PointMoverVectorData : Fin 10 → Fin 3 → Fin 24 → ℤ :=
  ![![![4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 5, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, -1, -1, 1, -1, 1, -1, -1, 1, 1], ![0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 3, -1, -3, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, -1, 1, 1, -1, 1, 1, -1, 1, 1], ![4, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-2, 2, -2, -4, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0, 0, -2, 0, 0], ![-4, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-2, 2, -2, -4, 2, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0], ![0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0]],
    ![![0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 5, 1, -1, -1, -1, -1, -1, -1, 1, 1, -1, -1, -1, -1, -1, -1, -1, 1, 1, -1, 1, -1, 1], ![-2, 2, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -2, 2]],
    ![![0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 5, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1], ![0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, -2, -2, -2, 0, -2, 0]],
    ![![0, 4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 2, 0]],
    ![![4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![2, 2, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0]]]

/-- The original integer coordinate action, retaining the numerator of every Xi step. -/
def leechNormSixHS100PointMoverStepNumerator (s : Fin 9) (v : Fin 24 → ℤ) : Fin 24 → ℤ :=
  match s.val with
  | 0 => fun i => v (leechNormSixHS100PointMoverPermutationInverse 0 i)
  | 1 => golayIntegerSign (leechNormSixHS100PointMoverSign 2816).val v
  | 2 => co1XiNumerator *ᵥ v
  | 3 => co1XiNumerator *ᵥ v
  | 4 => fun i => v (leechNormSixHS100PointMoverPermutationInverse 1 i)
  | 5 => co1XiNumerator *ᵥ v
  | 6 => fun i => v (leechNormSixHS100PointMoverPermutationInverse 2 i)
  | 7 => golayIntegerSign (leechNormSixHS100PointMoverSign 1).val v
  | _ => fun i => v (leechNormSixHS100PointMoverPermutationInverse 3 i)

/-- Xi has its original denominator two, and every original monomial step has denominator one. -/
def leechNormSixHS100PointMoverStepScale (s : Fin 9) : ℕ :=
  if s.val = 2 ∨ s.val = 3 ∨ s.val = 5 then 2 else 1

/-- Every stage follows the original whole-vector coordinate action with its exact denominator. -/
theorem leechNormSixHS100PointMover_vector_step : ∀ s : Fin 9, ∀ k : Fin 3,
    leechNormSixHS100PointMoverStepNumerator s (leechNormSixHS100PointMoverVectorData s.castSucc k) =
      leechNormSixHS100PointMoverStepScale s • leechNormSixHS100PointMoverVectorData s.succ k := by
  decide +kernel

/-- The literal original positive-octad support reached by the point mover. -/
def leechNormSixHS100PointMoverPairImage : Fin 24 → ℤ :=
  ![2, 2, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0]

/-- The three initial entries are exactly the original canonical flag vectors and positive pair. -/
theorem leechNormSixHS100PointMover_vector_initial :
    leechNormSixHS100PointMoverVectorData 0 0 = leechNormSixHS100Root.val ∧
    leechNormSixHS100PointMoverVectorData 0 1 = leechNormSixHS100Companion.val ∧
    leechNormSixHS100PointMoverVectorData 0 2 = leechNormSixHS100Pair.val := by
  decide +kernel

/-- All final original coordinates fix the flag and move the positive pair to the displayed octad. -/
theorem leechNormSixHS100PointMover_vector_final :
    leechNormSixHS100PointMoverVectorData 9 0 = leechNormSixHS100Root.val ∧
    leechNormSixHS100PointMoverVectorData 9 1 = leechNormSixHS100Companion.val ∧
    leechNormSixHS100PointMoverVectorData 9 2 = leechNormSixHS100PointMoverPairImage := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
