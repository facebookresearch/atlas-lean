/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialBitTensorSparse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastDot24

/-! Complete original signed monomial tensor with certified physical columns and exact fast parity. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Every original physical pullback column of the eight complete source plans. -/
def generatedAxisGlobalComparisonMonomialPhysicalPull : Fin 8 → Fin 24 → Fin 24 :=
![![5, 2, 14, 16, 8, 22, 1, 0, 17, 9, 21, 19, 13, 11, 15, 23, 10, 20, 7, 4, 3, 6, 12, 18],
  ![20, 10, 23, 11, 8, 9, 22, 21, 16, 3, 2, 18, 7, 15, 13, 4, 14, 5, 6, 12, 0, 17, 19, 1],
  ![3, 8, 7, 12, 20, 19, 21, 22, 23, 17, 18, 16, 9, 2, 13, 6, 14, 10, 1, 5, 4, 11, 15, 0],
  ![3, 8, 7, 12, 20, 19, 21, 22, 23, 17, 18, 16, 9, 2, 13, 6, 14, 10, 1, 5, 4, 11, 15, 0],
  ![20, 17, 18, 22, 7, 8, 6, 9, 10, 11, 4, 5, 12, 2, 3, 13, 1, 14, 0, 15, 19, 16, 21, 23],
  ![7, 22, 10, 2, 17, 13, 6, 4, 9, 19, 14, 8, 16, 3, 12, 0, 20, 21, 15, 18, 1, 11, 5, 23],
  ![17, 7, 12, 10, 13, 3, 15, 21, 8, 20, 2, 11, 4, 5, 23, 0, 16, 9, 14, 6, 19, 22, 18, 1],
  ![10, 17, 16, 9, 2, 1, 22, 20, 14, 7, 6, 12, 21, 0, 23, 3, 5, 4, 13, 15, 19, 8, 18, 11]]

/-- Every cached physical column equals the whole original permutation word. -/
theorem generatedAxisGlobalComparisonMonomialPhysicalPull_actual (k : Fin 8) (i : Fin 24) :
    generatedAxisGlobalComparisonMonomialPhysicalPull k i =
      ((((generatedAxisGlobalComparisonMonomialWord k).map
        generatedFourthMonomialPermutationLetter).prod).val.symm i) := by
  have h : ∀ (k : Fin 8) (i : Fin 24),
      generatedAxisGlobalComparisonMonomialPhysicalPull k i =
        ((((generatedAxisGlobalComparisonMonomialWord k).map
          generatedFourthMonomialPermutationLetter).prod).val.symm i) := by
    decide +kernel
  exact h k i

/-- All twelve original coordinate row parities are retained. -/
def generatedAxisGlobalComparisonMonomialFastPull (k : Fin 8) (a : Fin 4096) : SpinIndex :=
  fun i => if (generatedNinthLowerSpinFastDotTwelve
    (generatedAxisGlobalComparisonMonomialCoordinateRows k i) a.val).testBit 0 then 1 else 0

/-- All original quadratic Parker coefficients are retained. -/
def generatedAxisGlobalComparisonMonomialFastPhase (k : Fin 8) (a : Fin 4096) : ZMod 2 :=
  if (monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 12 =>
    if a.val.testBit i.val then generatedNinthLowerSpinFastDotTwelve
      (generatedAxisGlobalComparisonMonomialPhaseRows k i) a.val else 0))).testBit 0 then 1 else 0

/-- The exact fast pullback equals every original spin coordinate. -/
theorem generatedAxisGlobalComparisonMonomialFastPull_eq (k : Fin 8) (a : Fin 4096) :
    generatedAxisGlobalComparisonMonomialFastPull k a = generatedAxisGlobalComparisonMonomialBitPull k a := by
  funext i
  change (if (generatedNinthLowerSpinFastDotTwelve
    (generatedAxisGlobalComparisonMonomialCoordinateRows k i) a.val).testBit 0 then 1 else 0) =
      (if (monsterCo1GeometryBinaryMaskDot 12
        (generatedAxisGlobalComparisonMonomialCoordinateRows k i) a.val).testBit 0 then 1 else 0)
  rw [generatedNinth_lower_spin_fast_dot_twelve]

/-- The exact fast phase equals the entire original central Parker phase. -/
theorem generatedAxisGlobalComparisonMonomialFastPhase_eq (k : Fin 8) (a : Fin 4096) :
    generatedAxisGlobalComparisonMonomialFastPhase k a = generatedAxisGlobalComparisonMonomialBitPhase k a := by
  simp only [generatedAxisGlobalComparisonMonomialFastPhase,
    generatedAxisGlobalComparisonMonomialBitPhase, generatedNinth_lower_spin_fast_dot_twelve]

/-- The entire original tensor keeps its true zero guard, all spin inputs, and every physical column. -/
def generatedAxisGlobalComparisonMonomialFastTensor (k : Fin 8)
    (T : GeneratedAxisGlobalRationalTensor) (a : Fin 4096) (i : Fin 24) : ℚ :=
  let z := T (generatedAxisGlobalSpinLabel (generatedAxisGlobalComparisonMonomialFastPull k a))
    (generatedAxisGlobalComparisonMonomialPhysicalPull k i)
  if z = 0 then 0 else
    (generatedAxisGlobalIntSign (generatedAxisGlobalComparisonMonomialFastPhase k a) : ℚ) * z

/-- Every fast tensor coordinate equals the full original signed source tensor. -/
theorem generatedAxisGlobalComparisonMonomialFastTensor_eq (k : Fin 8)
    (T : GeneratedAxisGlobalRationalTensor) :
    generatedAxisGlobalComparisonMonomialFastTensor k T =
      generatedAxisGlobalComparisonMonomialBitTensorSparse k T := by
  funext a i
  simp only [generatedAxisGlobalComparisonMonomialFastTensor,
    generatedAxisGlobalComparisonMonomialBitTensorSparse,
    generatedAxisGlobalComparisonMonomialFastPull_eq,
    generatedAxisGlobalComparisonMonomialFastPhase_eq,
    generatedAxisGlobalComparisonMonomialPhysicalPull_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
