/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceRootData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddInverseData

/-! Finite actual-source binary products connecting three genuine prototypes to odd-family roots. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Product-ordered inverse words for the literal sixth, seventh and eighth local source fibers. -/
def generatedAxisGlobalOddPrototypeInverseWords : Fin 3 → List (Fin 10) :=
  ![[7, 1, 7, 9, 7, 1, 9, 1],
    [1, 7, 9, 7, 1, 9, 1],
    [1, 7, 9, 1, 7, 9, 1]]

/-- Exact candidate binary roots of the three literal prototype fibers. -/
def generatedAxisGlobalOddPrototypeMask : Fin 3 → ℕ := ![11300198, 15215633, 2277469]

/-- Indices of the corresponding genuine odd-family norm-eight forest roots. -/
def generatedAxisGlobalOddPrototypeRootIndex : Fin 3 → Fin 9 := ![8, 7, 1]

/-- Full odd-axis stabilizer words taking the genuine roots to the prototype roots. -/
def generatedAxisGlobalOddPrototypeTransportWords : Fin 3 → List (Fin 14) :=
  ![[13, 13, 13, 12, 7, 13, 13, 12],
    [13, 13, 6, 13, 13, 12, 13, 13, 12, 13, 13, 12, 10, 13],
    [4, 13, 13, 12, 13, 12, 13, 12, 13, 13, 5]]

set_option maxHeartbeats 1000000 in
-- Check both complete original products in each genuine hyperbolic-coordinate root calculation.
/-- The source inverse words and actual full-axis transports have the same exact binary roots. -/
theorem generatedAxisGlobalOddPrototype_certificate : ∀ k : Fin 3,
    (generatedAxisGlobalOddPrototypeInverseWords k).foldr
      (fun l x => generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) x)
      2048 = generatedAxisGlobalOddPrototypeMask k ∧
    (generatedAxisGlobalOddPrototypeTransportWords k).foldr
      (fun l x => generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddBinaryRows l) x)
      (generatedAxisGlobalOddRootMask (generatedAxisGlobalOddPrototypeRootIndex k)) =
        generatedAxisGlobalOddPrototypeMask k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
