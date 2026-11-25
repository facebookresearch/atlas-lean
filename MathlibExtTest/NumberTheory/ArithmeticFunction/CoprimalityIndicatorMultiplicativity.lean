/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.CoprimalityIndicatorMultiplicativity

open MetaMathlibExt

-- The two tuple-products are 6 and 35, so their coprime coordinates remain coprime.
example :
    let E : Finset (Fin 2 × Fin 2) := {(0, 1)}
    let m : Fin 2 → ℕ := ![2, 3]
    let n : Fin 2 → ℕ := ![5, 7]
    coprimalityIndicator E (fun i => m i * n i) =
      coprimalityIndicator E m * coprimalityIndicator E n := by
  dsimp only
  exact coprimalityIndicator_mul _ _ _ (by decide)

-- The statement includes a loop and a zero coordinate: the tuple-products are 0 and 1.
example :
    let E : Finset (Fin 1 × Fin 1) := {(0, 0)}
    let m : Fin 1 → ℕ := ![0]
    let n : Fin 1 → ℕ := ![1]
    coprimalityIndicator E (fun i => m i * n i) = 0 := by
  dsimp only
  exact (coprimalityIndicator_mul _ _ _ (by decide)).trans (by decide)
