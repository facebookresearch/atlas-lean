/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ClassicalMeteredParkingFunctions

open MetaMathlibExt

-- No cars and no spots, for any meter length.
example (t : ℕ) : IsMeteredParkingFunction t (Fin.elim0 : Fin 0 → Fin 0) :=
  IsPartialParkingFunction.isMeteredParkingFunction le_rfl (by decide) t

-- Three cars can park classically starting at spot one on a four-spot street.
example (t : ℕ) : IsMeteredParkingFunction t (![1, 1, 1] : Fin 3 → Fin 4) :=
  IsPartialParkingFunction.isMeteredParkingFunction (by decide) (by decide) t

-- The third car reuses the first spot with a short meter and takes the last spot with a long one.
example :
    meteredOutcome 1 4 [1, 1, 1] = [some 1, some 2, some 1] ∧
    meteredOutcome 2 4 [1, 1, 1] = [some 1, some 2, some 3] := by decide
