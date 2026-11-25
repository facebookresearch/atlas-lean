/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.LongMeteredParkingFunctions

open MetaMathlibExt

-- The empty street and empty preference list satisfy both conditions for every meter.
example (t : ℕ) (f : Fin 0 → Fin 0) : IsMeteredParkingFunction t f :=
  (isMeteredParkingFunction_iff_of_le (by simp) (by rfl) f).2 fun k => Fin.elim0 k

-- At the threshold the second car is displaced and all three still park.
example : IsPartialParkingFunction 3 4 ![2, 2, 0] :=
  (isMeteredParkingFunction_iff_of_le (t := 2) (by decide) (by decide) _).1 (by decide)

-- With only two spots at or beyond the common preference, shortening the meter
-- by one lets the last car reuse the first car's spot.
example : IsMeteredParkingFunction 1 (![2, 2, 2] : Fin 3 → Fin 4) ∧
    ¬ IsMeteredParkingFunction 2 (![2, 2, 2] : Fin 3 → Fin 4) := by
  refine ⟨by decide, fun h => ?_⟩
  have hpartial := (isMeteredParkingFunction_iff_of_le (by decide) (by decide) _).1 h
  exact (by decide : ¬ IsPartialParkingFunction 3 4 ![2, 2, 2]) hpartial
