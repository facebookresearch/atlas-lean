/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.LuckyCarPrescriptions

/-! # Tests for parking functions with prescribed lucky and unlucky cars -/

open MetaMathlibExt MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

-- With two unrestricted cars, the exponent is positive.
example : (Nat.card { f : Fin 4 → Fin 4 // IsParkingFunction 4 f ∧
    (∀ i ∈ ({1} : Finset (Fin 4)), IsLuckyCar f i) ∧
    (∀ i ∈ ({2} : Finset (Fin 4)), ¬ IsLuckyCar f i) } : ℚ) = 40 := by
  rw [card_parking_lucky_on 4 {1} {2} (by decide)]
  norm_num

-- When every car is prescribed, the exponent is -1.
example : (Nat.card { f : Fin 2 → Fin 2 // IsParkingFunction 2 f ∧
    (∀ i ∈ ({0} : Finset (Fin 2)), IsLuckyCar f i) ∧
    (∀ i ∈ ({1} : Finset (Fin 2)), ¬ IsLuckyCar f i) } : ℚ) = 1 := by
  rw [card_parking_lucky_on 2 {0} {1} (by decide)]
  norm_num

-- Independently enumerate the two-car runs satisfying those prescriptions.
example : (Finset.univ.filter (fun f : Fin 2 → Fin 2 =>
    IsParkingFunction 2 f ∧ parkSpots f 0 = f 0 ∧ parkSpots f 1 ≠ f 1)).card = 1 := by decide

-- The first car cannot be unlucky.
example : (Nat.card { f : Fin 3 → Fin 3 // IsParkingFunction 3 f ∧
    (∀ i ∈ (∅ : Finset (Fin 3)), IsLuckyCar f i) ∧
    (∀ i ∈ ({0} : Finset (Fin 3)), ¬ IsLuckyCar f i) } : ℚ) = 0 := by
  rw [card_parking_lucky_on 3 ∅ {0} (Finset.disjoint_empty_left _)]
  norm_num

-- There is one empty parking function.
example : (Nat.card { f : Fin 0 → Fin 0 // IsParkingFunction 0 f ∧
    (∀ i ∈ (∅ : Finset (Fin 0)), IsLuckyCar f i) ∧
    (∀ i ∈ (∅ : Finset (Fin 0)), ¬ IsLuckyCar f i) } : ℚ) = 1 := by
  rw [card_parking_lucky_on 0 ∅ ∅ (Finset.disjoint_empty_left _)]
  norm_num
