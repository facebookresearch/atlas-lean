/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorInteger

/-! Exact full physical tensor semantics of every genuine odd-family root product. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Complete integer tensor numerator and its actual dyadic denominator. -/
abbrev GeneratedAxisGlobalOddIntegerTensorData := (Fin 4096 → Fin 24 → ℤ) × ℕ

/-- Exact suffix-first packet evaluation in the identical original source product order. -/
def generatedAxisGlobalOddIntegerWord :
    List (Fin 10) → GeneratedAxisGlobalOddIntegerTensorData →
      GeneratedAxisGlobalOddIntegerTensorData
  | [], u => u
  | l :: ls, u =>
      let v := generatedAxisGlobalOddIntegerWord ls u
      (generatedAxisGlobalOddIntegerLetter l v.1,
        generatedAxisGlobalOddIntegerLetterFactor l * v.2)

/-- Complete integer source evaluation agrees with the actual entire tensor action. -/
theorem generatedAxisGlobalOddIntegerWord_packet (ls : List (Fin 10))
    (u : GeneratedAxisGlobalOddIntegerTensorData) :
    localTensorRepresentation ((ls.map generatedAxisGlobalOddSourceFiberLetter).prod)
        (generatedAxisGlobalTensorIntegerPacket u.1 u.2) =
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddIntegerWord ls u).1
        (generatedAxisGlobalOddIntegerWord ls u).2 := by
  induction ls with
  | nil =>
    simp only [List.map_nil, List.prod_nil, map_one, LinearEquiv.coe_one, id_eq,
      generatedAxisGlobalOddIntegerWord]
  | cons l ls ih =>
    rw [List.map_cons, List.prod_cons, map_mul, LinearEquiv.mul_apply, ih]
    exact generatedAxisGlobalOddIntegerLetter_packet l _ _

/-- All exact tensor output coordinates after one genuine odd-family root word. -/
def generatedAxisGlobalOddIntegerRootData (k : Fin 9) : GeneratedAxisGlobalOddIntegerTensorData :=
  generatedAxisGlobalOddIntegerWord (generatedAxisGlobalOddSourceRootWords k)
    (generatedAxisGlobalOddTensorInteger, 1)

/-- Every displayed root packet is the complete actual local-fiber tensor output. -/
theorem generatedAxisGlobalOddIntegerRoot_packet (k : Fin 9) :
    localTensorRepresentation (generatedAxisGlobalOddSourceRootFiber k)
        (griessConwayEncode generatedOddAxis).2.2 =
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddIntegerRootData k).1
        (generatedAxisGlobalOddIntegerRootData k).2 := by
  rw [generatedAxisGlobalOddTensorInteger_packet]
  exact generatedAxisGlobalOddIntegerWord_packet _ (generatedAxisGlobalOddTensorInteger, 1)

/-- The exact full tensor packet is the constituent of the identical actual Griess root word. -/
theorem generatedAxisGlobalOddIntegerRoot_actual (k : Fin 9) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord k) generatedOddAxis)).2.2 =
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddIntegerRootData k).1
        (generatedAxisGlobalOddIntegerRootData k).2 := by
  rw [generatedAxisGlobalOddSourceRootFiber_encode, localConwayRawRepresentation_tensor]
  exact generatedAxisGlobalOddIntegerRoot_packet k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
