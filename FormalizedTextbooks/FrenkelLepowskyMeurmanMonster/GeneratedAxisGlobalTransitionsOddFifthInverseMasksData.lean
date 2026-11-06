/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMasksData

/-! Exact inverse full-Q data for the four genuine original Fifth frames. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Original inverse binary/phase data, checked against the complete original forward action. -/
def generatedAxisGlobalOddFifthInverseMaskColumns : Fin 2 → Fin 24 → ℕ :=
  ![![14279673, 10325254, 2442127, 13976553, 14592961, 265473, 9594645, 10124871, 4400480, 9680345, 2328339, 7364608, 3453719, 3322761, 3191566, 3742478, 4001121, 3544817, 4813712, 5791350, 5206174, 1258263, 3765136, 4492756],
    ![1286920, 3784440, 6408321, 3053593, 13286260, 6767659, 13262041, 10404393, 12043384, 8334136, 10233882, 7366656, 3948006, 263056, 2381423, 3487464, 148361, 4604809, 3873680, 1611776, 1425433, 1288217, 3409920, 6278605]]

/-- Original inverse binary/phase data, checked against the complete original forward action. -/
def generatedAxisGlobalOddFifthInverseMaskPhases : Fin 2 → Fin 24 → ZMod 2 :=
  ![![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1]]

/-- Original inverse binary/phase data, checked against the complete original forward action. -/
def generatedAxisGlobalOddFifthInverseMaskRows : Fin 2 → Fin 24 → ℕ :=
  ![![6267454, 14656004, 10695104, 2798896, 10053152, 9110400, 15168128, 1205760, 4637696, 9592832, 9109504, 8388608, 720896, 9109504, 8388608, 8388608, 2621440, 2621440, 0, 2097152, 8388608, 0, 0, 0],
    ![21810, 3380408, 8422224, 55088, 15433696, 11748928, 14203904, 6228224, 15432704, 3391488, 7084032, 8388608, 3448832, 8437760, 11796480, 8847360, 8388608, 8388608, 8388608, 0, 0, 0, 0, 0]]

/-- Full original inverse central linear correction coefficients. -/
def generatedAxisGlobalOddFifthInverseMaskCoefficients : Fin 2 → ℕ :=
  ![11563267, 13734884]

/-- The full inverse generator candidate retains its actual central bit. -/
def generatedAxisGlobalOddFifthInverseMaskGenerator (k : Fin 2) (i : Fin 24) : Q :=
  qCentral (generatedAxisGlobalOddFifthInverseMaskPhases k i) *
    generatedAxisGlobalQMask (generatedAxisGlobalOddFifthInverseMaskColumns k i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
