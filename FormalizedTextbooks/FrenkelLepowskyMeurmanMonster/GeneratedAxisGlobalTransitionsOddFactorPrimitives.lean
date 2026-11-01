/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorSignFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorFactorPackets

/-! Separate complete spin and spatial certificates for every original signed source primitive. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The complete integral spin numerator, including both genuine inverse permutations. -/
def generatedAxisGlobalOddSpinPrimitive (l : Fin 10) (u : Fin 4096 → ℤ) : Fin 4096 → ℤ :=
  ![generatedAxisGlobalOddXiSpinInteger u,
    generatedAxisGlobalOddXiSpinInteger (generatedAxisGlobalOddXiSpinInteger u),
    generatedAxisGlobalOddSignSpinInteger 16 u, generatedAxisGlobalOddSignSpinInteger 16 u,
    generatedAxisGlobalOddSignSpinInteger 32 u, generatedAxisGlobalOddSignSpinInteger 32 u,
    generatedAxisGlobalOddMonomialSpinInteger [(0, false)] u,
    generatedAxisGlobalOddMonomialSpinInteger [(0, true)] u,
    generatedAxisGlobalOddMonomialSpinInteger [(1, false)] u,
    generatedAxisGlobalOddMonomialSpinInteger [(1, true)] u] l

/-- The matching complete original physical spatial numerator. -/
def generatedAxisGlobalOddSpatialPrimitive (l : Fin 10) (v : Fin 24 → ℤ) : Fin 24 → ℤ :=
  ![generatedAxisGlobalOddXiSpatialInteger v,
    generatedAxisGlobalOddXiSpatialInteger (generatedAxisGlobalOddXiSpatialInteger v),
    generatedAxisGlobalOddSignSpatialInteger 16 v, generatedAxisGlobalOddSignSpatialInteger 16 v,
    generatedAxisGlobalOddSignSpatialInteger 32 v, generatedAxisGlobalOddSignSpatialInteger 32 v,
    generatedAxisGlobalOddMonomialSpatialInteger [(0, false)] v,
    generatedAxisGlobalOddMonomialSpatialInteger [(0, true)] v,
    generatedAxisGlobalOddMonomialSpatialInteger [(1, false)] v,
    generatedAxisGlobalOddMonomialSpatialInteger [(1, true)] v] l

/-- Exact dyadic spin denominator factors for all ten signed source operations. -/
def generatedAxisGlobalOddSpinPrimitiveFactor : Fin 10 → ℕ :=
  ![8, 64, 2, 2, 2, 2, 1, 1, 1, 1]

/-- Exact dyadic spatial denominator factors for the same original operations. -/
def generatedAxisGlobalOddSpatialPrimitiveFactor : Fin 10 → ℕ :=
  ![2, 4, 1, 1, 1, 1, 1, 1, 1, 1]

/-- Every complete source tensor numerator is the product of its genuine two factors. -/
theorem generatedAxisGlobalOddIntegerLetter_factor (l : Fin 10)
    (u : Fin 4096 → ℤ) (v : Fin 24 → ℤ) :
    generatedAxisGlobalOddIntegerLetter l (generatedAxisGlobalOddTensorFactor u v) =
      generatedAxisGlobalOddTensorFactor (generatedAxisGlobalOddSpinPrimitive l u)
        (generatedAxisGlobalOddSpatialPrimitive l v) := by
  fin_cases l
  · exact generatedAxisGlobalOddXiInteger_factor u v
  · change generatedAxisGlobalXiIntegerAction
      (generatedAxisGlobalXiIntegerAction (generatedAxisGlobalOddTensorFactor u v)) = _
    rw [generatedAxisGlobalOddXiInteger_factor, generatedAxisGlobalOddXiInteger_factor]
    rfl
  · exact generatedAxisGlobalOddSignInteger_factor 16 u v
  · exact generatedAxisGlobalOddSignInteger_factor 16 u v
  · exact generatedAxisGlobalOddSignInteger_factor 32 u v
  · exact generatedAxisGlobalOddSignInteger_factor 32 u v
  · exact generatedAxisGlobalOddMonomialInteger_factor [(0, false)] u v
  · exact generatedAxisGlobalOddMonomialInteger_factor [(0, true)] u v
  · exact generatedAxisGlobalOddMonomialInteger_factor [(1, false)] u v
  · exact generatedAxisGlobalOddMonomialInteger_factor [(1, true)] u v

/-- Separate complete coordinate certificates imply the entire actual source tensor transport. -/
theorem generatedAxisGlobalOddFactorPrimitive_transport (l : Fin 10)
    (u U : Fin 4096 → ℤ) (v V : Fin 24 → ℤ) (Ds Dv Es Ev : ℕ)
    (hDs : 0 < Ds) (hDv : 0 < Dv) (hEs : 0 < Es) (hEv : 0 < Ev)
    (hs : ∀ k, (Es : ℤ) * generatedAxisGlobalOddSpinPrimitive l u k =
      (generatedAxisGlobalOddSpinPrimitiveFactor l : ℤ) * (Ds : ℤ) * U k)
    (hv : ∀ i, (Ev : ℤ) * generatedAxisGlobalOddSpatialPrimitive l v i =
      (generatedAxisGlobalOddSpatialPrimitiveFactor l : ℤ) * (Dv : ℤ) * V i) :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter l)
        (generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor u v)
          (Ds * Dv)) =
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor U V)
        (Es * Ev) := by
  have hf : generatedAxisGlobalOddIntegerLetterFactor l =
      generatedAxisGlobalOddSpinPrimitiveFactor l *
        generatedAxisGlobalOddSpatialPrimitiveFactor l := by
    have h : ∀ l : Fin 10, generatedAxisGlobalOddIntegerLetterFactor l =
        generatedAxisGlobalOddSpinPrimitiveFactor l *
          generatedAxisGlobalOddSpatialPrimitiveFactor l := by decide +kernel
    exact h l
  apply generatedAxisGlobalOddIntegerLetter_transport_of_certificate _ _ _ _ _
    (Nat.mul_pos hDs hDv) (Nat.mul_pos hEs hEv)
  intro k i
  rw [generatedAxisGlobalOddIntegerLetter_factor, hf]
  simp only [generatedAxisGlobalOddTensorFactor, Nat.cast_mul]
  calc
    ((Es : ℤ) * (Ev : ℤ)) *
        (generatedAxisGlobalOddSpinPrimitive l u k *
          generatedAxisGlobalOddSpatialPrimitive l v i) =
      ((Es : ℤ) * generatedAxisGlobalOddSpinPrimitive l u k) *
        ((Ev : ℤ) * generatedAxisGlobalOddSpatialPrimitive l v i) := by ring
    _ = ((generatedAxisGlobalOddSpinPrimitiveFactor l : ℤ) * (Ds : ℤ) * U k) *
        ((generatedAxisGlobalOddSpatialPrimitiveFactor l : ℤ) * (Dv : ℤ) * V i) := by
          rw [hs, hv]
    _ = _ := by ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
