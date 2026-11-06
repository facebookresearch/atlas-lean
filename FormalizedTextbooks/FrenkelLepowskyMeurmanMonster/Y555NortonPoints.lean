/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Six actual Q-valued parameters for Norton's Y₅₅₅ generator construction.
Source: Norton, Transforming the Monster presentation (2002), reproduced in
Farooq's 2012 thesis, pp.69–82, and the pinned mmgroup bimm/p3_to_mm.py.

These are the c/e point parameters after conjugating a=P₀ to the pure swap.
This file proves their relations inside the actual G; the line parameters,
the full diagram certificate, generation and recognition remain separate.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedSubgroups
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceCodeAddition

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The source cocode labels for c₂,c₃,e₁,e₂,e₃, in that order. -/
def y555NortonPointCocodeLabel : Fin 5 → Fin 4096
  | 0 => 0xaad
  | 1 => 0xb9b
  | 2 => 0x9b7
  | 3 => 0xb67
  | 4 => 0xad7

/-- The actual binary coordinates of the six positive source parameters.
The order is c₁,c₂,c₃,e₁,e₂,e₃. The first is x₄₀₀; the others are cocodes. -/
def y555NortonPointCoordinates (i : Fin 6) : Fin 24 → ZMod 2 :=
  Fin.cases (sourceExpectedCodeCoordinates (golayLabelCoefficients 1024))
    (fun j => binaryCocodeEmbedding (golayLabelCoefficients (y555NortonPointCocodeLabel j))) i

/-- Positive lifts of the six point parameters into the actual extraspecial Q. -/
def y555NortonPointQ (i : Fin 6) : Q :=
  ⟨Multiplicative.ofAdd (y555NortonPointCoordinates i), 1⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every listed positive lift is an involution in Q. -/
theorem y555NortonPointQ_sq (i : Fin 6) : y555NortonPointQ i ^ 2 = 1 := by
  rw [pow_two]
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    funext j
    change y555NortonPointCoordinates i j + y555NortonPointCoordinates i j = 0
    exact CharTwo.add_self_eq_zero _
  · apply Multiplicative.toAdd.injective
    change 0 + 0 + qBeta (y555NortonPointCoordinates i) (y555NortonPointCoordinates i) = 0
    have h : qBeta (y555NortonPointCoordinates i) (y555NortonPointCoordinates i) = 0 := by
      fin_cases i <;> decide +kernel
    rw [h]
    rfl

/-- The six point parameters mutually commute, as required by the source
projective-plane presentation; this is proved in the actual Q. -/
theorem y555NortonPointQ_commute (i j : Fin 6) :
    y555NortonPointQ i * y555NortonPointQ j =
      y555NortonPointQ j * y555NortonPointQ i := by
  rw [q_mul_comm_iff]
  change qBeta (y555NortonPointCoordinates i) (y555NortonPointCoordinates j) =
    qBeta (y555NortonPointCoordinates j) (y555NortonPointCoordinates i)
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Concrete point parameters in the actual generated group G. -/
noncomputable def y555NortonPoint (i : Fin 6) : ↥G :=
  qIntoGenerated (y555NortonPointQ i)

@[simp] theorem y555NortonPoint_sq (i : Fin 6) : y555NortonPoint i ^ 2 = 1 := by
  rw [y555NortonPoint, ← map_pow, y555NortonPointQ_sq, map_one]

theorem y555NortonPoint_commute (i j : Fin 6) :
    y555NortonPoint i * y555NortonPoint j = y555NortonPoint j * y555NortonPoint i := by
  change qIntoGenerated (y555NortonPointQ i) * qIntoGenerated (y555NortonPointQ j) = _
  rw [← map_mul, y555NortonPointQ_commute, map_mul]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
