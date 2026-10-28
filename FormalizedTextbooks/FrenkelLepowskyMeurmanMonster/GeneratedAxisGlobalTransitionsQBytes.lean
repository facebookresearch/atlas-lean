/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQMask

/-! Three checked eight-coordinate blocks give a full genuine Q normal form,
including its central correction. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The finite mask of an eight-coordinate binary vector. -/
def generatedAxisGlobalQByteMask (v : Fin 8 → ZMod 2) : Fin 256 :=
  ⟨(∑ i : Fin 8, if v i = 0 then 0 else 2 ^ i.val) % 256, Nat.mod_lt _ (by omega)⟩

/-- An original positive Q lift supported on one of the three eight-coordinate blocks. -/
def generatedAxisGlobalQByteFromFin (b : Fin 3) (t : Fin 256) : Q :=
  generatedAxisGlobalQMask (t.val * 2 ^ (8 * b.val))

/-- The actual block of eight binary coordinates of an arbitrary original Q element. -/
def generatedAxisGlobalQByteCoordinates (q : Q) (b : Fin 3) (i : Fin 8) : ZMod 2 :=
  toAdd q.base ⟨8 * b.val + i.val, by omega⟩

/-- The positive lift of the actual eight-coordinate block. -/
def generatedAxisGlobalQByte (v : Fin 8 → ZMod 2) (b : Fin 3) : Q :=
  generatedAxisGlobalQByteFromFin b (generatedAxisGlobalQByteMask v)

set_option maxHeartbeats 20000000 in
-- Check all256 possible eight-coordinate vectors in all three genuine blocks, at all24 positions.
set_option maxRecDepth 10000 in
/-- The finite block encoding is the original binary projection, with zero elsewhere. -/
theorem generatedAxisGlobalQByte_base (v : Fin 8 → ZMod 2) (b : Fin 3) (j : Fin 24) :
    toAdd (generatedAxisGlobalQByte v b).base j =
      if j.val / 8 = b.val then v ⟨j.val % 8, Nat.mod_lt _ (by omega)⟩ else 0 := by
  revert v b j
  decide +kernel

/-- The three actual positive block lifts, multiplied in their original coordinate order. -/
def generatedAxisGlobalQByteProduct (q : Q) : Q :=
  generatedAxisGlobalQByte (generatedAxisGlobalQByteCoordinates q 0) 0 *
    generatedAxisGlobalQByte (generatedAxisGlobalQByteCoordinates q 1) 1 *
    generatedAxisGlobalQByte (generatedAxisGlobalQByteCoordinates q 2) 2

/-- The ordered three-block product has every original binary coordinate. -/
theorem generatedAxisGlobalQByteProduct_binary (q : Q) :
    toAdd (generatedAxisGlobalQByteProduct q).base = toAdd q.base := by
  funext j
  change toAdd (generatedAxisGlobalQByte (generatedAxisGlobalQByteCoordinates q 0) 0).base j +
      toAdd (generatedAxisGlobalQByte (generatedAxisGlobalQByteCoordinates q 1) 1).base j +
      toAdd (generatedAxisGlobalQByte (generatedAxisGlobalQByteCoordinates q 2) 2).base j = _
  simp_rw [generatedAxisGlobalQByte_base]
  fin_cases j <;> simp [generatedAxisGlobalQByteCoordinates]

/-- The central coefficient is retained exactly, for every actual Q element. -/
theorem generatedAxisGlobalQByteProduct_normal_form (q : Q) :
    q = qCentral (toAdd q.coeff + toAdd (generatedAxisGlobalQByteProduct q).coeff) *
      generatedAxisGlobalQByteProduct q := by
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    apply toAdd.injective
    exact (generatedAxisGlobalQByteProduct_binary q).symm
  · apply toAdd.injective
    rw [qCentral_mul_coeff, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- A finite block-image evaluator with the complete original central correction. -/
def generatedAxisGlobalQByteEvaluation (images : Fin 3 → Fin 256 → Q) (q : Q) : Q :=
  qCentral (toAdd q.coeff + toAdd (generatedAxisGlobalQByteProduct q).coeff) *
    (images 0 (generatedAxisGlobalQByteMask (generatedAxisGlobalQByteCoordinates q 0)) *
      images 1 (generatedAxisGlobalQByteMask (generatedAxisGlobalQByteCoordinates q 1)) *
      images 2 (generatedAxisGlobalQByteMask (generatedAxisGlobalQByteCoordinates q 2)))

/-- Checked block images determine the original spin conjugation on every genuine Q element. -/
theorem generatedAxisGlobalQByteEvaluation_actual (s : SpinHolomorph)
    (images : Fin 3 → Fin 256 → Q)
    (hi : ∀ b t, spinConjugation s (generatedAxisGlobalQByteFromFin b t) = images b t) (q : Q) :
    spinConjugation s q = generatedAxisGlobalQByteEvaluation images q := by
  conv_lhs => rw [generatedAxisGlobalQByteProduct_normal_form q]
  rw [map_mul, spinConjugation_central]
  simp only [generatedAxisGlobalQByteProduct, generatedAxisGlobalQByte, map_mul, hi]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
