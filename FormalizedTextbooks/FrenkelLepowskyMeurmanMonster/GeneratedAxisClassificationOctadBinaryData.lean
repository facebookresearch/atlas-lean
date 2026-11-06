/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadCoordinates

/-! Exact certificates for eight original short roots in the first octad.
The integer and binary data were computed from this repository's published
basis, and all identities are checked by Lean's ordinary kernel. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual octad whose published Golay label is three. -/
noncomputable def generatedOctadBasisOctad : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨3, by decide +kernel⟩

/-- Six difference roots, one sum root, and the positive octad root. -/
noncomputable def generatedOctadBasisLabel (j : Fin 8) : GriessShortIndex :=
  if h : j.val < 6 then
    Sum.inl (0, griessPairIndex 8 ⟨9 + j.val, by omega⟩ (by
      intro he
      have hv : (8 : ℕ) = 9 + j.val := congrArg Fin.val he
      omega))
    else if j.val = 6 then Sum.inl (1, griessPairIndex 8 9 (by decide))
      else Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))

/-- Their exact integral-basis coordinates. -/
def generatedOctadBasisIntegerCoordinates : Matrix (Fin 24) (Fin 8) ℤ :=
  ![
  ![0, 0, -3, 0, -3, -3, -1, 4],
  ![0, 0, 1, 0, 1, 0, 0, -1],
  ![0, 0, 1, 0, 0, 1, 0, -1],
  ![0, 0, 1, 0, 0, 0, 0, -1],
  ![0, 0, 0, 0, 1, 1, 0, -1],
  ![0, 0, 0, 0, 1, 0, 0, -1],
  ![0, 0, 0, 0, 0, 1, 0, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 2, 1, 2, 2, 1, -1],
  ![-1, 0, 1, 0, 1, 0, 1, -1],
  ![0, -1, 1, 0, 0, 1, 0, -1],
  ![0, 0, -2, 0, 0, 0, 0, 1],
  ![0, 0, 0, -1, 1, 1, 0, -1],
  ![0, 0, 0, 0, -2, 0, 0, 1],
  ![0, 0, 0, 0, 0, -2, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0]]

/-- Their bases in the genuine hyperbolic quotient dictionary. -/
def generatedOctadBasisBinaryMatrix : Matrix (Fin 24) (Fin 8) (ZMod 2) :=
  leechHyperbolicInverse * generatedOctadBasisIntegerCoordinates.map (Int.castRingHom (ZMod 2))

/-- A finite certificate of binary independence. -/
def generatedOctadBasisLeftInverse : Matrix (Fin 8) (Fin 24) (ZMod 2) :=
  ![
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0],
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0],
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0],
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Original extraspecial commutator duals. -/
def generatedOctadBasisDual : Matrix (Fin 24) (Fin 8) (ZMod 2) :=
  ![
  ![0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 1, 0, 0, 0, 0, 0],
  ![0, 1, 1, 0, 0, 0, 0, 0],
  ![0, 1, 0, 1, 0, 1, 0, 0],
  ![1, 0, 0, 1, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, 0, 1, 0]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- The kernel checks eight 24-coordinate integer matrix identities against the catalogue.
/-- The integer data describe original catalogue vectors. -/
theorem generatedOctadBasis_integer_certificate : ∀ j : Fin 8,
    leechBasisMatrix *ᵥ generatedOctadBasisIntegerCoordinates.col j =
      griessShortIntegral (generatedOctadBasisLabel j) := by
  have hlabel : golayOctadLabel generatedOctadBasisOctad = 3 := by
    exact congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
      ⟨3, by decide +kernel⟩)
  have ho : golayEncodedMask (golayOctadLabel generatedOctadBasisOctad).val = 0xff00 := by
    rw [hlabel]
    decide +kernel
  have hm : griessOctadSignMask generatedOctadBasisOctad 0 = 0 := by
    simp [griessOctadSignMask, trialityEvenMask, trialityBitWeight8]
  intro j
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, griessShortIntegral, generatedOctadBasisLabel,
      Nat.ofNat_pos, ↓reduceDIte, add_zero, Fin.reduceFinMk, griessPairIndex_coordinates,
      Fin.reduceLT, ↓reduceIte, mul_ite, mul_one, mul_zero, Int.reduceNeg]
    decide +kernel
  · simp only [Fin.mk_one, Fin.isValue, griessShortIntegral, generatedOctadBasisLabel,
      Nat.one_lt_ofNat, ↓reduceDIte, Nat.reduceAdd, Fin.reduceFinMk,
      griessPairIndex_coordinates, Fin.reduceLT, ↓reduceIte, mul_ite, mul_one, mul_zero,
      Int.reduceNeg]
    decide +kernel
  · simp only [Fin.reduceFinMk, Fin.isValue, griessShortIntegral, generatedOctadBasisLabel,
      Nat.reduceLT, ↓reduceDIte, Nat.reduceAdd, griessPairIndex_coordinates, Fin.reduceLT,
      ↓reduceIte, mul_ite, mul_one, mul_zero, Int.reduceNeg]
    decide +kernel
  · simp only [Fin.reduceFinMk, Fin.isValue, griessShortIntegral, generatedOctadBasisLabel,
      Nat.reduceLT, ↓reduceDIte, Nat.reduceAdd, griessPairIndex_coordinates, Fin.reduceLT,
      ↓reduceIte, mul_ite, mul_one, mul_zero, Int.reduceNeg]
    decide +kernel
  · simp only [Fin.reduceFinMk, Fin.isValue, griessShortIntegral, generatedOctadBasisLabel,
      Nat.reduceLT, ↓reduceDIte, Nat.reduceAdd, griessPairIndex_coordinates, Fin.reduceLT,
      ↓reduceIte, mul_ite, mul_one, mul_zero, Int.reduceNeg]
    decide +kernel
  · simp only [Fin.reduceFinMk, Fin.isValue, griessShortIntegral, generatedOctadBasisLabel,
      Nat.lt_add_one, ↓reduceDIte, Nat.reduceAdd, griessPairIndex_coordinates, Fin.reduceLT,
      ↓reduceIte, mul_ite, mul_one, mul_zero, Int.reduceNeg]
    decide +kernel
  · simp only [Fin.reduceFinMk, Fin.isValue, griessShortIntegral, generatedOctadBasisLabel,
      lt_self_iff_false, ↓reduceDIte, ↓reduceIte, griessPairIndex_coordinates, Fin.reduceLT,
      mul_ite, mul_one, mul_zero, one_ne_zero]
    decide +kernel
  · simp only [Fin.reduceFinMk, Fin.isValue, griessShortIntegral, generatedOctadBasisLabel,
      Nat.reduceLT, ↓reduceDIte, Nat.succ_ne_self, ↓reduceIte, ho, hm, Nat.zero_testBit,
      Bool.false_eq_true]
    decide +kernel

/-- The binary matrix has a checked left inverse. -/
theorem generatedOctadBasis_left_inverse :
    generatedOctadBasisLeftInverse * generatedOctadBasisBinaryMatrix = 1 := by
  decide +kernel

/-- The duals have Kronecker commutator values on the eight roots. -/
theorem generatedOctadBasis_dual_certificate : ∀ i j : Fin 8,
    qBeta (generatedOctadBasisDual.col i) (generatedOctadBasisBinaryMatrix.col j) +
      qBeta (generatedOctadBasisBinaryMatrix.col j) (generatedOctadBasisDual.col i) =
        if i = j then 1 else 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
