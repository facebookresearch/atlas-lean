/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Concrete dictionary labels and short-vector coordinates for Conway's Griess algebra.
Source: Conway, Invent. Math. 79 (1985), §§6–8 and 12; Seysen,
arXiv:2002.10921v3, §§6.2 and 8.1, Table 5.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Triality
public import Mathlib.Data.Finset.Sort
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Explicit increasing enumeration of the octads. -/
def golayOctadLabel (d : Fin 759) : Fin 4096 :=
  (golayOctads.orderIsoOfFin golayOctads_card d).val

/-- The MOG coordinates occupied by a mask. -/
def golayMaskSupport (m : ℕ) : Finset (Fin 24) :=
  Finset.univ.filter (fun i => m.testBit i.val)

theorem golayMaskSupport_card (m : ℕ) : (golayMaskSupport m).card = golayMaskWeight m := by
  unfold golayMaskSupport
  rw [Finset.card_filter]
  rfl

theorem golayOctad_support_card (d : Fin 759) :
    (golayMaskSupport (golayEncodedMask (golayOctadLabel d).val)).card = 8 := by
  rw [golayMaskSupport_card]
  exact (Finset.mem_filter.mp (golayOctads.orderIsoOfFin golayOctads_card d).property).2

/-- Increasing order of the eight MOG coordinates within an octad. -/
def golayOctadCoordinate (d : Fin 759) (k : Fin 8) : Fin 24 :=
  ((golayMaskSupport (golayEncodedMask (golayOctadLabel d).val)).orderIsoOfFin
    (golayOctad_support_card d) k).val

/-- The 276 unordered pairs of coordinates, using their increasing representatives. -/
def griessCoordinatePairs : Finset (Fin 24 × Fin 24) :=
  Finset.univ.filter (fun p => p.1 < p.2)

theorem griessCoordinatePairs_card : griessCoordinatePairs.card = 276 := by
  decide +kernel

/-- Lexicographically ordered coordinate pairs. -/
def griessCoordinatePairEquiv : Fin 276 ≃ griessCoordinatePairs := by
  letI : LinearOrder (Fin 24 × Fin 24) := LinearOrder.lift'
    (finProdFinEquiv : Fin 24 × Fin 24 → Fin 576) finProdFinEquiv.injective
  exact (griessCoordinatePairs.orderIsoOfFin griessCoordinatePairs_card).toEquiv

def griessCoordinatePair (p : Fin 276) : Fin 24 × Fin 24 :=
  (griessCoordinatePairEquiv p).val

/-- Short-vector classes: two families of coordinate pairs, signed octads,
and odd vectors indexed by codewords modulo the all-one word and a coordinate. -/
abbrev GriessShortIndex := (Fin 2 × Fin 276) ⊕
  ((Fin 759 × Fin 64) ⊕ (Fin 2048 × Fin 24))

/-- The short-vector coordinate space has exactly 98280 basis labels. -/
theorem griessShortIndex_card : Fintype.card GriessShortIndex = 98280 := by
  simp [GriessShortIndex]

/-- The Parker cocycle θ(d), using the published basis values and its quadratic
extension in the first variable. Seysen §3.2, Lemma 3.3 and its sketch proof. -/
def parkerThetaMask (d : ℕ) : ℕ :=
  (List.finRange 12).foldl (fun m i => m ^^^
    (if d.testBit i.val then parkerBasisThetaMasks i else 0))
    ((List.finRange 12).foldl (fun m i =>
      (List.finRange 12).foldl (fun n j => n ^^^
        (if i < j ∧ d.testBit i.val ∧ d.testBit j.val then
          parkerBasisAssociatorMasks i j else 0)) m) 0)

/-- A subset's dual Golay coordinates, given by its intersection parities with
 the twelve code generators. -/
def golayCocodeDualMask (e : ℕ) : ℕ :=
  ∑ j : Fin 12, if golayMaskWeight (golayGeneratorMasks j &&& e) % 2 = 1 then
    2 ^ j.val else 0

/-- The even sign subset of an octad, translated from its eight local positions
back to the 24 MOG coordinates. -/
def griessOctadSignMask (d : Fin 759) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then 2 ^ (golayOctadCoordinate d k).val else 0)
      ||| m) 0

private theorem octadMaskFold_testBit (f : Fin 8 → Fin 24) (b : Fin 8 → Bool)
    (xs : List (Fin 8)) (i : Fin 24) :
    ((xs.foldr (fun k m => (if b k then 2 ^ (f k).val else 0) ||| m) 0).testBit i.val = true) ↔
      ∃ k ∈ xs, b k = true ∧ f k = i := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true, ih]
    by_cases ha : b a = true
    · simp [ha, Nat.testBit_two_pow, Fin.val_inj]
    · simp [ha]

/-- A sign mask occupies exactly the chosen local positions of the octad. -/
theorem griessOctadSignMask_testBit (d : Fin 759) (e : Fin 64) (i : Fin 24) :
    (griessOctadSignMask d e).testBit i.val = true ↔
      ∃ k : Fin 8, (trialityEvenMask e).testBit k.val = true ∧
        golayOctadCoordinate d k = i := by
  simpa [griessOctadSignMask] using octadMaskFold_testBit
    (golayOctadCoordinate d) (fun k => (trialityEvenMask e).testBit k.val) (List.finRange 8) i

/-- The eight local octad positions have distinct physical coordinates. -/
theorem golayOctadCoordinate_injective (d : Fin 759) :
    Function.Injective (golayOctadCoordinate d) := by
  intro k l h
  apply (golayMaskSupport (golayEncodedMask (golayOctadLabel d).val)).orderIsoOfFin
    (golayOctad_support_card d) |>.injective
  exact Subtype.ext h

/-- Every local octad position lies in the corresponding Golay octad. -/
theorem golayOctadCoordinate_mem (d : Fin 759) (k : Fin 8) :
    (golayEncodedMask (golayOctadLabel d).val).testBit (golayOctadCoordinate d k).val = true :=
  (Finset.mem_filter.mp ((golayMaskSupport
    (golayEncodedMask (golayOctadLabel d).val)).orderIsoOfFin
      (golayOctad_support_card d) k).property).2

/-- The source representatives have an even number of negative signs. -/
theorem trialityEvenMask_even : ∀ e : Fin 64, 2 ∣ trialityBitWeight8 (trialityEvenMask e) := by
  decide +kernel

set_option maxRecDepth 10000 in
-- The finite enumeration has 256 Boolean sign patterns.
set_option maxHeartbeats 4000000 in
-- Verify the 64 even sign patterns with the last sign fixed positive.
theorem trialityEvenMask_complete : ∀ b : Fin 8 → Bool,
    b 7 = false → 2 ∣ (∑ k, if b k then (1 : ℕ) else 0) →
      ∃ e : Fin 64, ∀ k : Fin 8, (trialityEvenMask e).testBit k.val = b k := by
  decide +kernel

theorem trialityEvenMask_last : ∀ e : Fin 64, (trialityEvenMask e).testBit 7 = false := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Compare the 64 canonical sign masks on their eight local coordinates.
theorem trialityEvenMask_injective : Function.Injective
    (fun e : Fin 64 => fun k : Fin 8 => (trialityEvenMask e).testBit k.val) := by
  decide +kernel

/-- Physical integer coordinates of the shortest vectors, with one representative
for each pair {λ,−λ}. The three formulas are Seysen §6.2, equation (6.1.1). -/
def griessShortIntegral : GriessShortIndex → (Fin 24 → ℤ)
  | Sum.inl (s, p) => fun i =>
      4 * (if i = (griessCoordinatePair p).1 then 1 else 0) +
        (if s = 0 then -4 else 4) * (if i = (griessCoordinatePair p).2 then 1 else 0)
  | Sum.inr (Sum.inl (d, e)) => fun i =>
      if (golayEncodedMask (golayOctadLabel d).val).testBit i.val then
        if (griessOctadSignMask d e).testBit i.val then -2 else 2
      else 0
  | Sum.inr (Sum.inr (d, j)) => fun i =>
      (if (golayEncodedMask d.val).testBit i.val then -1 else 1) *
        (if i = j then -3 else 1)

/-- The physical real vector in Conway's normalization by sqrt(8). -/
noncomputable def griessShortVector (r : GriessShortIndex) (i : Fin 24) : ℝ :=
  (griessShortIntegral r i : ℝ) / Real.sqrt 8


/-- Code coordinates of the short group labels in Seysen §6.2. Multiplication
by Ω is the toggle of coefficient eleven. -/
def griessShortCodeMask : GriessShortIndex → ℕ
  | Sum.inl (s, _) => if s = 0 then 0 else 2048
  | Sum.inr (Sum.inl (d, e)) => (golayOctadLabel d).val ^^^
      (if trialityBitWeight8 (trialityEvenMask e) / 2 % 2 = 0 then 0 else 2048)
  | Sum.inr (Sum.inr (d, i)) => d.val ^^^
      (if (golayMaskWeight (golayEncodedMask d.val) / 4 +
        if (golayEncodedMask d.val).testBit i.val then 1 else 0) % 2 = 0 then 0 else 2048)

/-- Cocode coordinates of the same short labels. The central coefficient of
these preferred X⁺ representatives is zero in the modified-code/cocode model. -/
def griessShortCocodeMask : GriessShortIndex → ℕ
  | Sum.inl (_, p) => golayCocodeDualMask
      (2 ^ (griessCoordinatePair p).1.val ||| 2 ^ (griessCoordinatePair p).2.val)
  | Sum.inr (Sum.inl (d, e)) =>
      parkerThetaMask (golayOctadLabel d).val ^^^ golayCocodeDualMask (griessOctadSignMask d e)
  | Sum.inr (Sum.inr (d, i)) => parkerThetaMask d.val ^^^ golayCocodeDualMask (2 ^ i.val)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
