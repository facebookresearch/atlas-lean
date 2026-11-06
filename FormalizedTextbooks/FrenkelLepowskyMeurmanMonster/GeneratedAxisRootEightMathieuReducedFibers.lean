/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReductionActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactSourceComparison

/-! Actual compact fibers of the reduced Mathieu pair retain their original spatial maps. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The reduced pair evaluated in the full original source fibers. -/
def generatedRootEightMathieuReducedSourceFiber (j : Fin 2) : localFiberSubgroup :=
  if j = 0 then generatedRootEightCompactSourceFiber 0 *
    generatedRootEightCompactSourceFiber 4 * generatedRootEightCompactSourceFiber 1
  else generatedRootEightCompactSourceFiber 8

/-- Compatible compact full fibers for the actual reduced pair, with complete Q source premises. -/
def generatedRootEightMathieuReducedCompactFiber
    (h0 : generatedRootEightCompactSourceCondition 0)
    (h1 : generatedRootEightCompactSourceCondition 1)
    (h4 : generatedRootEightCompactSourceCondition 4)
    (h8 : generatedRootEightCompactSourceCondition 8) (j : Fin 2) : localFiberSubgroup :=
  if j = 0 then generatedRootEightCompactSourceCertifiedFiber 0 h0 *
    generatedRootEightCompactSourceCertifiedFiber 4 h4 *
    generatedRootEightCompactSourceCertifiedFiber 1 h1
  else generatedRootEightCompactSourceCertifiedFiber 8 h8

/-- Actual Q correction on the left of a complete reduced compact generator. -/
def generatedRootEightMathieuReducedCorrectedFiber
    (h0 : generatedRootEightCompactSourceCondition 0)
    (h1 : generatedRootEightCompactSourceCondition 1)
    (h4 : generatedRootEightCompactSourceCondition 4)
    (h8 : generatedRootEightCompactSourceCondition 8) (q : Q) (j : Fin 2) : localFiberSubgroup :=
  localFiberIncl q * generatedRootEightMathieuReducedCompactFiber h0 h1 h4 h8 j

/-- Each original Mathieu source spatial map is exactly its unsigned genuine permutation. -/
theorem generatedRootEight_mathieu_source_spatial (j : Fin 10) :
    (generatedRootEightCompactSourceFiber (Fin.castAdd 4 j)).val.2 =
      golayPermutationIsometry (leechNormSixHS100MathieuOriginalGenerator j) := by
  have hj12 : j.val < 12 := by omega
  simp only [generatedRootEightCompactSourceFiber, Fin.val_castAdd, hj12, dite_true,
    generatedRootEightGeneratorPrimitiveFiber, j.isLt, dite_true]
  rw [generatedRootEight_permutation_word_fiber_spatial,
    ← leechNormSixHS100Mathieu_original_words]

private theorem source_spatial_00 :
    (generatedRootEightCompactSourceFiber 0).val.2 =
      golayPermutationIsometry (leechNormSixHS100MathieuOriginalGenerator 0) :=
  generatedRootEight_mathieu_source_spatial 0

private theorem source_spatial_01 :
    (generatedRootEightCompactSourceFiber 1).val.2 =
      golayPermutationIsometry (leechNormSixHS100MathieuOriginalGenerator 1) :=
  generatedRootEight_mathieu_source_spatial 1

private theorem source_spatial_04 :
    (generatedRootEightCompactSourceFiber 4).val.2 =
      golayPermutationIsometry (leechNormSixHS100MathieuOriginalGenerator 4) :=
  generatedRootEight_mathieu_source_spatial 4

private theorem source_spatial_08 :
    (generatedRootEightCompactSourceFiber 8).val.2 =
      golayPermutationIsometry (leechNormSixHS100MathieuOriginalGenerator 8) :=
  generatedRootEight_mathieu_source_spatial 8

private theorem fiber_spatial_mul (a b : localFiberSubgroup) :
    (a * b).val.2 = a.val.2 * b.val.2 := rfl

private theorem fiber_spatial_mul_three (a b c : localFiberSubgroup) :
    (a * b * c).val.2 = a.val.2 * b.val.2 * c.val.2 := rfl

private theorem permutation_mul_three (a b c : golayAutomorphismSubgroup) :
    golayPermutationIsometry (a * b * c) =
      golayPermutationIsometry a * golayPermutationIsometry b * golayPermutationIsometry c := by
  change golayPermutationHom (a * b * c) =
    golayPermutationHom a * golayPermutationHom b * golayPermutationHom c
  rw [map_mul, map_mul]

private theorem compact_source_spatial (i : Fin 14)
    (h : generatedRootEightCompactSourceCondition i) :
    (generatedRootEightCompactSourceCertifiedFiber i h).val.2 =
      (generatedRootEightCompactSourceFiber i).val.2 := rfl

/-- The complete reduced source fibers have exactly the genuine positive reduced permutations. -/
theorem generatedRootEight_mathieu_reduced_source_spatial (j : Fin 2) :
    (generatedRootEightMathieuReducedSourceFiber j).val.2 =
      golayPermutationIsometry (generatedRootEightMathieuReducedGenerator j) := by
  unfold generatedRootEightMathieuReducedSourceFiber generatedRootEightMathieuReducedGenerator
  split_ifs
  · rw [fiber_spatial_mul_three, source_spatial_00,
      source_spatial_04, source_spatial_01,
      permutation_mul_three]
  · exact source_spatial_08

/-- Compact substitution retains the entire original reduced spatial map. -/
theorem generatedRootEight_mathieu_reduced_compact_spatial
    (h0 : generatedRootEightCompactSourceCondition 0)
    (h1 : generatedRootEightCompactSourceCondition 1)
    (h4 : generatedRootEightCompactSourceCondition 4)
    (h8 : generatedRootEightCompactSourceCondition 8) (j : Fin 2) :
    (generatedRootEightMathieuReducedCompactFiber h0 h1 h4 h8 j).val.2 =
      golayPermutationIsometry (generatedRootEightMathieuReducedGenerator j) := by
  unfold generatedRootEightMathieuReducedCompactFiber generatedRootEightMathieuReducedGenerator
  split_ifs
  · rw [fiber_spatial_mul_three, compact_source_spatial, compact_source_spatial,
      compact_source_spatial, source_spatial_00,
      source_spatial_04, source_spatial_01,
      permutation_mul_three]
  · rw [compact_source_spatial]
    exact source_spatial_08

/-- Actual Q correction preserves every coordinate of the genuine reduced spatial map. -/
theorem generatedRootEight_mathieu_reduced_corrected_spatial
    (h0 : generatedRootEightCompactSourceCondition 0)
    (h1 : generatedRootEightCompactSourceCondition 1)
    (h4 : generatedRootEightCompactSourceCondition 4)
    (h8 : generatedRootEightCompactSourceCondition 8) (q : Q) (j : Fin 2) :
    (generatedRootEightMathieuReducedCorrectedFiber h0 h1 h4 h8 q j).val.2 =
      golayPermutationIsometry (generatedRootEightMathieuReducedGenerator j) := by
  rw [generatedRootEightMathieuReducedCorrectedFiber, fiber_spatial_mul,
    show (localFiberIncl q).val.2 = 1 from rfl, one_mul,
    generatedRootEight_mathieu_reduced_compact_spatial]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
