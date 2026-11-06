/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQSourceWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightGeneratorCandidates

/-! Literal source-word products represent the twelve original full fibers and canonical transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

/-- The complete original fiber product of a source word, in its stated product order. -/
def generatedRootEightQSourceWordFiber (j : Fin 13) : localFiberSubgroup :=
  ((generatedRootEightQSourceWords j).map generatedRootEightQPrimitiveFiber).prod

/-- Original permutation letters included in the eleven-factor source alphabet. -/
def generatedRootEightQPermutationLetters (w : List (Fin 4)) : List (Fin 11) :=
  w.map (Fin.castAdd 7)

/-- The source words reconstructed from the original full permutation, sign, and Xi factors. -/
def generatedRootEightQDeclaredWords (j : Fin 13) : List (Fin 11) :=
  if h : j.val < 10 then
    generatedRootEightQPermutationLetters (leechNormSixHS100MathieuGeneratorWords ⟨j.val, h⟩)
  else if j.val = 10 then
    generatedRootEightQPermutationLetters (leechNormSixHS100PointMoverPermutationWords 3) ++ [5] ++
      generatedRootEightQPermutationLetters (leechNormSixHS100PointMoverPermutationWords 2) ++ [4] ++
      generatedRootEightQPermutationLetters (leechNormSixHS100PointMoverPermutationWords 1) ++
      [4, 4, 7] ++
      generatedRootEightQPermutationLetters (leechNormSixHS100PointMoverPermutationWords 0)
  else if j.val = 11 then
    [6] ++ generatedRootEightQPermutationLetters leechNormSixHS100MatePermutationWord
  else
    [10] ++ generatedRootEightQPermutationLetters
      (generatedFifthRootEightCanonicalPermutationWords 2).reverse ++ [4, 4, 9] ++
      generatedRootEightQPermutationLetters
        (generatedFifthRootEightCanonicalPermutationWords 1).reverse ++ [4, 8] ++
      generatedRootEightQPermutationLetters
        (generatedFifthRootEightCanonicalPermutationWords 0).reverse

/-- Every source-table word agrees with the full original factors, including the canonical
chronological reversal into product order. -/
theorem generatedRootEight_Q_source_words_original :
    ∀ j : Fin 13, generatedRootEightQSourceWords j = generatedRootEightQDeclaredWords j := by
  decide +kernel

private theorem permutation_letter (k : Fin 4) :
    generatedRootEightQPrimitiveFiber (Fin.castAdd 7 k) =
      generatedFifthRootEightCanonicalFiberLetter k := by
  simp only [generatedRootEightQPrimitiveFiber, Fin.val_castAdd, k.isLt, dite_true]

private theorem permutation_word (w : List (Fin 4)) :
    ((generatedRootEightQPermutationLetters w).map generatedRootEightQPrimitiveFiber).prod =
      generatedRootEightPermutationWordFiber w := by
  simp only [generatedRootEightQPermutationLetters, List.map_map, Function.comp_def,
    permutation_letter, generatedRootEightPermutationWordFiber]

private theorem chronological_product (w : List (Fin 4)) :
    w.foldl (fun f k => generatedFifthRootEightCanonicalFiberLetter k * f) 1 =
      generatedRootEightPermutationWordFiber w.reverse := by
  have aux (v : List (Fin 4)) (f : localFiberSubgroup) :
      v.foldl (fun a k => generatedFifthRootEightCanonicalFiberLetter k * a) f =
        (v.reverse.map generatedFifthRootEightCanonicalFiberLetter).prod * f := by
    induction v generalizing f with
    | nil => simp
    | cons k v ih =>
      simp only [List.foldl_cons, ih, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil,
        mul_one, mul_assoc]
  simpa only [mul_one, generatedRootEightPermutationWordFiber] using aux w 1

private theorem primitive_xi : generatedRootEightQPrimitiveFiber 4 = xiSpinLocalFiber := rfl
private theorem primitive_sign_one : generatedRootEightQPrimitiveFiber 5 = generatedFifthSignFiber 1 0 := rfl
private theorem primitive_sign_all : generatedRootEightQPrimitiveFiber 6 = generatedFifthSignFiber 2048 0 := rfl
private theorem primitive_sign_mover : generatedRootEightQPrimitiveFiber 7 = generatedFifthSignFiber 2816 0 := rfl
private theorem primitive_sign_first : generatedRootEightQPrimitiveFiber 8 = generatedFifthSignFiber 1536 0 := rfl
private theorem primitive_sign_middle : generatedRootEightQPrimitiveFiber 9 = generatedFifthSignFiber 3220 0 := rfl
private theorem primitive_sign_last : generatedRootEightQPrimitiveFiber 10 = generatedFifthSignFiber 165 0 := rfl

/-- Each of the twelve entire original source-word fibers is precisely its declared generator fiber. -/
theorem generatedRootEight_Q_source_generator_fiber (j : Fin 12) :
    generatedRootEightQSourceWordFiber (Fin.castAdd 1 j) =
      generatedRootEightGeneratorPrimitiveFiber j := by
  rw [generatedRootEightQSourceWordFiber, generatedRootEight_Q_source_words_original]
  unfold generatedRootEightQDeclaredWords generatedRootEightGeneratorPrimitiveFiber
  simp only [Fin.val_castAdd]
  split_ifs with h h10 h11
  · exact permutation_word _
  · simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, permutation_word, primitive_xi,
      primitive_sign_one, primitive_sign_mover, generatedRootEightPointMoverFiber]
    group
  · simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, permutation_word, primitive_sign_all,
      generatedRootEightMateFiber]
  · omega

/-- The thirteenth entire source-word fiber is precisely the frozen collapsed canonical fiber. -/
theorem generatedRootEight_Q_source_canonical_fiber :
    generatedRootEightQSourceWordFiber 12 = generatedRootEightCanonicalFiber := by
  rw [generatedRootEightQSourceWordFiber, generatedRootEight_Q_source_words_original]
  simp only [generatedRootEightQDeclaredWords, show ¬(12 : Fin 13).val < 10 by decide,
    show (12 : Fin 13).val ≠ 10 by decide, show (12 : Fin 13).val ≠ 11 by decide,
    dite_false, ite_false, List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, permutation_word, primitive_xi,
    primitive_sign_first, primitive_sign_middle, primitive_sign_last]
  simp only [generatedRootEightCanonicalFiber, generatedRootEightCanonicalMonomialFiber,
    generatedFifthRootEightCanonicalSignLabels, generatedFifthRootEightCanonicalPermutationFiber,
    chronological_product]
  group
  rfl

/-- Every source generator word retains the entire original local H action and phases. -/
theorem generatedRootEight_Q_source_generator_local (j : Fin 12) :
    localFiberIntoH (generatedRootEightQSourceWordFiber (Fin.castAdd 1 j)) =
      generatedRootEightGeneratorPrimitiveLocal j := by
  rw [generatedRootEight_Q_source_generator_fiber]
  rfl

/-- The complete canonical source word has the original frozen local H lift. -/
theorem generatedRootEight_Q_source_canonical_local :
    localFiberIntoH (generatedRootEightQSourceWordFiber 12) = generatedFifthRootEightCanonicalLocal := by
  rw [generatedRootEight_Q_source_canonical_fiber, generatedRootEight_canonical_fiber_local]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
