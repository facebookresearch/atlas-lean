/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Algebraic parity transport for the actual compact binary and quadratic matrices. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
private def bin (b : Bool) : ZMod 2 := if b then 1 else 0
private theorem bin_xor (a b : Bool) : bin (Bool.xor a b) = bin a + bin b := by
  cases a <;> cases b <;> decide
private theorem bin_and (a b : Bool) : bin (a && b) = bin a * bin b := by
  cases a <;> cases b <;> decide
private theorem bin_fold (l : List Bool) (a : Bool) :
    bin (l.foldl Bool.xor a) = bin a + (l.map bin).sum := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, bin_xor]
    abel
private theorem parity_bin (n r : ℕ) :
    bin (monsterNortonBitParity (n &&& r)) =
      ∑ j : Fin 12, bin (n.testBit j.val) * bin (r.testBit j.val) := by
  have h : monsterNortonBitParity (n &&& r) =
      (List.ofFn (fun j : Fin 12 => (n &&& r).testBit j.val)).foldl Bool.xor false := rfl
  rw [h, bin_fold]
  simp only [bin, Bool.false_eq_true, ite_false, zero_add, List.map_ofFn,
    List.sum_ofFn, Nat.testBit_and]
  apply Finset.sum_congr rfl
  intro j _
  change bin (n.testBit j.val && r.testBit j.val) = _
  rw [bin_and]
  rfl
private theorem perm_parity (k : Fin 2) (n : Fin 4096) (i : Fin 12) :
    monsterNortonUCompactPermutation k (golayLabelCoefficients n) i =
      bin (monsterNortonBitParity (n.val &&& monsterNortonUCompactPermutationRows k i)) := by
  rw [monsterNortonUCompactPermutation_apply, Matrix.mulVec, dotProduct, parity_bin]
  change (∑ j : Fin 12, bin ((monsterNortonUCompactPermutationRows k i).testBit j.val) *
    bin (n.val.testBit j.val)) = _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem label_bin (b : Fin 12 → Bool) :
    nortonUIntegerLabel (fun i => bin (b i)) =
      ⟨(∑ i : Fin 12, if b i then 2 ^ i.val else 0) % 4096,
        Nat.mod_lt _ (by norm_num)⟩ := by
  have hs : (nortonUIntegerLabel (fun i => bin (b i))).val =
      ∑ i : Fin 12, if b i then 2 ^ i.val else 0 := by
    change (∑ i : Fin 12, (bin (b i)).val * 2 ^ i.val) = _
    apply Finset.sum_congr rfl
    intro i _
    have h1 : (1 : ZMod 2).val = 1 := by decide
    cases hb : b i <;> simp [bin, h1]
  apply Fin.ext
  change (nortonUIntegerLabel (fun i => bin (b i))).val =
    (∑ i : Fin 12, if b i then 2 ^ i.val else 0) % 4096
  rw [← hs, Nat.mod_eq_of_lt (nortonUIntegerLabel (fun i => bin (b i))).isLt]

set_option maxHeartbeats 1000000 in
-- Normalize the twelve packed coordinates before associating the scalar sums.
/-- The bitwise permutation formula is exactly the actual binary linear map on every label. -/
theorem monsterNortonUCompactBitPermutation_actual (k : Fin 2) (n : Fin 4096) :
    nortonUIntegerLabel (monsterNortonUCompactPermutation k (golayLabelCoefficients n)) =
      monsterNortonUCompactBitPermutation k n := by
  have hc : monsterNortonUCompactPermutation k (golayLabelCoefficients n) =
      fun i => bin (monsterNortonBitParity
        (n.val &&& monsterNortonUCompactPermutationRows k i)) := by
    funext i
    exact perm_parity k n i
  rw [hc, label_bin]
  apply Fin.ext
  dsimp only [monsterNortonUCompactBitPermutation]
  apply congrArg (fun m : ℕ => m % 4096)
  norm_num [Fin.sum_univ_succ]
  abel

private theorem parity_sum (n : ℕ) :
    bin (monsterNortonBitParity n) = ∑ j : Fin 12, bin (n.testBit j.val) := by
  have h : monsterNortonBitParity n =
      (List.ofFn (fun j : Fin 12 => n.testBit j.val)).foldl Bool.xor false := rfl
  rw [h, bin_fold]
  simp only [bin, Bool.false_eq_true, ite_false, zero_add, List.map_ofFn, List.sum_ofFn]
  rfl

private theorem parity_xor (m n : ℕ) :
    bin (monsterNortonBitParity (m ^^^ n)) =
      bin (monsterNortonBitParity m) + bin (monsterNortonBitParity n) := by
  rw [parity_sum, parity_sum, parity_sum]
  simp only [Nat.testBit_xor, bin_xor, Finset.sum_add_distrib]

private theorem selected_parity (k : Fin 2) (n : Fin 4096) (i : Fin 12) :
    bin (monsterNortonBitParity (if n.val.testBit i.val then
      n.val &&& monsterNortonUCompactDiagonalRows k i else 0)) =
        ∑ j : Fin 12, bin (n.val.testBit i.val) * bin (n.val.testBit j.val) *
          bin ((monsterNortonUCompactDiagonalRows k i).testBit j.val) := by
  cases h : n.val.testBit i.val
  · simp [bin, monsterNortonBitParity]
  · change bin (monsterNortonBitParity (n.val &&& monsterNortonUCompactDiagonalRows k i)) =
      ∑ j : Fin 12, bin true * bin (n.val.testBit j.val) *
        bin ((monsterNortonUCompactDiagonalRows k i).testBit j.val)
    rw [parity_bin]
    simp only [show bin true = (1 : ZMod 2) from rfl, one_mul]

set_option maxHeartbeats 1000000 in
-- Normalize the twelve packed coordinates before associating the scalar sums.
/-- The bitwise sign formula is exactly the actual quadratic form on every label. -/
theorem monsterNortonUCompactBitDiagonal_actual (k : Fin 2) (n : Fin 4096) :
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal k)
      (golayLabelCoefficients n)) = monsterNortonUCompactBitDiagonal k n := by
  let x : ℕ := (if n.val.testBit 0 then n.val &&& monsterNortonUCompactDiagonalRows k 0 else 0) ^^^
    (if n.val.testBit 1 then n.val &&& monsterNortonUCompactDiagonalRows k 1 else 0) ^^^
    (if n.val.testBit 2 then n.val &&& monsterNortonUCompactDiagonalRows k 2 else 0) ^^^
    (if n.val.testBit 3 then n.val &&& monsterNortonUCompactDiagonalRows k 3 else 0) ^^^
    (if n.val.testBit 4 then n.val &&& monsterNortonUCompactDiagonalRows k 4 else 0) ^^^
    (if n.val.testBit 5 then n.val &&& monsterNortonUCompactDiagonalRows k 5 else 0) ^^^
    (if n.val.testBit 6 then n.val &&& monsterNortonUCompactDiagonalRows k 6 else 0) ^^^
    (if n.val.testBit 7 then n.val &&& monsterNortonUCompactDiagonalRows k 7 else 0) ^^^
    (if n.val.testBit 8 then n.val &&& monsterNortonUCompactDiagonalRows k 8 else 0) ^^^
    (if n.val.testBit 9 then n.val &&& monsterNortonUCompactDiagonalRows k 9 else 0) ^^^
    (if n.val.testBit 10 then n.val &&& monsterNortonUCompactDiagonalRows k 10 else 0) ^^^
    (if n.val.testBit 11 then n.val &&& monsterNortonUCompactDiagonalRows k 11 else 0)
  have hq : monsterMonomialQuadratic (monsterNortonUCompactDiagonal k)
      (golayLabelCoefficients n) = bin (monsterNortonBitParity x) := by
    calc
      _ = ∑ i : Fin 12, bin (monsterNortonBitParity (if n.val.testBit i.val then
          n.val &&& monsterNortonUCompactDiagonalRows k i else 0)) := by
        unfold monsterMonomialQuadratic
        apply Finset.sum_congr rfl
        intro i _
        rw [selected_parity]
        rfl
      _ = _ := by
        dsimp only [x]
        simp_rw [parity_xor]
        norm_num [Fin.sum_univ_succ]
        abel
  rw [hq]
  change nortonUIntegerSign (bin (monsterNortonBitParity x)) =
    if monsterNortonBitParity x then -1 else 1
  cases h : monsterNortonBitParity x <;> simp [bin, nortonUIntegerSign]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
