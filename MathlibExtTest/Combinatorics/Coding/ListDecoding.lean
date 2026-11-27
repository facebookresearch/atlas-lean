/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.ListDecoding

open MathlibExt.Combinatorics.Coding.ListDecoding

/-- The binary repetition code of length 3. -/
def rep3 : Finset (Fin 3 → Bool) := {fun _ => false, fun _ => true}

theorem rep3_dist : ∀ c₁ ∈ rep3, ∀ c₂ ∈ rep3, c₁ ≠ c₂ → 3 ≤ hammingDist c₁ c₂ := by
  decide

-- Johnson radius for `n = d = 3`: `(3 - 1)² = 4 > 3 · 0`, so radius 1 is list decodable.
example : IsListDecodable rep3 1 (3 * 3) :=
  isListDecodable_of_johnson rep3 (d := 3) (by norm_num) le_rfl rep3_dist (by norm_num)

-- The sharp form: `|S| · (4 - 0) ≤ 3 · (2 - 0)`, i.e. at most one codeword within distance 1.
example (y : Fin 3 → Bool) :
    (rep3.filter fun c => hammingDist y c ≤ 1).card * ((3 - 1) ^ 2 - 3 * (3 - 3)) ≤
      3 * ((3 - 1) - (3 - 3)) :=
  johnson_bound _ y (d := 3) (by norm_num) le_rfl
    (fun c₁ h₁ c₂ h₂ hne => rep3_dist c₁ (Finset.mem_filter.mp h₁).1 c₂
      (Finset.mem_filter.mp h₂).1 hne)
    (fun c hc => (Finset.mem_filter.mp hc).2) (by norm_num)

-- Monotonicity in the list size.
example : IsListDecodable rep3 1 100 :=
  (isListDecodable_of_johnson rep3 (d := 3) (by norm_num) le_rfl rep3_dist (by norm_num)).mono
    (by norm_num)

-- Agreement count.
example : (Finset.univ.filter fun j : Fin 3 => (fun _ => false : Fin 3 → Bool) j = true).card =
    3 - hammingDist (fun _ => false : Fin 3 → Bool) (fun _ => true) :=
  card_filter_eq _ _

-- Some radius-0 ball holds at least `|C| · 1 / 2^3` codewords of the full space.
example : ∃ y : Fin 3 → Bool,
    (Finset.univ : Finset (Fin 3 → Bool)).card * (∑ i ∈ Finset.range 1, Nat.choose 3 i * 1 ^ i) ≤
      2 ^ 3 * (Finset.univ.filter fun c => hammingDist y c ≤ 0).card := by
  simpa using exists_mul_card_filter_ge (Finset.univ : Finset (Fin 3 → Bool)) 0
