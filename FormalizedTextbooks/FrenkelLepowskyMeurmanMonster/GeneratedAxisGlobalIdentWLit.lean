/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentTri

/-! # Factory literal lists and width independence (gident2)

Decoders of packed literal term lists and octad blocks (values in `b`-bit fields with offset
`2^(b-1)`), used by the factory family glue modules, and the width independence of the odd
short terms of triality images (`twOddCol_congr`): they only depend on the signed field values of
the packed tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent

/-- Decode `n` terms: labels in 17-bit fields, values in `b`-bit fields with offset `2^(b-1)`. -/
def decodeTermsB (b : ℕ) (labs nums : ℕ) : ℕ → List (ℕ × ℤ)
  | 0 => []
  | n + 1 => ((labs &&& 131071 : ℕ), ((nums &&& (2 ^ b - 1) : ℕ) : ℤ) - ((2 ^ (b - 1) : ℕ) : ℤ)) ::
      decodeTermsB b (labs >>> 17) (nums >>> b) n

/-- Decode `n` octad numerators with sign labels from `e` (values in `b`-bit fields). -/
def decodeBlockValsB (b : ℕ) (vals : ℕ) : ℕ → ℕ → List (ℕ × ℤ)
  | _, 0 => []
  | e, n + 1 => (e, ((vals &&& (2 ^ b - 1) : ℕ) : ℤ) - ((2 ^ (b - 1) : ℕ) : ℤ)) ::
      decodeBlockValsB b (vals >>> b) (e + 1) n

/-- Decode `n` octad blocks: 10-bit octad indices, 64 numerators (`b`-bit fields) per block. -/
def decodeBlocksB (b : ℕ) (idx vals : ℕ) : ℕ → List (ℕ × List (ℕ × ℤ))
  | 0 => []
  | n + 1 => ((idx &&& 1023 : ℕ), decodeBlockValsB b vals 0 64) ::
      decodeBlocksB b (idx >>> 10) (vals >>> (64 * b)) n

/-- The integer vector `e_a + e_b`. -/
def pairZ (a b : ℕ) : List ℤ := (List.range 24).map (fun j => if j = a ∨ j = b then 1 else 0)

/-- The column values are the signed field values. -/
theorem twColVals_getElem (w : ℕ) (x : SVec) (k : ℕ) (hk : k < (twColVals w x).length) :
    (twColVals w x)[k] = sval w x k := by
  have h4 : k < 4096 := by rwa [twColVals_length] at hk
  have h1 : k < (twUnpack w 12 x.1).length := by rw [twUnpack_length]; exact h4
  have h2 : k < (twUnpack w 12 x.2).length := by rw [twUnpack_length]; exact h4
  have e1 : (twUnpack w 12 x.1)[k] = fld w x.1 k := by
    have := twUnpack_getElem? w x.1 k h4
    rw [List.getElem?_eq_getElem h1] at this
    exact Option.some.inj this
  have e2 : (twUnpack w 12 x.2)[k] = fld w x.2 k := by
    have := twUnpack_getElem? w x.2 k h4
    rw [List.getElem?_eq_getElem h2] at this
    exact Option.some.inj this
  simp only [twColVals, List.getElem_zipWith, e1, e2, sval]

/-- Column values depend only on the signed field values. -/
theorem twColVals_congr (w w' : ℕ) (x x' : SVec) (h : ∀ k < 4096, sval w x k = sval w' x' k) :
    twColVals w x = twColVals w' x' := by
  apply List.ext_getElem (by rw [twColVals_length, twColVals_length])
  intro k h1 h2
  rw [twColVals_getElem, twColVals_getElem]
  exact h k (by rwa [twColVals_length] at h1)

/-- The odd short terms of a column depend only on the signed field values. -/
theorem twOddCol_congr (w w' : ℕ) (X X' : List SVec) (j : ℕ)
    (h : ∀ k < 4096, sval w (tcol X j) k = sval w' (tcol X' j) k) :
    twOddCol w X j = twOddCol w' X' j := by
  unfold twOddCol
  rw [twColVals_congr w w' _ _ h]

/-- The odd short terms depend only on the signed field values of all columns. -/
theorem twTriOdd_congr (w w' : ℕ) (X X' : List SVec)
    (h : ∀ j < 24, ∀ k < 4096, sval w (tcol X j) k = sval w' (tcol X' j) k) :
    twTriOdd w X = twTriOdd w' X' := by
  unfold twTriOdd
  apply List.flatMap_congr
  intro j hj
  exact twOddCol_congr w w' X X' j (h j (List.mem_range.mp hj))

/-- Equal rational tensors with a nonzero denominator have equal signed fields. -/
theorem sval_eq_of_tensorRat (w w' : ℕ) (X X' : List SVec) (D : ℚ) (hD : D ≠ 0)
    (h : tensorRat w X D = tensorRat w' X' D) :
    ∀ j < 24, ∀ k < 4096, sval w (tcol X j) k = sval w' (tcol X' j) k := by
  intro j hj k hk
  have := congrFun (congrFun h ⟨k, hk⟩) ⟨j, hj⟩
  simp only [tensorRat] at this
  have h2 := (div_left_inj' hD).mp this
  exact_mod_cast h2

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
