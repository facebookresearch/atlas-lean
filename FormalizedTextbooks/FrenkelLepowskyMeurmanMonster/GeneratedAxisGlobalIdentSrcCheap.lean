/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentWiden

/-! # Helpers for cheap triality source vectors

Congruence and scaling lemmas for the literal checks of the generic triality image `twTriVec`
(worker gtwelfth): the matrix, pair and octad label checks read only the matrix block, the short
block and the short scale of the incoming vector, and the pair check is invariant under scaling the
literal pair numerators together with the scale. Splitting lemmas for the octad blocks and the odd
terms of the image, and decoders of packed literal short lists (labels with signed `8`-bit
numerators). -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The matrix check reads only the matrix block, the short block and the short scale. -/
theorem srcTwMatCheck_congr (M' : MatRep) (L L' : IdentVec) (hm : L.mat = L'.mat)
    (hs : L.sh = L'.sh) (hd : L.sden = L'.sden) : twMatCheck M' L = twMatCheck M' L' := by
  unfold twMatCheck twTriMatEntry
  rw [hm, hs, hd]

/-- The octad label check reads only the short block. -/
theorem srcTwOctCheck_congr (os : List ℕ) (L L' : IdentVec) (hs : L.sh = L'.sh) :
    twOctCheck os L = twOctCheck os L' := by
  unfold twOctCheck
  rw [hs]

/-- The pair check reads only the matrix block, the short block and the short scale. -/
theorem srcTwPairCheck_congr (P' : List (ℕ × ℤ)) (L L' : IdentVec) (D : ℚ) (hm : L.mat = L'.mat)
    (hs : L.sh = L'.sh) (hd : L.sden = L'.sden) : twPairCheck P' L D = twPairCheck P' L' D := by
  unfold twPairCheck twTriPairEntry
  rw [hm, hs, hd]

/-- Lookups in a list with scaled numerators. -/
theorem srcLookupQ_scale (c : ℤ) (lab : ℕ) : ∀ P : List (ℕ × ℤ),
    lookupQ (P.map (fun q => (q.1, c * q.2))) lab = c * lookupQ P lab
  | [] => by simp [lookupQ]
  | q :: P => by
    have ih := srcLookupQ_scale c lab P
    simp only [lookupQ, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    split_ifs <;> push_cast <;> ring

/-- The pair check is invariant under scaling the numerators together with the scale. -/
theorem srcTwPairCheck_scale (P : List (ℕ × ℤ)) (c : ℤ) (L : IdentVec) (D E : ℚ)
    (hc : (c : ℚ) ≠ 0) (hD : D = c * E) :
    twPairCheck (P.map (fun q => (q.1, c * q.2))) L D = twPairCheck P L E := by
  have key : ∀ x : ℚ, (c : ℚ) * x / (2 * D) = x / (2 * E) := fun x => by
    rw [hD, mul_left_comm, mul_div_mul_left _ _ hc]
  unfold twPairCheck
  simp only [List.all_map, Function.comp_def, srcLookupQ_scale, key]

/-- Octad blocks of the image over a concatenated octad label list. -/
theorem srcTwTriOct_append (K : ℤ) (B : List (ℕ × List (ℕ × ℤ))) (a b : List ℕ) :
    twTriOct K B (a ++ b) = twTriOct K B a ++ twTriOct K B b := by
  unfold twTriOct
  rw [List.map_append]

/-- The odd terms of the image in four blocks of six columns. -/
theorem srcTwTriOdd_split (w : ℕ) (X : List SVec) :
    twTriOdd w X = (List.range' 0 6).flatMap (twOddCol w X) ++
      (List.range' 6 6).flatMap (twOddCol w X) ++ (List.range' 12 6).flatMap (twOddCol w X) ++
      (List.range' 18 6).flatMap (twOddCol w X) := by
  unfold twTriOdd
  rw [← List.flatMap_append, ← List.flatMap_append, ← List.flatMap_append]
  rfl

/-- Decode `n` terms from `25`-bit fields: a `17`-bit label and an `8`-bit numerator (offset
`128`). -/
def srcDecT (v : ℕ) : ℕ → List (ℕ × ℤ)
  | 0 => []
  | n + 1 => ((v &&& 131071 : ℕ), (((v >>> 17) &&& 255 : ℕ) : ℤ) - 128) :: srcDecT (v >>> 25) n

/-- Decode `n` octad entries from `14`-bit fields: a `6`-bit position and an `8`-bit numerator
(offset `128`). -/
def srcDecE (v : ℕ) : ℕ → List (ℕ × ℤ)
  | 0 => []
  | n + 1 => ((v &&& 63 : ℕ), (((v >>> 6) &&& 255 : ℕ) : ℤ) - 128) :: srcDecE (v >>> 14) n

/-- Decode `n` octad blocks: `10`-bit octad labels, `7`-bit entry counts and `14`-bit entries. -/
def srcDecOcts (idx cnt ent : ℕ) : ℕ → List (ℕ × List (ℕ × ℤ))
  | 0 => []
  | n + 1 => ((idx &&& 1023 : ℕ),
      srcDecE (ent &&& ((1 <<< (14 * (cnt &&& 127))) - 1)) (cnt &&& 127)) ::
        srcDecOcts (idx >>> 10) (cnt >>> 7) (ent >>> (14 * (cnt &&& 127))) n

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
