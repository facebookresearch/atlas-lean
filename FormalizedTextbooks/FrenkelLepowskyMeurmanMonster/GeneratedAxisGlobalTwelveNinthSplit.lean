/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Block splitting of dense factory short checks

The literal short blocks of the dense source families are concatenations of literal constants
(pair terms, octad chunks, odd columns). Splitting a transported target list at the same
boundaries, a short transport check reduces to one kernel check per block, each of which decodes
only its own block (no prefix is decoded). -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent

/-- Short checks of two consecutive segments combine. -/
theorem shortCheckF_append_of (d : QMaskP) : ∀ (A A' B B' : List (ℕ × ℤ)),
    shortCheckF d A A' = true → shortCheckF d B B' = true → shortCheckF d (A ++ B) (A' ++ B') = true
  | [], [], _, _, _, h => h
  | [], _ :: _, _, _, h, _ => by simp [shortCheckF] at h
  | _ :: _, [], _, _, h, _ => by simp [shortCheckF] at h
  | a :: A, a' :: A', B, B', h, hB => by
    simp only [List.cons_append, shortCheckF, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, shortCheckF_append_of d A A' B B' h.2 hB⟩

/-- The flat terms of consecutive octad blocks. -/
theorem octsFlat_append : ∀ (A B : List (ℕ × List (ℕ × ℤ))),
    octsFlat (A ++ B) = octsFlat A ++ octsFlat B
  | [], _ => rfl
  | b :: A, B => by simp only [List.cons_append, octsFlat, octsFlat_append A B, List.append_assoc]

/-- The flat Ninth source terms in literal blocks. -/
theorem srcNinthCShort_flat_blocks : srcNinthCShort.flat =
    srcNinthCPairs ++ (octsFlat srcNinthCOct0 ++ (octsFlat srcNinthCOct1 ++
      (octsFlat srcNinthCOct2 ++
      (octsFlat srcNinthCOct3 ++ (octsFlat srcNinthCOct4 ++ (octsFlat srcNinthCOct5 ++
      (octsFlat srcNinthCOct6 ++ (srcNinthCOdd0 ++ (srcNinthCOdd1 ++ (srcNinthCOdd2 ++
      (srcNinthCOdd3 ++
      (srcNinthCOdd4 ++ (srcNinthCOdd5 ++ (srcNinthCOdd6 ++ (srcNinthCOdd7 ++ (srcNinthCOdd8 ++
      (srcNinthCOdd9 ++ (srcNinthCOdd10 ++ (srcNinthCOdd11 ++ (srcNinthCOdd12 ++ (srcNinthCOdd13 ++
      (srcNinthCOdd14 ++ (srcNinthCOdd15 ++ (srcNinthCOdd16 ++ (srcNinthCOdd17 ++ (srcNinthCOdd18 ++
      (srcNinthCOdd19 ++ (srcNinthCOdd20 ++ (srcNinthCOdd21 ++ (srcNinthCOdd22 ++
      srcNinthCOdd23)))))))))))))))))))))))))))))) := by
  simp only [srcNinthCShort, ShortData.flat, srcNinthCOctLit, srcNinthCOddLit, octsFlat_append,
    List.append_assoc]

/-- The flat Tenth source terms in literal blocks. -/
theorem srcTenthCShort_flat_blocks : srcTenthCShort.flat =
    srcTenthCPairs ++ (octsFlat srcTenthCOct0 ++ (octsFlat srcTenthCOct1 ++
      (octsFlat srcTenthCOct2 ++
      (octsFlat srcTenthCOct3 ++ (octsFlat srcTenthCOct4 ++ (octsFlat srcTenthCOct5 ++
      (srcTenthCOdd0 ++ (srcTenthCOdd1 ++ (srcTenthCOdd2 ++ (srcTenthCOdd3 ++
      (srcTenthCOdd4 ++ (srcTenthCOdd5 ++ (srcTenthCOdd6 ++ (srcTenthCOdd7 ++ (srcTenthCOdd8 ++
      (srcTenthCOdd9 ++ (srcTenthCOdd10 ++ (srcTenthCOdd11 ++ (srcTenthCOdd12 ++ (srcTenthCOdd13 ++
      (srcTenthCOdd14 ++ (srcTenthCOdd15 ++ (srcTenthCOdd16 ++ (srcTenthCOdd17 ++ (srcTenthCOdd18 ++
      (srcTenthCOdd19 ++ (srcTenthCOdd20 ++ (srcTenthCOdd21 ++ (srcTenthCOdd22 ++
      srcTenthCOdd23))))))))))))))))))))))))))))) := by
  simp only [srcTenthCShort, ShortData.flat, srcTenthCOctLit, srcTenthCOddLit, octsFlat_append,
    List.append_assoc]

/-- The odd Twelfth source columns in literal blocks. -/
theorem twelfthLitOdd_blocks : (List.range 24).flatMap twelfthLitOddCol =
    twelfthLitOddCol 0 ++ (twelfthLitOddCol 1 ++ (twelfthLitOddCol 2 ++ (twelfthLitOddCol 3 ++
      (twelfthLitOddCol 4 ++ (twelfthLitOddCol 5 ++ (twelfthLitOddCol 6 ++ (twelfthLitOddCol 7 ++
      (twelfthLitOddCol 8 ++ (twelfthLitOddCol 9 ++ (twelfthLitOddCol 10 ++ (twelfthLitOddCol 11 ++
      (twelfthLitOddCol 12 ++ (twelfthLitOddCol 13 ++ (twelfthLitOddCol 14 ++
      (twelfthLitOddCol 15 ++
      (twelfthLitOddCol 16 ++ (twelfthLitOddCol 17 ++ (twelfthLitOddCol 18 ++
      (twelfthLitOddCol 19 ++
      (twelfthLitOddCol 20 ++ (twelfthLitOddCol 21 ++ (twelfthLitOddCol 22 ++
      twelfthLitOddCol 23)))))))))))))))))))))) := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_singleton, List.append_assoc]

/-- The flat Twelfth source terms in literal blocks. -/
theorem twelfthShS_flat_blocks : twelfthShS.flat =
    twelfthSrcPairs128 ++ (octsFlat twelfthLitOct0 ++ (octsFlat twelfthLitOct1 ++
      (octsFlat twelfthLitOct2 ++ (octsFlat twelfthLitOct3 ++ (octsFlat twelfthLitOct4 ++
      (twelfthLitOddCol 0 ++ (twelfthLitOddCol 1 ++ (twelfthLitOddCol 2 ++ (twelfthLitOddCol 3 ++
      (twelfthLitOddCol 4 ++ (twelfthLitOddCol 5 ++ (twelfthLitOddCol 6 ++ (twelfthLitOddCol 7 ++
      (twelfthLitOddCol 8 ++ (twelfthLitOddCol 9 ++ (twelfthLitOddCol 10 ++ (twelfthLitOddCol 11 ++
      (twelfthLitOddCol 12 ++ (twelfthLitOddCol 13 ++ (twelfthLitOddCol 14 ++
      (twelfthLitOddCol 15 ++
      (twelfthLitOddCol 16 ++ (twelfthLitOddCol 17 ++ (twelfthLitOddCol 18 ++
      (twelfthLitOddCol 19 ++
      (twelfthLitOddCol 20 ++ (twelfthLitOddCol 21 ++ (twelfthLitOddCol 22 ++
      twelfthLitOddCol 23)))))))))))))))))))))))))))) := by
  simp only [twelfthShS, ShortData.flat, twelfthLitOct, octsFlat_append, twelfthLitOdd_blocks,
    List.append_assoc]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
