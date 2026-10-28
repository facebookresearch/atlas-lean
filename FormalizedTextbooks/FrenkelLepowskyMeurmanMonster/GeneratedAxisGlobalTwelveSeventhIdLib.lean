/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhN
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord

/-! # Split octad and odd parts for dense identification vectors

For dense representations the octad and odd parts of the self-comparison criterion
(`ident_forward_selfM` / `ident_inverse_selfM`) read thousands of fields of one packed vector with
`2^16` fields; evaluated in one kernel check this exceeds the memory budget.  The parts are sums
over the octad blocks / odd terms of the target list, which split along a split of the list
(`ShortData.ofList` regroups by filters); each piece is then evaluated in its own kernel check
against the same packed vector.  Nothing here assumes any identification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Regrouping a concatenation: octad blocks. -/
theorem ofList_oct_append (A B : List (ℕ × ℤ)) :
    (ShortData.ofList (A ++ B)).oct = (ShortData.ofList A).oct ++ (ShortData.ofList B).oct := by
  simp only [ShortData.ofList, List.filter_append, List.map_append]

/-- Regrouping a concatenation: odd terms. -/
theorem ofList_odd_append (A B : List (ℕ × ℤ)) :
    (ShortData.ofList (A ++ B)).odd = (ShortData.ofList A).odd ++ (ShortData.ofList B).odd := by
  simp only [ShortData.ofList, List.filter_append]

/-- The octad part of the pairing over a list of octad blocks. -/
def octSumB (w : ℕ) (fwd : Bool) (L : IdentVec) (B : List (ℕ × List (ℕ × ℤ))) : ℤ :=
  (B.map (fun b => (b.2.map (fun q => q.2 * octZ w fwd (octPackXH w fwd L) b.1 q.1)).sum)).sum

/-- The octad part of the pairing is the octad part over the blocks of the target. -/
theorem octSumZ_eq_B (w : ℕ) (fwd : Bool) (L W : IdentVec) :
    octSumZ w fwd L W = octSumB w fwd L W.sh.oct := rfl

/-- The octad part over blocks splits along a concatenation. -/
theorem octSumB_append (w : ℕ) (fwd : Bool) (L : IdentVec) (A B : List (ℕ × List (ℕ × ℤ))) :
    octSumB w fwd L (A ++ B) = octSumB w fwd L A + octSumB w fwd L B := by
  simp only [octSumB, List.map_append, List.sum_append]

/-- The packed octad self part over a list of octad blocks, read from the packed octad terms
of `V`. -/
def selfOctB (w : ℕ) (V : IdentVec) (B : List (ℕ × List (ℕ × ℤ))) : ℤ :=
  ((B.flatMap (fun b => b.2.map (fun q => (64 * b.1 + q.1 % 64, q.2)))).map
    (fun p => p.2 * svalS w (packH w 10 16 (octLFlat V)) p.1)).sum

/-- The packed octad self part over blocks splits along a concatenation. -/
theorem selfOctB_append (w : ℕ) (V : IdentVec) (A B : List (ℕ × List (ℕ × ℤ))) :
    selfOctB w V (A ++ B) = selfOctB w V A + selfOctB w V B := by
  simp only [selfOctB, List.flatMap_append, List.map_append, List.sum_append]

/-- The packed octad self sum is the self part over the blocks of `V`. -/
theorem selfOctPW_eq_B (w : ℕ) (V : IdentVec) (h : octPackOk w V = true) :
    selfOctPW w V = selfOctB w V V.sh.oct := by
  unfold selfOctPW
  rw [if_pos h]
  rfl

/-- The packed odd self part over a list of odd terms, read from the packed odd terms of `V`. -/
def selfOddB (V : IdentVec) (T : List (ℕ × ℤ)) : ℤ :=
  (T.map (fun q => q.2 * svalS 32 (packH 32 10 16 (oddLFlat V)) (q.1 - 49128))).sum

/-- The packed odd self part splits along a concatenation. -/
theorem selfOddB_append (V : IdentVec) (A B : List (ℕ × ℤ)) :
    selfOddB V (A ++ B) = selfOddB V A + selfOddB V B := by
  simp only [selfOddB, List.map_append, List.sum_append]

/-- The packed odd self sum is the self part over the odd terms of `V`. -/
theorem selfOddP_eq_B (V : IdentVec) (h : oddPackOk V = true) :
    selfOddP V = selfOddB V V.sh.odd := by
  unfold selfOddP
  rw [if_pos h]
  rfl

/-- The odd part of the pairing over a list of odd terms. -/
def oddWB (w : ℕ) (fwd : Bool) (X : List SVec) (T : List (ℕ × ℤ)) : ℤ :=
  (T.map (fun q => q.2 * oddWTerm w fwd X q.1)).sum

/-- The odd part of the pairing is the odd part over the odd terms of the target. -/
theorem oddWZ_eq_B (w : ℕ) (fwd : Bool) (X : List SVec) (W : IdentVec) :
    oddWZ w fwd X W = oddWB w fwd X W.sh.odd := rfl

/-- The odd part over terms splits along a concatenation. -/
theorem oddWB_append (w : ℕ) (fwd : Bool) (X : List SVec) (A B : List (ℕ × ℤ)) :
    oddWB w fwd X (A ++ B) = oddWB w fwd X A + oddWB w fwd X B := by
  simp only [oddWB, List.map_append, List.sum_append]

/-- The odd-to-tensor part over a list of odd terms of the source. -/
def oddLB (w : ℕ) (fwd : Bool) (Y : List SVec) (T : List (ℕ × ℤ)) : ℤ :=
  (T.map (fun q => q.2 * oddLTerm w fwd Y q.1)).sum

/-- The odd-to-tensor part is the part over the odd terms of the source. -/
theorem oddLZ_eq_B (w : ℕ) (fwd : Bool) (Y : List SVec) (L : IdentVec) :
    oddLZ w fwd Y L = oddLB w fwd Y L.sh.odd := rfl

/-- The odd-to-tensor part over terms splits along a concatenation. -/
theorem oddLB_append (w : ℕ) (fwd : Bool) (Y : List SVec) (A B : List (ℕ × ℤ)) :
    oddLB w fwd Y (A ++ B) = oddLB w fwd Y A + oddLB w fwd Y B := by
  simp only [oddLB, List.map_append, List.sum_append]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
