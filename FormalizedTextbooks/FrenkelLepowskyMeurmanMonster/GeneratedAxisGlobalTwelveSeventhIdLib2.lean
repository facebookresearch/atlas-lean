/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ

/-! # Split pair parts for dense identification vectors

The pair contributions to the matrix part (`triMatZI`) and to the pair part (`pairSumZI`) of the
self-comparison criterion, and the pair self sum `selfPairsZ`, are sums over the pair terms of a
regrouped target list; they split along a split of the list and each piece is evaluated in its
own kernel check.  Nothing here assumes any identification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Regrouping a concatenation: pair terms. -/
theorem ofList_pairs_append (A B : List (ℕ × ℤ)) :
    (ShortData.ofList (A ++ B)).pairs = (ShortData.ofList A).pairs ++ (ShortData.ofList B).pairs := by
  simp only [ShortData.ofList, List.filter_append]

/-- The diagonal terms of the integer matrix part. -/
def triMatDiag (LM WM : MatZ) : ℚ :=
  24 * LM.scal * WM.scal +
    LM.scal * ((((List.finRange 24).map (fun i => WM.num i i)).sum : ℤ) : ℚ) /
      (WM.den * 4 ^ WM.k) +
    WM.scal * ((((List.finRange 24).map (fun i => LM.num i i)).sum : ℤ) : ℚ) /
      (LM.den * 4 ^ LM.k) +
    ((((List.finRange 24).map (fun i => LM.num i i * WM.num i i)).sum : ℤ) : ℚ) /
      ((LM.den * 4 ^ LM.k) * (WM.den * 4 ^ WM.k))

/-- The pair contributions to the integer matrix part over a list of pair terms of the source. -/
def triMatPB (fwd : Bool) (WM : MatZ) (P : List (ℕ × ℤ)) : ℤ :=
  (P.map (fun q => q.2 * (if fwd then 1 else if q.1 < 276 then 1 else -1) *
    WM.num (pairCoordsF q.1).1 (pairCoordsF q.1).2)).sum

/-- The integer matrix part splits into diagonal terms and pair contributions. -/
theorem triMatZI_eq_B (fwd : Bool) (LM WM : MatZ) (L : IdentVec) :
    triMatZI fwd LM WM L = triMatDiag LM WM +
      L.sden * ((triMatPB fwd WM L.sh.pairs : ℤ) : ℚ) / (WM.den * 4 ^ WM.k) := rfl

/-- The pair contributions split along a concatenation. -/
theorem triMatPB_append (fwd : Bool) (WM : MatZ) (A B : List (ℕ × ℤ)) :
    triMatPB fwd WM (A ++ B) = triMatPB fwd WM A + triMatPB fwd WM B := by
  simp only [triMatPB, List.map_append, List.sum_append]

/-- The pair part of the pairing over a list of pair terms of the target. -/
def pairSumQB (fwd : Bool) (LM : MatZ) (L : IdentVec) (P : List (ℕ × ℤ)) : ℚ :=
  (((P.map (fun q => q.2 * (if fwd then (if q.1 < 276 then 1 else -1) else 1) *
      LM.num (pairCoordsF q.1).1 (pairCoordsF q.1).2)).sum : ℤ) : ℚ) / (LM.den * 4 ^ LM.k) +
    L.sden * (((P.map (fun q => q.2 *
      (if fwd then idxSum L.sh.pairs (q.1 % 276) - idxSum L.sh.pairs (276 + q.1 % 276)
       else if q.1 < 276 then idxSum L.sh.pairs (q.1 % 276) + idxSum L.sh.pairs (276 + q.1 % 276)
       else -(idxSum L.sh.pairs (q.1 % 276) + idxSum L.sh.pairs (276 + q.1 % 276))))).sum : ℤ) :
      ℚ) / 2

/-- The integer pair part is the pair part over the pair terms of the target. -/
theorem pairSumZI_eq_B (fwd : Bool) (LM : MatZ) (L W : IdentVec) :
    pairSumZI fwd LM L W = pairSumQB fwd LM L W.sh.pairs := rfl

/-- The pair part over pair terms splits along a concatenation. -/
theorem pairSumQB_append (fwd : Bool) (LM : MatZ) (L : IdentVec) (A B : List (ℕ × ℤ)) :
    pairSumQB fwd LM L (A ++ B) = pairSumQB fwd LM L A + pairSumQB fwd LM L B := by
  simp only [pairSumQB, List.map_append, List.sum_append]
  push_cast
  ring

/-- The pair self part over a list of pair terms, against the pair terms of `V`. -/
def selfPairsB (V : IdentVec) (P : List (ℕ × ℤ)) : ℤ := (P.map (fun q => q.2 * idxSum V.sh.pairs q.1)).sum

/-- The pair self sum is the self part over the pair terms of `V`. -/
theorem selfPairsZ_eq_B (V : IdentVec) : selfPairsZ V = selfPairsB V V.sh.pairs := rfl

/-- The pair self part splits along a concatenation. -/
theorem selfPairsB_append (V : IdentVec) (A B : List (ℕ × ℤ)) :
    selfPairsB V (A ++ B) = selfPairsB V A + selfPairsB V B := by
  simp only [selfPairsB, List.map_append, List.sum_append]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
