/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortSparse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTensorOperators

/-! # Complete coordinate representations of local images

An `IdentVec` stores the three coordinate blocks of a Griess vector in the form used by the
cheap identification method: the matrix block as `MatRep`, the short block as sparse lists split
by kind (pair labels, octad blocks, odd labels) times a rational scale, and the scaled tensor
block as a rational tensor in spin labels (to be given by packed columns).  A local fiber element
acts blockwise: the matrix block by its spatial isometry, the short block by a checked sparse
transport, the tensor block by `localTensorRepresentation`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators

/-! ## Sparse short data -/

/-- A sparse short block split by kind: pair labels (`< 552`), octad blocks `(o, [(e, c)])`
standing for the flat labels `552 + 64 o + e`, and odd labels (`49128 ≤ · < 98280`). -/
structure ShortData where
  /-- Pair terms, by flat label. -/
  pairs : List (ℕ × ℤ)
  /-- Octad terms, grouped by octad. -/
  oct : List (ℕ × List (ℕ × ℤ))
  /-- Odd terms, by flat label. -/
  odd : List (ℕ × ℤ)

/-- The flat terms of one octad block. -/
def octFlat (o : ℕ) (es : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  es.map (fun p => (552 + 64 * o + p.1, p.2))

/-- The flat terms of all octad blocks. -/
def octsFlat : List (ℕ × List (ℕ × ℤ)) → List (ℕ × ℤ)
  | [] => []
  | b :: bs => octFlat b.1 b.2 ++ octsFlat bs

/-- All flat terms of a sparse short block. -/
def ShortData.flat (S : ShortData) : List (ℕ × ℤ) := S.pairs ++ octsFlat S.oct ++ S.odd

/-- The range conditions of a sparse short block. -/
def ShortData.ok (S : ShortData) : Bool :=
  S.pairs.all (fun p => decide (p.1 < 552)) &&
    S.oct.all (fun b => decide (b.1 < 759) && b.2.all (fun p => decide (p.1 < 64))) &&
    S.odd.all (fun p => decide (49128 ≤ p.1) && decide (p.1 < 98280))

/-- The rational short coordinates of a sparse list. -/
def shortFunQ (L : List (ℕ × ℤ)) (r : GriessShortIndex) : ℚ :=
  (L.map (fun p => if shortDecode p.1 = r then (p.2 : ℚ) else 0)).sum

/-- The real short block of a sparse list is its rational short coordinates. -/
theorem shortFunQ_real (L : List (ℕ × ℤ)) :
    (fun r => (shortFunQ L r : ℝ)) = shortVec L := by
  funext r
  rw [shortVec_apply, shortFunQ]
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, ih, List.filter_cons]
    by_cases h : shortDecode p.1 = r
    · simp [h]
    · simp [h]

/-- Coordinates of a concatenation. -/
theorem shortFunQ_append (A B : List (ℕ × ℤ)) (r : GriessShortIndex) :
    shortFunQ (A ++ B) r = shortFunQ A r + shortFunQ B r := by
  simp [shortFunQ, List.map_append, List.sum_append]

/-- Pairing with sparse short coordinates is a sum over the terms. -/
theorem sum_mul_shortFunQ (X : GriessShortIndex → ℚ) (L : List (ℕ × ℤ)) :
    (∑ r, X r * shortFunQ L r) = (L.map (fun p => (p.2 : ℚ) * X (shortDecode p.1))).sum := by
  induction L with
  | nil => simp [shortFunQ]
  | cons p L ih =>
    have h : ∀ r, X r * shortFunQ (p :: L) r =
        (if shortDecode p.1 = r then (p.2 : ℚ) * X r else 0) + X r * shortFunQ L r := by
      intro r
      simp only [shortFunQ, List.map_cons, List.sum_cons]
      split_ifs <;> ring
    simp only [h, Finset.sum_add_distrib, ih, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      List.map_cons, List.sum_cons]

/-! ## Complete representations -/

/-- A complete coordinate representation of a Griess vector. -/
structure IdentVec where
  /-- The matrix block. -/
  mat : MatRep
  /-- The sparse short block (before scaling). -/
  sh : ShortData
  /-- The scale of the short block. -/
  sden : ℚ
  /-- The scaled tensor block in spin labels. -/
  ten : GeneratedAxisGlobalRationalTensor

/-- The rational packet of a representation. -/
def IdentVec.packet (V : IdentVec) : GeneratedAxisGlobalRationalPacket :=
  (V.mat.toMat, (fun r => V.sden * shortFunQ V.sh.flat r,
    fun t i => V.ten (generatedAxisGlobalSpinLabel t) i))

/-- The real coordinates of a representation. -/
def IdentVec.real (V : IdentVec) : ConwayRawSpace :=
  generatedAxisGlobalRationalPacketReal V.packet

/-- The matrix block of the real coordinates. -/
theorem IdentVec.real_fst (V : IdentVec) : V.real.1 = matR V.mat.toMat := rfl

/-- The short block of the real coordinates. -/
theorem IdentVec.real_short (V : IdentVec) :
    V.real.2.1 = (V.sden : ℝ) • shortVec V.sh.flat := by
  rw [← shortFunQ_real]
  funext r
  simp [IdentVec.real, IdentVec.packet, generatedAxisGlobalRationalPacketReal]

/-- The tensor block of the real coordinates. -/
theorem IdentVec.real_tensor (V : IdentVec) :
    V.real.2.2 = generatedAxisGlobalRationalTensorReal V.ten := rfl

/-- A local fiber element acts blockwise on representations: checked matrix image, checked
sparse short transport and exact tensor image. -/
theorem IdentVec.local_actual (f : localFiberSubgroup) (V : IdentVec) (M' : MatRep)
    (S' : ShortData) (T' : GeneratedAxisGlobalRationalTensor)
    (hM : conwayMatrixAction f.val.2 (matR V.mat.toMat) = matR M'.toMat)
    (d : QMaskData) (hd : d.Valid (spinConjugation f.val.1))
    (hS : shortCheck d V.sh.flat S'.flat = true)
    (hT : localTensorRepresentation f (generatedAxisGlobalRationalTensorReal V.ten) =
      generatedAxisGlobalRationalTensorReal T')
    (x : GriessSpace) (hx : griessConwayEncode x = V.real) :
    griessConwayEncode (rhoLocal (localFiberIntoH f) x) =
      (⟨M', S', V.sden, T'⟩ : IdentVec).real := by
  change griessConwayEncode (localGriessRepresentation f x) = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply, hx]
  apply Prod.ext
  · rw [IdentVec.real_fst, IdentVec.real_fst]
    exact hM
  · apply Prod.ext
    · change localShortOperator f V.real.2.1 = _
      rw [IdentVec.real_short, IdentVec.real_short, map_smul,
        shortVec_transport f d hd _ _ hS]
    · change localTensorRepresentation f V.real.2.2 = _
      rw [IdentVec.real_tensor, IdentVec.real_tensor]
      exact hT

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
