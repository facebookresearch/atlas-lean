/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairTri
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

/-! # Kernel-fast evaluation of the exact pairings

`pairTri` is stated with the original coordinate formulas, some of which are slow to evaluate in
the kernel (Golay weights, the octad Fourier matrix, the literal pair catalogue).  Here every such
subterm is replaced by a certified packed-table reader, giving `pairTriF` with
`pairTriF fwd L W = pairTri fwd L W`.  The tensor-to-tensor sum is kept unchanged, to be
evaluated on packed tensors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators

/-! ## Fast subterms -/

/-- Parity bits of all seven-bit numbers. -/
def identParityTable : ℕ := 0x96696996699696696996966996696996

/-- Negative signs of the octad Fourier diagonal. -/
def identOctDiagTable : ℕ := 0xe88181178117177e

set_option maxRecDepth 100000 in
/-- The parity table is the weight parity of every seven-bit number. -/
theorem identParityTable_spec : ∀ x : Fin 128,
    identParityTable.testBit x.val = decide (trialityBitWeight8 x.val % 2 = 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The diagonal table gives the octad Fourier diagonal. -/
theorem identOctDiagTable_spec : ∀ e : Fin 64,
    (if identOctDiagTable.testBit e.val then (-1 : ℤ) else 1) = trialityIntegerDiagonal e := by
  decide +kernel

/-- The octad Fourier coefficient from the packed tables. -/
def octMF (fwd : Bool) (e f : ℕ) : ℚ :=
  let a := if fwd then e % 64 else f % 64
  let b := if fwd then f % 64 else e % 64
  (if identOctDiagTable.testBit a then -1 else 1) *
    (if identParityTable.testBit (identEvenMask a &&& identEvenMask b) then -1 else 1)

/-- The bitwise conjunction of two even masks is a seven-bit number. -/
theorem evenMask_and_lt (a b : Fin 64) : identEvenMask a.val &&& identEvenMask b.val < 128 :=
  lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt _ (by decide))

/-- The fast Fourier coefficient is the original one. -/
theorem octMF_eq (fwd : Bool) (e f : ℕ) : octMF fwd e f = octM fwd e f := by
  have key : ∀ a b : Fin 64,
      (if identOctDiagTable.testBit a.val then (-1 : ℚ) else 1) *
        (if identParityTable.testBit (identEvenMask a.val &&& identEvenMask b.val) then -1 else 1) =
      (trialityIntegerMatrix a b : ℚ) := by
    intro a b
    have hd := identOctDiagTable_spec a
    have hp := identParityTable_spec ⟨_, evenMask_and_lt a b⟩
    simp only at hp
    simp only [identEvenMask_actual] at hp
    rw [trialityIntegerMatrix, Int.cast_mul, ← hd, trialityHadamard]
    simp only [identEvenMask_actual]
    rw [hp]
    rcases Nat.mod_two_eq_zero_or_one
      (trialityBitWeight8 (trialityEvenMask a &&& trialityEvenMask b)) with h | h
    · simp [h]
    · simp [h]
  unfold octMF octM
  cases fwd
  · exact key ⟨f % 64, Nat.mod_lt _ (by decide)⟩ ⟨e % 64, Nat.mod_lt _ (by decide)⟩
  · exact key ⟨e % 64, Nat.mod_lt _ (by decide)⟩ ⟨f % 64, Nat.mod_lt _ (by decide)⟩

/-- The fast coordinate pair of a pair label. -/
def pairCoordsF (p : ℕ) : Fin 24 × Fin 24 := identPairFin ⟨p % 276, Nat.mod_lt _ (by decide)⟩

/-- The fast coordinate pair is the catalogue pair. -/
theorem pairCoordsF_eq (p : ℕ) : pairCoordsF p = pairCoords p := identPairFin_actual _

/-- The fast weight sign of an odd code label `d < 2048`. -/
def oddWeightSignF (d : ℕ) : ℚ := if identOddWeightFlag d = 0 then 1 else -1

/-- The fast weight sign is the original one. -/
theorem oddWeightSignF_eq (d : ℕ) (hd : d < 2048) : oddWeightSignF d = oddWeightSign d := by
  have hf := identOddWeightFlag_actual ⟨d, hd⟩
  have hw := golayEncodedMask_weights ⟨d, by omega⟩
  simp only at hf hw
  unfold oddWeightSignF oddWeightSign
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | hw | hw | hw | hw <;>
    · rw [hw] at hf ⊢
      by_cases h0 : identOddWeightFlag d = 0
      · simp only [h0, ↓reduceIte] at hf ⊢
        revert hf
        decide
      · simp only [h0, ↓reduceIte] at hf ⊢
        revert hf
        decide

/-- The fast coordinate sign of an odd code label `d < 2048`. -/
def oddCoordSignF (d j : ℕ) : ℚ := if (identOddCode d).testBit j then -1 else 1

/-- The fast coordinate sign is the original one. -/
theorem oddCoordSignF_eq (d j : ℕ) (hd : d < 2048) : oddCoordSignF d j = oddCoordSign d j := by
  unfold oddCoordSignF oddCoordSign
  rw [identOddCode_actual ⟨d, hd⟩]

/-- The fast weight sign at the code label of an odd flat label. -/
theorem oddWeightSignF_oddD (lab : ℕ) : oddWeightSignF (oddD lab) = oddWeightSign (oddD lab) :=
  oddWeightSignF_eq _ (Nat.mod_lt _ (by decide))

/-- The fast coordinate sign at the code label of an odd flat label. -/
theorem oddCoordSignF_oddD (lab j : ℕ) :
    oddCoordSignF (oddD lab) j = oddCoordSign (oddD lab) j :=
  oddCoordSignF_eq _ _ (Nat.mod_lt _ (by decide))

/-! ## Fast pairing parts -/

/-- Fast matrix part. -/
def triMatF (fwd : Bool) (L W : IdentVec) : ℚ :=
  (∑ i : Fin 24, L.mat.entry i i * W.mat.entry i i) +
    (L.sh.pairs.map (fun q => L.sden * (q.2 : ℚ) / 2 *
      (if fwd then 1 else if q.1 < 276 then 1 else -1) *
      (W.mat.entry (pairCoordsF q.1).1 (pairCoordsF q.1).2 +
        W.mat.entry (pairCoordsF q.1).2 (pairCoordsF q.1).1))).sum

/-- Fast short coordinate at a pair label. -/
def triPairF (fwd : Bool) (L : IdentVec) (lab : ℕ) : ℚ :=
  let m := L.mat.entry (pairCoordsF lab).1 (pairCoordsF lab).2
  let s0 := L.sden * lookupQ L.sh.pairs (lab % 276)
  let s1 := L.sden * lookupQ L.sh.pairs (276 + lab % 276)
  if fwd then (if lab < 276 then m + (s0 - s1) / 2 else (s0 - s1) / 2 - m)
  else (if lab < 276 then m + (s0 + s1) / 2 else m - (s0 + s1) / 2)

/-- Fast short coordinate at an octad label. -/
def triOctF (fwd : Bool) (L : IdentVec) (o e : ℕ) : ℚ :=
  L.sden * (L.sh.oct.map (fun b => if b.1 = o then
    (b.2.map (fun q => (q.2 : ℚ) * octMF fwd e q.1 / 8)).sum else 0)).sum

/-- Fast short coordinate at an odd label. -/
def triOddF (fwd : Bool) (L : IdentVec) (lab : ℕ) : ℚ :=
  let d := oddD lab
  let j : Fin 24 := ⟨oddJ lab, Nat.mod_lt _ (by decide)⟩
  let t0 := L.ten ⟨d, by unfold d oddD; omega⟩ j
  let t1 := L.ten ⟨d + 2048, by unfold d oddD; omega⟩ j
  if fwd then oddWeightSignF d * (t0 + t1) / 2 else oddCoordSignF d j.val * (t0 - t1) / 2

/-- Fast short part. -/
def triShortF (fwd : Bool) (L W : IdentVec) : ℚ :=
  W.sden * ((W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF fwd L q.1)).sum +
    (W.sh.oct.map (fun b => (b.2.map (fun q => (q.2 : ℚ) * triOctF fwd L b.1 q.1)).sum)).sum +
    (W.sh.odd.map (fun q => (q.2 : ℚ) * triOddF fwd L q.1)).sum)

/-- Fast tensor contribution of one odd term of `L`. -/
def triTCF (fwd : Bool) (W : IdentVec) (lab : ℕ) : ℚ :=
  let d := oddD lab
  let j : Fin 24 := ⟨oddJ lab, Nat.mod_lt _ (by decide)⟩
  let w0 := W.ten ⟨d, by unfold d oddD; omega⟩ j
  let w1 := W.ten ⟨d + 2048, by unfold d oddD; omega⟩ j
  if fwd then oddCoordSignF d j.val * (w0 - w1) else oddWeightSignF d * (w0 + w1)

/-- The fast exact pairing; the tensor-to-tensor sum is kept for packed evaluation. -/
def pairTriF (fwd : Bool) (L W : IdentVec) : ℚ :=
  triMatF fwd L W + triShortF fwd L W +
    ((L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) * triTCF fwd W q.1)).sum +
      ∑ k : Fin 4096, ∑ j : Fin 24, tPartQ fwd L.ten k j * W.ten k j) / 2

/-- The fast pairing is the exact pairing. -/
theorem pairTriF_eq (fwd : Bool) (L W : IdentVec) : pairTriF fwd L W = pairTri fwd L W := by
  have h1 : triMatF fwd L W = triMatQ fwd L W := by
    simp only [triMatF, triMatQ, pairCoordsF_eq]
  have h2 : ∀ lab, triPairF fwd L lab = triPairQ fwd L lab := by
    intro lab
    simp only [triPairF, triPairQ, pairCoordsF_eq]
  have h3 : ∀ o e, triOctF fwd L o e = triOctQ fwd L o e := by
    intro o e
    simp only [triOctF, triOctQ, octMF_eq]
  have h4 : ∀ lab, triOddF fwd L lab = triOddQ fwd L lab := by
    intro lab
    simp only [triOddF, triOddQ, oddWeightSignF_oddD, oddCoordSignF_oddD]
  have h5 : ∀ lab, triTCF fwd W lab = triTCQ fwd W lab := by
    intro lab
    simp only [triTCF, triTCQ, oddWeightSignF_oddD, oddCoordSignF_oddD]
  simp only [pairTriF, pairTri, triTensorQ, triShortF, triShortQ, h1, h2, h3, h4, h5]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
