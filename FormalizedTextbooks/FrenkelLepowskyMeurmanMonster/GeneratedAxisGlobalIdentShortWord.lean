/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentLetters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortLetters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatrix

/-! # Short and matrix data of words in the identification alphabet

Adapters from the shared alphabet `IdentLetter` (worker `gident`) to the mask data and spatial
data of `gident2`.  A word is given with literal mask data for each letter; one boolean check
certifies every letter (odd source letters and extraspecial letters by comparison with their
canonical data, source signs with `ε = 0` against their exact evaluator).  The composite data
of the word are then certified by folding the coordinate generators through the word.  The
spatial alphabet gives the matrix block action of every word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent

/-! ## Mask data of letters -/

/-- Equality of two mask data, as a boolean. -/
def qmDataEq (d e : QMaskData) : Bool :=
  (List.finRange 24).all (fun i => d.cols i == e.cols i && d.rows i == e.rows i) &&
    d.coeff == e.coeff

/-- Boolean equality of mask data gives equal evaluations. -/
theorem qmDataEq_valid (d e : QMaskData) (h : qmDataEq d e = true) (a : MulAut Q)
    (he : e.Valid a) : d.Valid a := by
  simp only [qmDataEq, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    beq_iff_eq] at h
  obtain ⟨hcr, hc⟩ := h
  have hcols : d.cols = e.cols := funext (fun i => (hcr i).1)
  have hrows : d.rows = e.rows := funext (fun i => (hcr i).2)
  intro v
  rw [he v, hcols, hrows, hc]

/-- The literal-data check of one letter. -/
def identLetterCheck : IdentLetter → QMaskData → Bool
  | .xi, d => qmDataEq d (sourceLetterData 0)
  | .mono l, d => qmDataEq d (sourceLetterData (monoLetterIndex l))
  | .sign a ε, d => (ε == 0) && signLetterCheck a d
  | .qel g, d => qmDataEq d (qLetterDataZ (qmEncode g).1)

/-- Checked letter data are valid. -/
theorem identLetterCheck_sound (x : IdentLetter) (d : QMaskData)
    (h : identLetterCheck x d = true) : d.Valid (spinConjugation x.fiber.val.1) := by
  cases x with
  | xi =>
    exact qmDataEq_valid _ _ h _ xiLetterData_valid
  | mono l =>
    exact qmDataEq_valid _ _ h _ (monoLetterData_valid l)
  | sign a ε =>
    simp only [identLetterCheck, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hε, hs⟩ := h
    subst hε
    exact signLetterCheck_sound a d hs
  | qel g =>
    exact qmDataEq_valid _ _ h _ (qLetterDataZ_valid g)

/-- A checked word is computed by its word of mask data. -/
theorem identCheckedWord_spec (w : List (IdentLetter × QMaskData))
    (hw : w.all (fun p => identLetterCheck p.1 p.2) = true) (p : ℕ × Bool) :
    spinConjugation (identWordFiber (w.map Prod.fst)).val.1 (qmElt p) =
      qmElt (qmWord (w.map Prod.snd) p) := by
  induction w with
  | nil =>
    change spinConjugation 1 (qmElt p) = qmElt p
    rw [map_one]
    rfl
  | cons x w ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hw
    change spinConjugation (x.1.fiber.val.1 * (identWordFiber (w.map Prod.fst)).val.1)
      (qmElt p) = _
    rw [map_mul, MulAut.mul_apply, ih hw.2,
      x.2.step_spec _ (identLetterCheck_sound x.1 x.2 hw.1)]
    rfl

/-- Composite data of a checked word, certified by generator images and computed rows. -/
theorem identCheckedWord_valid (w : List (IdentLetter × QMaskData))
    (hw : w.all (fun p => identLetterCheck p.1 p.2) = true) (d : QMaskData)
    (hcols : ∀ i : Fin 24, qmWord (w.map Prod.snd) (2 ^ i.val, false) =
      (d.cols i, d.coeff.testBit i.val))
    (hrows : ∀ i : Fin 24, d.rows i = rowsOf d.cols i) :
    d.Valid (spinConjugation (identWordFiber (w.map Prod.fst)).val.1) := by
  apply QMaskData.valid_of_generators _ d _ hrows
  intro i
  rw [← qmElt_unit, identCheckedWord_spec w hw, hcols]

/-! ## Spatial data of letters -/

/-- The spatial isometry of a letter. -/
def identLetterSpatial : IdentLetter → leechIsomSubgroup
  | .xi => generatedAxisGlobalOddSourceSpatialLetter 0
  | .mono l => generatedAxisGlobalOddSourceSpatialLetter (monoLetterIndex l)
  | .sign a _ => golaySignIsometry (sourceGeneratedSignCode a)
  | .qel _ => 1

/-- The rational evaluator of the spatial isometry of a letter. -/
def identLetterVec : IdentLetter → List ℚ → List ℚ
  | .xi => sourceSpatialVec 0
  | .mono l => sourceSpatialVec (monoLetterIndex l)
  | .sign a _ => signSpatialVec a
  | .qel _ => id

/-- The spatial alphabet of the identification letters. -/
def identSpatialAlphabet : SpatialAlphabet IdentLetter where
  fib := IdentLetter.fiber
  sp := identLetterSpatial
  proj := by
    intro x
    cases x with
    | xi =>
      have h := sourceSpatial_proj 0
      rw [sourceLetter_xi] at h
      exact h
    | mono l =>
      have h := sourceSpatial_proj (monoLetterIndex l)
      rw [sourceLetter_mono] at h
      exact h
    | sign a ε => exact generatedFifth_sign_fiber_projection a ε
    | qel g => rfl
  vec := identLetterVec
  vec_actual := by
    intro x v
    cases x with
    | xi => exact sourceSpatialVec_actual 0 v
    | mono l => exact sourceSpatialVec_actual (monoLetterIndex l) v
    | sign a ε => exact signSpatialVec_actual a v
    | qel g => rfl

/-- The matrix block of a word image is the transported block. -/
theorem identWord_matrix (ls : List IdentLetter) (A : MatRep) :
    conwayMatrixAction (identWordFiber ls).val.2 (matR A.toMat) =
      matR (A.act identSpatialAlphabet ls).toMat :=
  MatRep.act_actual identSpatialAlphabet ls A

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
