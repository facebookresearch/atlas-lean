/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFastParity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortProductCovariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.QCoordinateGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechQuadratic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness

/-! # Extraspecial mask data of local words

Generic infrastructure for the cheap whole-vector identification method (worker `gident2`).
An automorphism of `Q` is evaluated on signed binary masks `(m, b)`, standing for
`qCentral b * generatedAxisGlobalQMask m`, by binary columns, triangular correction rows and
linear central coefficients (`generatedAxisGlobalQMaskImage_actual`).  Data of a whole word of
local fiber letters is certified from the letters' data by folding the twenty-four coordinate
generators through the word and checking the computed correction rows; no per-stage cache
modules are needed.  No numerical certificate enters this module. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative

/-! ## Fast dot products and central bits -/

private theorem bool_fold_xor (bits : List Bool) (a : Bool) :
    bits.foldl Bool.xor a = Bool.xor a (bits.foldl Bool.xor false) := by
  induction bits generalizing a with
  | nil => cases a <;> rfl
  | cons b bits ih =>
    simp only [List.foldl_cons]
    rw [ih (Bool.xor a b), ih (Bool.xor false b)]
    cases a <;> cases b <;> cases bits.foldl Bool.xor false <;> rfl

private theorem mask_sum_bool (bits : List Bool) :
    monsterCo1GeometryBinaryMaskSum (bits.map (fun b => if b then 1 else 0)) =
      if bits.foldl Bool.xor false then 1 else 0 := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [List.map_cons, monsterCo1GeometryBinaryMaskSum, List.foldl_cons, ih]
    have hf : bits.foldl Bool.xor (Bool.xor false b) =
        Bool.xor b (bits.foldl Bool.xor false) := by
      rw [bool_fold_xor bits (Bool.xor false b)]
      cases b <;> rfl
    simp only [hf]
    generalize bits.foldl Bool.xor false = c
    cases b <;> cases c <;> decide +kernel

private theorem mask_sum_append (a b : List ℕ) :
    monsterCo1GeometryBinaryMaskSum (a ++ b) =
      Nat.xor (monsterCo1GeometryBinaryMaskSum a) (monsterCo1GeometryBinaryMaskSum b) := by
  induction a with
  | nil => simp only [List.nil_append, monsterCo1GeometryBinaryMaskSum, Nat.xor_eq,
      Nat.zero_xor]
  | cons c a ih =>
    simp only [List.cons_append, monsterCo1GeometryBinaryMaskSum, ih, Nat.xor_eq,
      Nat.xor_assoc]

/-- The twelve-bit dot parity, read from the certified byte and nibble parity tables. -/
def identDot12 (a b : ℕ) : ℕ :=
  if !(generatedAxisGlobalFastParityTwelve ((a &&& b) % 4096)) then 1 else 0

/-- The fast twelve-bit dot is the original finite dot. -/
theorem identDot12_eq (a b : ℕ) : identDot12 a b = monsterCo1GeometryBinaryMaskDot 12 a b := by
  have hbits : (List.ofFn (fun k : Fin 12 =>
      if a.testBit k.val then if b.testBit k.val then 1 else 0 else 0)) =
      (List.ofFn (fun k : Fin 12 => (a &&& b).testBit k.val)).map
        (fun bit => if bit then 1 else 0) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext k
    dsimp only [Function.comp_apply]
    rw [Nat.testBit_and]
    cases a.testBit k.val <;> cases b.testBit k.val <;> rfl
  unfold monsterCo1GeometryBinaryMaskDot
  rw [hbits, mask_sum_bool]
  have hp := generatedAxisGlobalFastParity_certificate
    (⟨(a &&& b) % 4096, Nat.mod_lt _ (by decide)⟩ : Fin 4096)
  have hm := generatedAxisGlobalParityTwelve_mod (a &&& b)
  have he : generatedAxisGlobalParityTwelve (a &&& b) =
      generatedAxisGlobalFastParityTwelve ((a &&& b) % 4096) := hm.trans hp
  unfold generatedAxisGlobalParityTwelve at he
  unfold identDot12
  rw [← he]
  cases (List.ofFn (fun k : Fin 12 => (a &&& b).testBit k.val)).foldl Bool.xor false <;> rfl

/-- The twenty-four-bit dot splits at coordinate twelve. -/
theorem identDot24_split (a b : ℕ) :
    monsterCo1GeometryBinaryMaskDot 24 a b =
      Nat.xor (monsterCo1GeometryBinaryMaskDot 12 a b)
        (monsterCo1GeometryBinaryMaskDot 12 (a >>> 12) (b >>> 12)) := by
  unfold monsterCo1GeometryBinaryMaskDot
  change monsterCo1GeometryBinaryMaskSum (List.ofFn (fun k : Fin (12 + 12) =>
    if a.testBit k.val then if b.testBit k.val then 1 else 0 else 0)) = _
  rw [List.ofFn_add, mask_sum_append]
  simp only [Fin.val_castLE, Fin.val_natAdd, Nat.testBit_shiftRight, Nat.add_comm]

/-- The twenty-four-bit dot parity from two table lookups. -/
def identDot24 (a b : ℕ) : ℕ :=
  if Bool.xor (generatedAxisGlobalFastParityTwelve ((a &&& b) % 4096))
      (generatedAxisGlobalFastParityTwelve (((a >>> 12) &&& (b >>> 12)) % 4096)) then 1 else 0

/-- The fast twenty-four-bit dot is the original finite dot. -/
theorem identDot24_eq (a b : ℕ) : identDot24 a b = monsterCo1GeometryBinaryMaskDot 24 a b := by
  rw [identDot24_split, ← identDot12_eq, ← identDot12_eq]
  unfold identDot24 identDot12
  cases generatedAxisGlobalFastParityTwelve ((a &&& b) % 4096) <;>
    cases generatedAxisGlobalFastParityTwelve (((a >>> 12) &&& (b >>> 12)) % 4096) <;>
      decide +kernel

/-- The central value of mask data on a mask, with fast dot products. -/
def identQCentral (rows : Fin 24 → ℕ) (coeff v : ℕ) : ℕ :=
  Nat.xor (monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 =>
    if v.testBit i.val then identDot24 (rows i) v else 0))) (identDot24 coeff v)

/-- The fast central value is the original central value. -/
theorem identQCentral_eq (rows : Fin 24 → ℕ) (coeff v : ℕ) :
    identQCentral rows coeff v = generatedAxisGlobalQMaskCentral rows coeff v := by
  unfold identQCentral generatedAxisGlobalQMaskCentral generatedAxisGlobalQMaskPhase
  simp_rw [identDot24_eq]

/-! ## Correction rows -/

/-- The hyperbolic cocycle bit `β(u, v) = Σ_{k<12} u_k v_{12+k}` of two binary masks. -/
def qBetaBit (u v : ℕ) : Bool := (monsterCo1GeometryBinaryMaskDot 12 u (v >>> 12)).testBit 0

/-- The cocycle bit is the original cocycle of the decoded vectors. -/
theorem qBetaBit_spec (u v : ℕ) :
    golayBooleanCast (qBetaBit u v) =
      qBeta (monsterCo1GeometryBinaryMaskDecode u) (monsterCo1GeometryBinaryMaskDecode v) := by
  unfold qBetaBit golayBooleanCast
  rw [monsterCo1GeometryBinaryMaskDot_decode]
  unfold qBeta
  apply Finset.sum_congr rfl
  intro k _
  simp only [monsterCo1GeometryBinaryMaskDecode, Nat.testBit_shiftRight, Fin.val_castAdd,
    Fin.val_natAdd]

/-- The cocycle of two coordinate units. -/
theorem qBeta_single_single : ∀ i j : Fin 24,
    qBeta (Pi.single i 1) (Pi.single j 1) = golayBooleanCast (i.val + 12 == j.val) := by
  decide +kernel

/-- Boolean casts turn exclusive or into addition. -/
theorem golayBooleanCast_xor_eq (a b : Bool) :
    golayBooleanCast (xor a b) = golayBooleanCast a + golayBooleanCast b := by
  cases a <;> cases b <;> decide

/-- The correction row of binary columns: bit `j > i` is `β(c_i, c_j) + β(e_i, e_j)`. -/
def rowsOf (cols : Fin 24 → ℕ) (i : Fin 24) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun j : Fin 24 =>
    if i < j ∧ xor (qBetaBit (cols i) (cols j)) (i.val + 12 == j.val) = true then 2 ^ j.val
    else 0))

/-- Every computed correction row is the original cocycle difference of the columns. -/
theorem rowsOf_spec (cols : Fin 24 → ℕ) (i j : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (rowsOf cols i) j =
      if i < j then
        qBeta (monsterCo1GeometryBinaryMaskDecode (cols i))
          (monsterCo1GeometryBinaryMaskDecode (cols j)) +
        qBeta (Pi.single i 1) (Pi.single j 1)
      else 0 := by
  unfold rowsOf
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn, Finset.sum_apply]
  have h (k : Fin 24) : (monsterCo1GeometryBinaryMaskDecode ∘ fun j : Fin 24 =>
      if i < j ∧ xor (qBetaBit (cols i) (cols j)) (i.val + 12 == j.val) = true then 2 ^ j.val
      else 0) k j =
      if k = j then
        (if i < j ∧ xor (qBetaBit (cols i) (cols j)) (i.val + 12 == j.val) = true then 1 else 0)
      else 0 := by
    simp only [Function.comp_apply]
    split_ifs with h1 h2 h3 <;>
      simp_all [monsterCo1GeometryBinaryMaskDecode_zero, co1NonsplitMask_unit]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [qBeta_single_single, ← qBetaBit_spec]
  by_cases hij : i < j
  · simp only [hij, true_and, ↓reduceIte]
    rw [← golayBooleanCast_xor_eq]
    cases xor (qBetaBit (cols i) (cols j)) (i.val + 12 == j.val) <;> rfl
  · simp [hij]

/-! ## Bit masks of boolean families -/

/-- The mask with bit `i` equal to `bits i`, for `i < 24`. -/
def maskOfBits (bits : Fin 24 → Bool) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 => if bits i then 2 ^ i.val else 0))

/-- Decoding a mask of booleans recovers their casts. -/
theorem decode_maskOfBits (bits : Fin 24 → Bool) :
    monsterCo1GeometryBinaryMaskDecode (maskOfBits bits) = fun i => golayBooleanCast (bits i) := by
  funext j
  unfold maskOfBits
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn, Finset.sum_apply]
  have h (k : Fin 24) : (monsterCo1GeometryBinaryMaskDecode ∘ fun i : Fin 24 =>
      if bits i then 2 ^ i.val else 0) k j = if k = j then golayBooleanCast (bits j) else 0 := by
    simp only [Function.comp_apply]
    by_cases hk : k = j
    · subst hk
      cases bits k <;> simp [monsterCo1GeometryBinaryMaskDecode_zero, co1NonsplitMask_unit,
        golayBooleanCast]
    · cases bits k <;> simp [hk, monsterCo1GeometryBinaryMaskDecode_zero, co1NonsplitMask_unit]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- The bits of a mask of booleans. -/
theorem testBit_maskOfBits (bits : Fin 24 → Bool) (i : Fin 24) :
    (maskOfBits bits).testBit i.val = bits i := by
  have h := congrFun (decode_maskOfBits bits) i
  simp only [monsterCo1GeometryBinaryMaskDecode, golayBooleanCast] at h
  cases h1 : (maskOfBits bits).testBit i.val <;> cases h2 : bits i <;> simp_all

/-! ## Signed masks and mask data -/

/-- The extraspecial element with central bit `p.2` and binary mask `p.1`. -/
def qmElt (p : ℕ × Bool) : Q := qCentral (golayBooleanCast p.2) * generatedAxisGlobalQMask p.1

/-- The binary base of a signed mask. -/
theorem qmElt_base (p : ℕ × Bool) :
    toAdd (qmElt p).base = monsterCo1GeometryBinaryMaskDecode p.1 := by
  unfold qmElt
  rw [qCentral_mul_base]
  rfl

/-- The central coefficient of a signed mask. -/
theorem qmElt_coeff (p : ℕ × Bool) : toAdd (qmElt p).coeff = golayBooleanCast p.2 := by
  unfold qmElt
  rw [qCentral_mul_coeff]
  change golayBooleanCast p.2 + 0 = _
  rw [add_zero]

/-- Coordinate generators are unsigned unit masks. -/
theorem qmElt_unit (i : Fin 24) : qmElt (2 ^ i.val, false) = qCoordinateGenerator i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    rw [qmElt_base]
    exact co1NonsplitMask_unit i
  · apply toAdd.injective
    rw [qmElt_coeff]
    rfl

/-- Unsigned masks are the positive mask lifts. -/
theorem qmElt_false (m : ℕ) : qmElt (m, false) = generatedAxisGlobalQMask m := by
  unfold qmElt
  rw [show golayBooleanCast false = 0 from rfl]
  apply NormalizedCocycleExtension.Extension.ext
  · exact qCentral_mul_base _ _
  · apply toAdd.injective
    rw [qCentral_mul_coeff, zero_add]

/-- The signed mask of an arbitrary extraspecial element. -/
def qmEncode (q : Q) : ℕ × Bool :=
  (maskOfBits (fun i => toAdd q.base i == 1), toAdd q.coeff == 1)

/-- Casting the test `c == 1` returns `c`. -/
theorem golayBooleanCast_beq_one (c : ZMod 2) : golayBooleanCast (c == 1) = c := by
  fin_cases c <;> rfl

/-- Every extraspecial element is the signed mask of its encoding. -/
theorem qmElt_encode (q : Q) : qmElt (qmEncode q) = q := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    rw [qmElt_base]
    unfold qmEncode
    rw [decode_maskOfBits]
    funext i
    exact golayBooleanCast_beq_one _
  · apply toAdd.injective
    rw [qmElt_coeff]
    exact golayBooleanCast_beq_one _

/-- Mask data of an extraspecial automorphism: columns, correction rows, central coefficients. -/
structure QMaskData where
  /-- Binary images of the coordinate units. -/
  cols : Fin 24 → ℕ
  /-- Triangular correction rows of the columns. -/
  rows : Fin 24 → ℕ
  /-- Central bits of the images of the coordinate units. -/
  coeff : ℕ

/-- The data evaluates the automorphism on every positive mask lift. -/
def QMaskData.Valid (d : QMaskData) (a : MulAut Q) : Prop :=
  ∀ v, a (generatedAxisGlobalQMask v) = generatedAxisGlobalQMaskImage d.cols d.rows d.coeff v

/-- One evaluation step of mask data on a signed mask. -/
def QMaskData.step (d : QMaskData) (p : ℕ × Bool) : ℕ × Bool :=
  (generatedAxisGlobalQMaskVector d.cols p.1,
    xor p.2 ((identQCentral d.rows d.coeff p.1).testBit 0))

/-- A valid data step computes the automorphism on signed masks. -/
theorem QMaskData.step_spec (d : QMaskData) (a : MulAut Q) (h : d.Valid a) (p : ℕ × Bool) :
    a (qmElt p) = qmElt (d.step p) := by
  unfold qmElt QMaskData.step
  rw [map_mul, co1NonsplitAut_central, h,
    generatedAxisGlobalQMaskImage_certificate d.cols d.rows d.coeff p.1
      (generatedAxisGlobalQMaskVector d.cols p.1)
      (golayBooleanCast ((identQCentral d.rows d.coeff p.1).testBit 0))
      rfl (by rw [identQCentral_eq]; rfl),
    ← mul_assoc, qCentral_mul, golayBooleanCast_xor_eq]

/-- Generator images and computed correction rows give valid data for a local fiber element. -/
theorem QMaskData.valid_of_generators (f : localFiberSubgroup) (d : QMaskData)
    (hgen : ∀ i : Fin 24, spinConjugation f.val.1 (qCoordinateGenerator i) =
      qmElt (d.cols i, d.coeff.testBit i.val))
    (hrows : ∀ i : Fin 24, d.rows i = rowsOf d.cols i) :
    d.Valid (spinConjugation f.val.1) := by
  let a := spinConjugation f.val.1
  have hR : ∀ v, squareQuad (qBinaryAction a v) = squareQuad v := by
    intro v
    change squareQuad (spinBinaryAction f.val.1 v) = _
    rw [f.property]
    exact leechBinaryAction_squareQuad _ v
  have hb (i : Fin 24) : qBinaryAction a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (d.cols i) := by
    have h := qBinaryAction_apply a (qCoordinateGenerator i)
    change qBinaryAction a (Pi.single i 1) = toAdd (a (qCoordinateGenerator i)).base at h
    rw [h]
    change toAdd (spinConjugation f.val.1 (qCoordinateGenerator i)).base = _
    rw [hgen i, qmElt_base]
  have hr : qCorrectionMatrix (qBinaryAction a) =
      monsterCo1GeometryBinaryMaskMatrix d.rows := by
    ext i j
    change (if i < j then qCocycleDifference (qBinaryAction a)
      (Pi.single i 1) (Pi.single j 1) else 0) = monsterCo1GeometryBinaryMaskDecode (d.rows i) j
    simp only [qCocycleDifference_apply, hb]
    rw [hrows i, rowsOf_spec]
  have hc (i : Fin 24) : co1NonsplitAutPhase a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode d.coeff i := by
    change toAdd (spinConjugation f.val.1 (qCoordinateGenerator i)).coeff = _
    rw [hgen i, qmElt_coeff]
    rfl
  exact generatedAxisGlobalQMaskImage_actual a hR _ _ _ hb hr hc

/-- Literal data agreeing with an exact evaluator on the generators is valid. -/
theorem QMaskData.valid_of_images (f : localFiberSubgroup) (E : Q → Q)
    (hE : ∀ q, spinConjugation f.val.1 q = E q) (d : QMaskData)
    (hcols : ∀ i : Fin 24,
      qmEncode (E (qCoordinateGenerator i)) = (d.cols i, d.coeff.testBit i.val))
    (hrows : ∀ i : Fin 24, d.rows i = rowsOf d.cols i) :
    d.Valid (spinConjugation f.val.1) := by
  apply QMaskData.valid_of_generators f d _ hrows
  intro i
  rw [hE, ← hcols i, qmElt_encode]

/-! ## Words of letters -/

/-- Evaluate a word of mask data (the head letter acts last). -/
def qmWord : List QMaskData → ℕ × Bool → ℕ × Bool
  | [], p => p
  | d :: ds, p => d.step (qmWord ds p)

/-- An alphabet of local fiber letters with valid mask data. -/
structure QMaskAlphabet (α : Type) where
  /-- The local fiber element of a letter. -/
  fib : α → localFiberSubgroup
  /-- The mask data of a letter. -/
  dat : α → QMaskData
  /-- The mask data of every letter is valid. -/
  valid : ∀ x, (dat x).Valid (spinConjugation (fib x).val.1)

/-- A word of valid letters is computed by its word of mask data. -/
theorem QMaskAlphabet.word_spec {α : Type} (A : QMaskAlphabet α) (w : List α)
    (p : ℕ × Bool) :
    spinConjugation ((w.map A.fib).prod).val.1 (qmElt p) = qmElt (qmWord (w.map A.dat) p) := by
  induction w with
  | nil =>
    change spinConjugation 1 (qmElt p) = qmElt p
    rw [map_one]
    rfl
  | cons x w ih =>
    change spinConjugation ((A.fib x).val.1 * ((w.map A.fib).prod).val.1) (qmElt p) = _
    rw [map_mul, MulAut.mul_apply, ih, (A.dat x).step_spec _ (A.valid x)]
    rfl

/-- Composite data of a word, certified by its generator images and computed correction rows. -/
theorem QMaskAlphabet.valid_word {α : Type} (A : QMaskAlphabet α) (w : List α)
    (d : QMaskData)
    (hcols : ∀ i : Fin 24, qmWord (w.map A.dat) (2 ^ i.val, false) =
      (d.cols i, d.coeff.testBit i.val))
    (hrows : ∀ i : Fin 24, d.rows i = rowsOf d.cols i) :
    d.Valid (spinConjugation ((w.map A.fib).prod).val.1) := by
  apply QMaskData.valid_of_generators _ d _ hrows
  intro i
  rw [← qmElt_unit, A.word_spec, hcols]

/-! ## Extraspecial letters -/

/-- The commutator bits of a mask with the coordinate units. -/
def qLetterBits (m : ℕ) (i : Fin 24) : Bool := xor (qBetaBit m (2 ^ i.val)) (qBetaBit (2 ^ i.val) m)

/-- Mask data of conjugation by the extraspecial element of mask `m`. -/
def qLetterData (m : ℕ) : QMaskData :=
  ⟨fun i => 2 ^ i.val, rowsOf (fun i => 2 ^ i.val), maskOfBits (qLetterBits m)⟩

/-- Conjugation by an extraspecial element has the data of its mask, for either central bit. -/
theorem qLetterData_valid (m : ℕ) (b : Bool) :
    (qLetterData m).Valid (spinConjugation (localFiberIncl (qmElt (m, b))).val.1) := by
  apply QMaskData.valid_of_generators _ _ _ (fun _ => rfl)
  intro i
  change spinConjugation (spinHolomorphIncl (qmElt (m, b))) (qCoordinateGenerator i) = _
  rw [spinConjugation_incl, q_conjugation_central_phase]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    rw [qCentral_mul_base, qmElt_base, ← qmElt_unit, qmElt_base]
    rfl
  · apply toAdd.injective
    rw [qCentral_mul_coeff, qmElt_coeff]
    change _ + toAdd (qCoordinateGenerator i).coeff = _
    rw [← qmElt_unit, qmElt_coeff, qmElt_base, qmElt_base,
      show golayBooleanCast false = 0 from rfl, add_zero]
    simp only [qLetterData, testBit_maskOfBits, qLetterBits, golayBooleanCast_xor_eq,
      qBetaBit_spec]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
