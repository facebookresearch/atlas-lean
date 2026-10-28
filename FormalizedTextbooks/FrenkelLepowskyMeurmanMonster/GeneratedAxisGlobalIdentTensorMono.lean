/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiOp

/-! # Packed monomial tensor letters

Packed implementations of the four single-letter rational monomial tensor operators
`generatedAxisGlobalRationalTensorMonomial [l]` (source permutation letters and inverses).
The label pullback is linear; it is realized by a transvection list checked on the twelve
basis labels, and extended by linearity.  The quadratic phase is a bitset checked against a
cheap bit formula proved equal to `monsterMonomialQuadratic`. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative

/-! ## Linear label maps -/

/-- The exclusive or of `g j` over the set bits `j < n` of `k`. -/
def linFold (g : ℕ → ℕ) (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => linFold g k n ^^^ (if k.testBit n then g n else 0)

/-- An exclusive-or-linear map is determined by the images of powers of two. -/
theorem eq_linFold (f : ℕ → ℕ) (hf : ∀ x y, f (x ^^^ y) = f x ^^^ f y) (k : ℕ) :
    ∀ n, f (k % 2 ^ n) = linFold (fun j => f (2 ^ j)) k n := by
  have h0 : f 0 = 0 := by
    have h := hf 0 0
    rw [Nat.xor_self, Nat.xor_self] at h
    exact h
  intro n
  induction n with
  | zero => simp [linFold, Nat.mod_one, h0]
  | succ n ih =>
    rw [mod_two_pow_succ_xor, hf, linFold, ih, Nat.xor_comm]
    split_ifs <;> simp [h0]

/-- A transvection index map is exclusive-or-linear. -/
theorem tvIdx_xor (c j x y : ℕ) : tvIdx c j (x ^^^ y) = tvIdx c j x ^^^ tvIdx c j y := by
  apply Nat.eq_of_testBit_eq
  intro b
  unfold tvIdx
  rw [Nat.testBit_xor]
  cases hx : x.testBit c <;> cases hy : y.testBit c <;>
    simp [Nat.testBit_xor] <;> cases x.testBit b <;> cases y.testBit b <;>
    cases (2 ^ j).testBit b <;> rfl

/-- All operations of a list are transvections. -/
def allTransB : List IdxOp → Bool
  | [] => true
  | .trans _ _ :: os => allTransB os
  | .flip _ :: _ => false

/-- A list of transvections has an exclusive-or-linear index map. -/
theorem idxOps_xor : ∀ (os : List IdxOp), allTransB os = true → ∀ x y,
    idxOps os (x ^^^ y) = idxOps os x ^^^ idxOps os y
  | [], _, x, y => rfl
  | .trans c j :: os, h, x, y => by
    simp only [idxOps, IdxOp.idx]
    rw [idxOps_xor os h x y, tvIdx_xor]
  | .flip _ :: _, h, _, _ => by simp [allTransB] at h

/-- Validity of index operations is decidable. -/
instance idxOpValidDecidable (K : ℕ) : DecidablePred (IdxOp.Valid K) := fun o =>
  match o with
  | .flip k => inferInstanceAs (Decidable (k < K))
  | .trans c j => inferInstanceAs (Decidable (c < K ∧ j < K ∧ c ≠ j))

/-! ## Data -/

/-- The four single monomial letters. -/
def monoLetter : Fin 4 → Fin 2 × Bool := ![(0, false), (0, true), (1, false), (1, true)]

/-- The images of the basis labels under the label pullback of a monomial letter. -/
def monoImg (l : Fin 2 × Bool) (j : ℕ) : ℕ :=
  if h : j < 12 then
    (omegaOrbitPermCodeImages (if l.2 then Fin.castAdd 2 l.1 else Fin.natAdd 2 l.1)
      ⟨j, h⟩).val
  else 0

/-- Transvection decompositions of the four monomial label pullbacks. -/
def monoOps : Fin 4 → List IdxOp := ![
[.trans 0 1, .trans 0 2, .trans 0 3, .trans 0 8, .trans 0 10, .trans 0 11, .trans 1 2,
      .trans 1 3, .trans 1 8, .trans 9 2, .trans 2 9, .trans 2 11, .trans 8 3, .trans 3 2,
      .trans 3 8, .trans 4 0, .trans 4 3, .trans 4 5, .trans 4 9, .trans 4 11, .trans 5 0,
      .trans 5 8, .trans 7 6, .trans 6 0, .trans 6 1, .trans 6 2, .trans 6 7, .trans 6 9,
      .trans 6 11, .trans 7 0, .trans 7 1, .trans 7 2, .trans 7 3, .trans 7 8, .trans 9 8,
      .trans 8 3, .trans 8 9, .trans 9 3, .trans 9 8, .trans 9 11, .trans 10 1, .trans 10 2,
      .trans 10 3, .trans 10 4, .trans 10 5, .trans 10 6, .trans 10 7, .trans 10 8,
      .trans 10 9],
    [.trans 0 2, .trans 0 3, .trans 0 4, .trans 0 5, .trans 0 6, .trans 0 7, .trans 0 8,
      .trans 0 9, .trans 0 10, .trans 0 11, .trans 1 2, .trans 1 3, .trans 1 8, .trans 1 9,
      .trans 2 3, .trans 2 8, .trans 2 11, .trans 8 3, .trans 3 2, .trans 3 8, .trans 3 9,
      .trans 4 2, .trans 4 3, .trans 4 5, .trans 5 0, .trans 5 3, .trans 5 4, .trans 5 6,
      .trans 5 7, .trans 5 10, .trans 5 11, .trans 6 2, .trans 6 3, .trans 6 7, .trans 7 0,
      .trans 7 1, .trans 7 3, .trans 7 4, .trans 7 10, .trans 7 11, .trans 9 8, .trans 8 3,
      .trans 8 9, .trans 8 11, .trans 9 2, .trans 9 3, .trans 9 8, .trans 9 11, .trans 10 1,
      .trans 10 4, .trans 10 6],
    [.trans 2 0, .trans 0 2, .trans 0 3, .trans 0 5, .trans 0 7, .trans 0 9, .trans 4 1,
      .trans 1 0, .trans 1 4, .trans 1 6, .trans 1 8, .trans 3 2, .trans 2 0, .trans 2 3,
      .trans 2 5, .trans 2 7, .trans 2 9, .trans 2 10, .trans 5 3, .trans 3 0, .trans 3 2,
      .trans 3 5, .trans 3 7, .trans 3 9, .trans 6 4, .trans 4 0, .trans 4 1, .trans 4 6,
      .trans 4 8, .trans 8 5, .trans 5 0, .trans 5 1, .trans 5 4, .trans 5 8, .trans 7 6,
      .trans 6 0, .trans 6 2, .trans 6 3, .trans 6 7, .trans 6 9, .trans 9 7, .trans 7 0,
      .trans 7 2, .trans 7 3, .trans 7 6, .trans 7 9, .trans 8 1, .trans 8 4, .trans 8 6,
      .trans 8 9, .trans 9 0, .trans 9 7, .trans 9 8],
    [.trans 2 0, .trans 0 2, .trans 0 3, .trans 0 5, .trans 0 7, .trans 0 9, .trans 4 1,
      .trans 1 0, .trans 1 4, .trans 1 6, .trans 1 8, .trans 3 2, .trans 2 0, .trans 2 3,
      .trans 2 5, .trans 2 7, .trans 2 9, .trans 2 10, .trans 5 3, .trans 3 0, .trans 3 2,
      .trans 3 5, .trans 3 7, .trans 3 9, .trans 6 4, .trans 4 0, .trans 4 1, .trans 4 6,
      .trans 4 8, .trans 8 5, .trans 5 0, .trans 5 1, .trans 5 4, .trans 5 8, .trans 7 6,
      .trans 6 0, .trans 6 2, .trans 6 3, .trans 6 7, .trans 6 9, .trans 9 7, .trans 7 0,
      .trans 7 2, .trans 7 3, .trans 7 6, .trans 7 9, .trans 8 1, .trans 8 4, .trans 8 6,
      .trans 8 9, .trans 9 0, .trans 9 7, .trans 9 8]]

/-- The source column of each output column, for the four monomial letters. -/
def monoCols : Fin 4 → List ℕ := ![
[13, 22, 19, 1, 5, 7, 6, 8, 9, 10, 11, 4, 12, 20, 16, 0, 3, 21, 15, 18, 2, 14, 17, 23],
    [15, 3, 20, 16, 11, 4, 6, 5, 7, 8, 9, 10, 12, 0, 21, 18, 14, 22, 19, 2, 13, 17, 1, 23],
    [0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 20, 17, 18, 19, 16, 21, 23, 22],
    [0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15, 20, 17, 18, 19, 16, 21, 23, 22]]


/-- The relabeling lists consist of valid transvections. -/
theorem monoOps_valid : ∀ l : Fin 4, ∀ o ∈ monoOps l, o.Valid 12 := by
  decide +kernel

/-- The relabeling lists consist of transvections only. -/
theorem monoOps_allTrans : ∀ l : Fin 4, allTransB (monoOps l) = true := by
  decide +kernel

/-- The relabeling lists send each basis label to the pullback image. -/
theorem monoOps_basis : ∀ (l : Fin 4) (j : Fin 12),
    idxOps (monoOps l) (2 ^ j.val) = monoImg (monoLetter l) j.val := by
  decide +kernel

/-! ## The label pullback -/

/-- The spin index with bits given by a natural number. -/
def lab (x : ℕ) : SpinIndex := fun i => if x.testBit i.val then 1 else 0

/-- Spin indices of exclusive ors add. -/
theorem lab_xor (x y : ℕ) : lab (x ^^^ y) = lab x + lab y := by
  funext i
  simp only [lab, Pi.add_apply, Nat.testBit_xor]
  cases x.testBit i.val <;> cases y.testBit i.val <;> decide

/-- The spin index of a linear fold is the corresponding sum. -/
theorem lab_linFold (g : ℕ → ℕ) (k : ℕ) : ∀ n,
    lab (linFold g k n) = ∑ j ∈ Finset.range n, (if k.testBit j then lab (g j) else 0) := by
  intro n
  induction n with
  | zero =>
    funext i
    simp [linFold, lab]
  | succ n ih =>
    rw [linFold, lab_xor, ih, Finset.sum_range_succ]
    split_ifs
    · rfl
    · funext i
      simp [lab]

/-- A linear fold of twelve-bit images stays below `4096`. -/
theorem linFold_lt (g : ℕ → ℕ) (hg : ∀ j, g j < 4096) (k : ℕ) : ∀ n, linFold g k n < 4096 := by
  intro n
  induction n with
  | zero => simp [linFold]
  | succ n ih =>
    rw [linFold]
    split_ifs
    · exact Nat.xor_lt_two_pow (n := 12) ih (hg n)
    · simpa using ih

/-- The basis images of a monomial letter are twelve-bit labels. -/
theorem monoImg_lt (l : Fin 2 × Bool) (j : ℕ) : monoImg l j < 4096 := by
  unfold monoImg
  by_cases h : j < 12 <;> simp [h]

/-- `lab` agrees with the Golay label coefficients. -/
theorem lab_eq_coeff (k : Fin 4096) : lab k.val = golayLabelCoefficients k := rfl

/-- The label pullback of a monomial letter is the linear fold of its basis images. -/
theorem mono_pull_coeff (l : Fin 2 × Bool) (k : Fin 4096) :
  generatedFourthMonomialPullLetter l (golayLabelCoefficients k) =
    golayLabelCoefficients ⟨linFold (monoImg l) k.val 12,
      linFold_lt (monoImg l) (monoImg_lt l) k.val 12⟩ := by
  funext i
  have hp : generatedFourthMonomialPullLetter l (golayLabelCoefficients k) i =
      ∑ j : Fin 12, golayLabelCoefficients
        (omegaOrbitPermCodeImages (if l.2 then Fin.castAdd 2 l.1 else Fin.natAdd 2 l.1) j) i *
          golayLabelCoefficients k j := by
    rcases l with ⟨l1, l2⟩
    cases l2 <;> rfl
  rw [hp]
  change _ = lab (linFold (monoImg l) k.val 12) i
  rw [lab_linFold, Finset.sum_apply, ← Fin.sum_univ_eq_sum_range
    (fun j => (if k.val.testBit j then lab (monoImg l j) else 0) i) 12]
  apply Finset.sum_congr rfl
  intro j _
  simp only [monoImg, j.isLt, dite_true, golayLabelCoefficients]
  unfold lab
  split_ifs <;> simp_all

/-- The label of the pullback of a monomial letter. -/
theorem mono_pull_label (l : Fin 2 × Bool) (k : Fin 4096) :
    (generatedAxisGlobalSpinLabel (generatedFourthMonomialPullLetter l
      (golayLabelCoefficients k))).val = linFold (monoImg l) k.val 12 := by
  rw [mono_pull_coeff, generatedAxisGlobalSpinLabel_coeff]

/-- The relabeling list of a monomial letter realizes its label pullback. -/
theorem monoOps_idx (l : Fin 4) (k : Fin 4096) :
    idxOps (monoOps l) k.val = linFold (monoImg (monoLetter l)) k.val 12 := by
  have h := eq_linFold (idxOps (monoOps l)) (idxOps_xor _ (monoOps_allTrans l)) k.val 12
  rw [Nat.mod_eq_of_lt (by simp [k.isLt])] at h
  rw [h]
  have hcongr : ∀ n, n ≤ 12 → linFold (fun j => idxOps (monoOps l) (2 ^ j)) k.val n =
      linFold (monoImg (monoLetter l)) k.val n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [linFold, linFold, ih (by omega)]
      have := monoOps_basis l ⟨n, by omega⟩
      simp only at this
      rw [this]
  exact hcongr 12 le_rfl

/-! ## The quadratic phase -/

/-- The Boolean exclusive-or fold of `f 0, ..., f (n-1)`. -/
def xorFold (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => xorFold f n ^^ f n

/-- A sum of Boolean indicators in `ZMod 2` is the exclusive-or fold. -/
theorem xorFold_sum (f : ℕ → Bool) : ∀ n,
    (∑ i ∈ Finset.range n, (if f i then (1 : ZMod 2) else 0)) = if xorFold f n then 1 else 0 := by
  intro n
  induction n with
  | zero => simp [xorFold]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, xorFold]
    cases xorFold f n <;> cases f n <;> decide

/-- A cheap quadratic form given by twelve row masks. -/
def quadBits (rows : ℕ → ℕ) (a : ℕ) : Bool :=
  xorFold (fun i => a.testBit i && bpar (a &&& rows i) 12) 12

/-- The Parker phase rows of a source permutation, as a function of the row index. -/
def monoRows (k : Fin 2) (i : ℕ) : ℕ :=
  if h : i < 12 then monsterSourcePermutationPhaseRows k ⟨i, h⟩ else 0

/-- The phase rows are twelve-bit masks. -/
theorem monoRows_lt : ∀ (k : Fin 2) (i : Fin 12), monoRows k i.val < 4096 := by
  decide +kernel

/-- The Parker quadratic phase in cheap form. -/
theorem monomialQuadratic_coeff (kk : Fin 2) (a : Fin 4096) :
    monsterMonomialQuadratic (monsterSourcePermutationPhaseData kk) (golayLabelCoefficients a) =
      if quadBits (monoRows kk) a.val then 1 else 0 := by
  rw [quadBits, ← xorFold_sum, monsterMonomialQuadratic, ← Fin.sum_univ_eq_sum_range
    (fun i => if (a.val.testBit i && bpar (a.val &&& monoRows kk i) 12) then (1 : ZMod 2)
      else 0) 12]
  apply Finset.sum_congr rfl
  intro i _
  have hrow : (fun j => monsterSourcePermutationPhaseData kk i j) =
      golayLabelCoefficients ⟨monoRows kk i.val, monoRows_lt kk i⟩ := by
    funext j
    simp [monsterSourcePermutationPhaseData, golayBooleanCast, golayLabelCoefficients, monoRows,
      i.isLt]
  have hdot := spinDot_coeff ⟨monoRows kk i.val, monoRows_lt kk i⟩ a
  rw [← hrow, spinDot] at hdot
  have hsplit : (∑ j : Fin 12, golayLabelCoefficients a i * golayLabelCoefficients a j *
      monsterSourcePermutationPhaseData kk i j) = golayLabelCoefficients a i *
        ∑ j : Fin 12, monsterSourcePermutationPhaseData kk i j * golayLabelCoefficients a j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit, hdot]
  simp only [golayLabelCoefficients, Bool.and_eq_true]
  by_cases h1 : a.val.testBit i.val <;> by_cases h2 : bpar (a.val &&& monoRows kk i.val) 12 <;>
    simp [h1, h2]

/-- The field mask of a cheap quadratic form: exclusive or of bit masks times linear masks. -/
def qmaskAux (w : ℕ) (rows : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => qmaskAux w rows n ^^^ (bmask w 12 n &&& linMask w 12 (rows n) false 12)

/-- The cheap quadratic form truncated to the first `n` rows. -/
def quadBitsAux (rows : ℕ → ℕ) (a : ℕ) (n : ℕ) : Bool :=
  xorFold (fun i => a.testBit i && bpar (a &&& rows i) 12) n

/-- The quadratic mask is the field mask of the cheap quadratic form. -/
theorem qmaskAux_isFieldMask (w : ℕ) (rows : ℕ → ℕ) : ∀ n, n ≤ 12 →
    IsFieldMask w (2 ^ 12) (qmaskAux w rows n) (fun t => quadBitsAux rows t n = true) := by
  intro n
  induction n with
  | zero =>
    intro _
    exact (zero_isFieldMask w _).congr (fun t _ => by simp [quadBitsAux, xorFold])
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := isFieldMask_and (bmask_isFieldMask w 12 n (by omega))
      (linMask_isFieldMask w 12 (rows n) false 12 le_rfl)
    refine (isFieldMask_xor h1 h2).congr (fun t _ => ?_)
    simp only [quadBitsAux, xorFold, Bool.false_xor]
    cases xorFold (fun i => t.testBit i && bpar (t &&& rows i) 12) n <;>
      cases t.testBit n <;> cases bpar (t &&& rows n) 12 <;> simp

/-- The phase mask of a monomial letter. -/
def monoPhaseMask (w : ℕ) (l : Fin 4) : ℕ :=
  if (monoLetter l).2 then qmaskAux w (monoRows (monoLetter l).1) 12
  else actOps w 12 (monoOps (if (monoLetter l).1 = 0 then 0 else 2))
    (qmaskAux w (monoRows (monoLetter l).1) 12)

/-- A repeated block fits in its total length. -/
theorem rep_lt (B s : ℕ) (hB : B < 2 ^ s) (c : ℕ) : rep B s c < 2 ^ (s * c) := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  rw [testBit_rep B s hB c b]
  simp [show ¬ b < s * c by omega]

/-- Bit masks of `2^12` fields fit in `4096` fields. -/
theorem bmask_lt (w k : ℕ) (hk : k < 12) : bmask w 12 k < 2 ^ (w * 2 ^ 12) := by
  have h := rep_lt _ _ (bmask_block_lt w k) (2 ^ (12 - (k + 1)))
  have e : w * 2 ^ (k + 1) * 2 ^ (12 - (k + 1)) = w * 2 ^ 12 := by
    rw [Nat.mul_assoc, ← pow_add]
    congr 2
    omega
  rw [e] at h
  exact h

/-- Linear masks fit in `4096` fields. -/
theorem linMask_lt (w m : ℕ) (c : Bool) : ∀ j, j ≤ 12 → linMask w 12 m c j < 2 ^ (w * 2 ^ 12) := by
  intro j
  induction j with
  | zero =>
    intro _
    cases c
    · simp [linMask]
    · simp only [linMask, ite_true, allMask]
      exact Nat.sub_lt (by positivity) one_pos
  | succ j ih =>
    intro hj
    rw [linMask]
    apply Nat.xor_lt_two_pow (ih (by omega))
    split_ifs
    · exact bmask_lt w j (by omega)
    · positivity

/-- The quadratic mask fits in `4096` fields. -/
theorem qmaskAux_lt (w : ℕ) (rows : ℕ → ℕ) : ∀ n, qmaskAux w rows n < 2 ^ (w * 2 ^ 12) := by
  intro n
  induction n with
  | zero => simp [qmaskAux]
  | succ n ih =>
    rw [qmaskAux]
    exact Nat.xor_lt_two_pow ih (Nat.and_lt_two_pow _ (linMask_lt w _ false 12 le_rfl))

/-- The Parker phase of a monomial letter at a natural spin label (zero outside the range). -/
def monoPhaseAt (l : Fin 4) (k : ℕ) : ZMod 2 :=
  if h : k < 4096 then
    generatedFourthMonomialPullPhase (monoLetter l) (golayLabelCoefficients ⟨k, h⟩)
  else 0

/-- The Parker quadratic phase equals one exactly where the cheap quadratic form is true. -/
theorem monomialQuadratic_eq_one (kk : Fin 2) (a : Fin 4096) :
    monsterMonomialQuadratic (monsterSourcePermutationPhaseData kk) (golayLabelCoefficients a) = 1
      ↔ quadBitsAux (monoRows kk) a.val 12 = true := by
  rw [monomialQuadratic_coeff]
  change (if quadBitsAux (monoRows kk) a.val 12 = true then (1 : ZMod 2) else 0) = 1 ↔ _
  by_cases hb : quadBitsAux (monoRows kk) a.val 12 = true
  · simp [hb]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, iff_false]
    decide

/-- Phase masks of letters with an inverse pullback (letters 0 and 2). -/
theorem monoPhaseMask_isFieldMask_inv (w : ℕ) (l : Fin 4) (hl : (monoLetter l).2 = false)
    (hself : monoLetter (if (monoLetter l).1 = 0 then 0 else 2) = monoLetter l) :
    IsFieldMask w (2 ^ 12) (monoPhaseMask w l) (fun k => monoPhaseAt l k = 1) := by
  have hq := qmaskAux_isFieldMask w (monoRows (monoLetter l).1) 12 le_rfl
  set l' : Fin 4 := if (monoLetter l).1 = 0 then 0 else 2 with hl'
  have hr := isFieldMask_actOps (monoOps l') (monoOps_valid l') (qmaskAux_lt w _ 12) hq
  have hm : monoPhaseMask w l =
      actOps w 12 (monoOps l') (qmaskAux w (monoRows (monoLetter l).1) 12) := by
    simp only [monoPhaseMask, hl, Bool.false_eq_true, ↓reduceIte, hl']
  rw [hm]
  refine hr.congr (fun k hk => ?_)
  have hk' : k < 4096 := by simpa using hk
  simp only [monoPhaseAt, hk', dite_true]
  rw [monoOps_idx l' ⟨k, hk'⟩, hself, generatedFourthMonomialPullPhase]
  simp only [hl, Bool.false_eq_true, ↓reduceIte]
  have hs : (monsterSourcePermutationCode (monoLetter l).1).symm
      (golayLabelCoefficients ⟨k, hk'⟩) =
      generatedFourthMonomialPullLetter (monoLetter l) (golayLabelCoefficients ⟨k, hk'⟩) := by
    rw [generatedFourthMonomialPullLetter, hl]
    rfl
  rw [hs, mono_pull_coeff, monomialQuadratic_eq_one]

/-- Phase masks of letters with a direct pullback (letters 1 and 3). -/
theorem monoPhaseMask_isFieldMask_dir (w : ℕ) (l : Fin 4) (hl : (monoLetter l).2 = true) :
    IsFieldMask w (2 ^ 12) (monoPhaseMask w l) (fun k => monoPhaseAt l k = 1) := by
  have hq := qmaskAux_isFieldMask w (monoRows (monoLetter l).1) 12 le_rfl
  have hm : monoPhaseMask w l = qmaskAux w (monoRows (monoLetter l).1) 12 := by
    simp only [monoPhaseMask, hl, ↓reduceIte]
  rw [hm]
  refine hq.congr (fun k hk => ?_)
  have hk' : k < 4096 := by simpa using hk
  simp only [monoPhaseAt, hk', dite_true, generatedFourthMonomialPullPhase, hl, ↓reduceIte]
  rw [monomialQuadratic_eq_one]

/-- The phase mask is the field mask of the Parker phase. -/
theorem monoPhaseMask_isFieldMask (w : ℕ) (l : Fin 4) :
    IsFieldMask w (2 ^ 12) (monoPhaseMask w l) (fun k => monoPhaseAt l k = 1) := by
  fin_cases l
  · exact monoPhaseMask_isFieldMask_inv w 0 rfl rfl
  · exact monoPhaseMask_isFieldMask_dir w 1 rfl
  · exact monoPhaseMask_isFieldMask_inv w 2 rfl rfl
  · exact monoPhaseMask_isFieldMask_dir w 3 rfl

/-! ## The packed monomial letter -/

/-- The column permutation data are the actual Golay coordinate permutations. -/
theorem monoCols_spec : ∀ (l : Fin 4) (i : Fin 24),
    (monoCols l).getD i.val 0 =
      ((generatedFourthMonomialPermutationLetter (monoLetter l)).val.symm i).val := by
  decide +kernel

/-- The packed monomial action on one column: relabel, then the phase signs. -/
def colMono (w : ℕ) (l : Fin 4) (x : SVec) : SVec :=
  sflip (allMask w (2 ^ 12)) (monoPhaseMask w l) (sops w 12 (monoOps l) x)

/-- The packed monomial tensor letter. -/
def tensorMono (w : ℕ) (l : Fin 4) (X : List SVec) : List SVec :=
  (List.range 24).map (fun i => colMono w l (tcol X ((monoCols l).getD i 0)))

/-- The packed monomial column action: bounds and values. -/
theorem colMono_spec {w B : ℕ} (l : Fin 4) {x : SVec} (hx : SBnd w (2 ^ 12) B x)
    (hB : B < 2 ^ w) :
    SBnd w (2 ^ 12) B (colMono w l x) ∧ ∀ k : Fin 4096,
      sval w (colMono w l x) k.val =
        (if monoPhaseAt l k.val = 1 then -1 else 1) *
          sval w x (linFold (monoImg (monoLetter l)) k.val 12) := by
  obtain ⟨s1, s2⟩ := sops_spec (monoOps l) (monoOps_valid l) hx
  obtain ⟨s3, s4⟩ := sflip_spec s1 _ _ (monoPhaseMask_isFieldMask w l) hB
  refine ⟨s3, fun k => ?_⟩
  unfold colMono
  rw [s4 k.val k.isLt, (s2 k.val k.isLt).2, monoOps_idx]
  split_ifs <;> ring

/-- The packed monomial tensor letter: bounds and the exact rational monomial formula. -/
theorem tensorMono_spec {w B : ℕ} (l : Fin 4) {X : List SVec} (hX : TBnd w B X)
    (hB : B < 2 ^ w) (D : ℚ) :
    TBnd w B (tensorMono w l X) ∧
      tensorRat w (tensorMono w l X) D =
        generatedAxisGlobalRationalTensorMonomial [monoLetter l] (tensorRat w X D) := by
  have hsrc : ∀ i < 24, (monoCols l).getD i 0 < 24 := by
    intro i hi
    have := monoCols_spec l ⟨i, hi⟩
    simp only at this
    rw [this]
    exact Fin.isLt _
  have hcol : ∀ i < 24, tcol (tensorMono w l X) i = colMono w l (tcol X ((monoCols l).getD i 0)) :=
    fun i hi => tcol_range_map _ 24 i hi
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hcol i hi]
    exact (colMono_spec l (hX _ (hsrc i hi)) hB).1
  · funext k i
    simp only [tensorRat, generatedAxisGlobalRationalTensorMonomial,
      generatedFourthMonomialWordPull,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, add_zero]
    rw [hcol i.val i.isLt, (colMono_spec l (hX _ (hsrc i.val i.isLt)) hB).2 k,
      monoCols_spec l i]
    have hph : monoPhaseAt l k.val =
        generatedFourthMonomialPullPhase (monoLetter l) (golayLabelCoefficients k) := by
      simp [monoPhaseAt, k.isLt]
    rw [hph]
    have hlab := mono_pull_label (monoLetter l) k
    have hl : generatedAxisGlobalSpinLabel (generatedFourthMonomialPullLetter (monoLetter l)
        (golayLabelCoefficients k)) = ⟨linFold (monoImg (monoLetter l)) k.val 12,
          linFold_lt _ (monoImg_lt _) k.val 12⟩ := Fin.ext hlab
    rw [hl]
    simp only [generatedAxisGlobalIntSign]
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide)
      (generatedFourthMonomialPullPhase (monoLetter l) (golayLabelCoefficients k)) with hc | hc
    · simp only [hc, zero_ne_one, ↓reduceIte, one_mul, Int.cast_one]
    · simp only [hc, ↓reduceIte, one_ne_zero, neg_mul, one_mul, Int.cast_neg, Int.cast_one]
      ring

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
