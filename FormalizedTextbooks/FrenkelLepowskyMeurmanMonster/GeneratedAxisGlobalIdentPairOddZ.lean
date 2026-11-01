/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctH

/-! # The packed pairing with integer octad and odd parts

Rational arithmetic is slow in the kernel.  `pairTriGMZ` evaluates the odd short terms of both
sides as integer sums read directly (shift and mask) from the packed tensor numerators
(`oddWZ`, `oddLZ`), and the octad terms as the integer sum `octSumZ` of the packed
Walsh-Hadamard transform, with one rational division per part.  With packed tensors it equals
`pairTriGM` (`pairTriGMZ_eq`, worker `gident`); `pairTriGMZ_parts` assembles it from separately
evaluated parts, and `ident_forward_GMZ` / `ident_inverse_GMZ` give the identifications. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators

/-! ## Integer odd terms -/

/-- The weight sign of an odd code label, as an integer. -/
def oddWS (d : ℕ) : ℤ := if identOddWeightFlag d = 0 then 1 else -1

/-- The coordinate sign of an odd code label, as an integer. -/
def oddCS (d j : ℕ) : ℤ := if (identOddCode d).testBit j then -1 else 1

theorem oddWS_cast (d : ℕ) : ((oddWS d : ℤ) : ℚ) = oddWeightSignF d := by
  unfold oddWS oddWeightSignF
  split_ifs <;> simp

theorem oddCS_cast (d j : ℕ) : ((oddCS d j : ℤ) : ℚ) = oddCoordSignF d j := by
  unfold oddCS oddCoordSignF
  split_ifs <;> simp

/-- The integer odd term of `W` against the triality image of `L` (numerators of `L`). -/
def oddWTerm (w : ℕ) (fwd : Bool) (X : List SVec) (lab : ℕ) : ℤ :=
  let d := oddD lab
  let j := oddJ lab
  let s0 := svalS w (tcol X j) d
  let s1 := svalS w (tcol X j) (d + 2048)
  if fwd then oddWS d * (s0 + s1) else oddCS d j * (s0 - s1)

/-- The integer odd-term tensor contribution (numerators of `W`). -/
def oddLTerm (w : ℕ) (fwd : Bool) (Y : List SVec) (lab : ℕ) : ℤ :=
  let d := oddD lab
  let j := oddJ lab
  let s0 := svalS w (tcol Y j) d
  let s1 := svalS w (tcol Y j) (d + 2048)
  if fwd then oddCS d j * (s0 - s1) else oddWS d * (s0 + s1)

/-- The odd short terms of `W` against the triality image of `L`, in integers. -/
def oddWZ (w : ℕ) (fwd : Bool) (X : List SVec) (W : IdentVec) : ℤ :=
  (W.sh.odd.map (fun q => q.2 * oddWTerm w fwd X q.1)).sum

/-- The odd short terms of `L` against the tensor of `W`, in integers. -/
def oddLZ (w : ℕ) (fwd : Bool) (Y : List SVec) (L : IdentVec) : ℤ :=
  (L.sh.odd.map (fun q => q.2 * oddLTerm w fwd Y q.1)).sum

theorem svalS_eq_sval (w : ℕ) (x : SVec) (i : ℕ) : svalS w x i = sval w x i := by
  simp only [svalS, sval, fldS_eq]

theorem triOddF_packed (w : ℕ) (fwd : Bool) (L : IdentVec) (X : List SVec) (D : ℚ)
    (hLt : L.ten = tensorRat w X D) (lab : ℕ) :
    triOddF fwd L lab = (oddWTerm w fwd X lab : ℚ) / (2 * D) := by
  unfold triOddF oddWTerm
  rw [hLt]
  simp only [tensorRat, svalS_eq_sval]
  cases fwd
  · simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_mul, Int.cast_sub, oddCS_cast]
    ring
  · simp only [↓reduceIte, Int.cast_mul, Int.cast_add, oddWS_cast]
    ring

theorem triTCF_packed (w : ℕ) (fwd : Bool) (W : IdentVec) (Y : List SVec) (E : ℚ)
    (hWt : W.ten = tensorRat w Y E) (lab : ℕ) :
    triTCF fwd W lab = (oddLTerm w fwd Y lab : ℚ) / E := by
  unfold triTCF oddLTerm
  rw [hWt]
  simp only [tensorRat, svalS_eq_sval]
  cases fwd
  · simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_mul, Int.cast_add, oddWS_cast]
    ring
  · simp only [↓reduceIte, Int.cast_mul, Int.cast_sub, oddCS_cast]
    ring

/-- The odd short terms of `W` from the packed numerators of `L`. -/
theorem oddW_packed (w : ℕ) (fwd : Bool) (L W : IdentVec) (X : List SVec) (D : ℚ)
    (hLt : L.ten = tensorRat w X D) :
    (W.sh.odd.map (fun q => (q.2 : ℚ) * triOddF fwd L q.1)).sum =
      (oddWZ w fwd X W : ℚ) / (2 * D) := by
  unfold oddWZ
  simp only [triOddF_packed w fwd L X D hLt]
  induction W.sh.odd with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons, ih, Int.cast_add, Int.cast_mul]
    ring

/-- The odd terms of `L` against the tensor of `W` from the packed numerators of `W`. -/
theorem oddL_packed (w : ℕ) (fwd : Bool) (L W : IdentVec) (Y : List SVec) (E : ℚ)
    (hWt : W.ten = tensorRat w Y E) :
    (L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) * triTCF fwd W q.1)).sum =
      L.sden * (oddLZ w fwd Y L : ℚ) / E := by
  unfold oddLZ
  simp only [triTCF_packed w fwd W Y E hWt]
  induction L.sh.odd with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons, ih, Int.cast_add, Int.cast_mul]
    ring

/-! ## The pairing with integer octad and odd parts -/

/-- The integer octad sum of `W` against the packed transform of `L`. -/
def octSumZ (w : ℕ) (fwd : Bool) (L W : IdentVec) : ℤ :=
  (W.sh.oct.map (fun b =>
    (b.2.map (fun q => q.2 * octZ w fwd (octPackXH w fwd L) b.1 q.1)).sum)).sum

/-- The pair short terms of `W` against the triality image of `L`. -/
def pairSumQ (fwd : Bool) (L W : IdentVec) : ℚ :=
  (W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF fwd L q.1)).sum

/-- `pairTriGM` with integer octad terms (packed transform, field width `wo`) and integer odd
terms read from the packed numerators. -/
def pairTriGMZ (wo w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ) : ℚ :=
  triMatF fwd L W +
    (if octPackOk wo L then
      W.sden * (pairSumQ fwd L W + L.sden * (octSumZ wo fwd L W : ℚ) / 8 +
        (oddWZ w fwd X W : ℚ) / (2 * D))
    else triShortF fwd L W) +
    (L.sden * (oddLZ w fwd Y L : ℚ) / E + (tdotM w (trialityTensorT w (!fwd) X) Y : ℚ) /
      (2 * D * E)) / 2

/-- With packed tensors, the integer pairing is `pairTriGM`. -/
theorem pairTriGMZ_eq (wo w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) :
    pairTriGMZ wo w fwd L W X Y D E = pairTriGM w fwd L W X Y D E := by
  rw [← pairTriGMH_eq wo]
  unfold pairTriGMZ pairTriGMH triShortOH
  rw [oddL_packed w fwd L W Y E hWt]
  split_ifs
  · rw [oddW_packed w fwd L W X D hLt]
    rfl
  · rfl

/-- The integer pairing from the values of its parts (each part can be evaluated separately). -/
theorem pairTriGMZ_parts {wo w : ℕ} {fwd : Bool} {L W : IdentVec} {X Y : List SVec} {D E : ℚ}
    {m p : ℚ} {n a b c : ℤ} (hok : octPackOk wo L = true) (hm : triMatF fwd L W = m)
    (hp : pairSumQ fwd L W = p) (hn : octSumZ wo fwd L W = n) (ha : oddWZ w fwd X W = a)
    (hb : oddLZ w fwd Y L = b) (hc : tdotM w (trialityTensorT w (!fwd) X) Y = c) :
    pairTriGMZ wo w fwd L W X Y D E =
      m + W.sden * (p + L.sden * (n : ℚ) / 8 + (a : ℚ) / (2 * D)) +
        (L.sden * (b : ℚ) / E + (c : ℚ) / (2 * D * E)) / 2 := by
  unfold pairTriGMZ
  rw [hok, hm, hp, hn, ha, hb, hc]
  rfl

/-- Forward identification from `pairTriGMZ`. -/
theorem ident_forward_GMZ (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriGMZ wo w true L W X Y D E = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_forward_GM i j h g L W hL hW hLt hWt hX hY hB hBC hx hy
    (by rw [← pairTriGMZ_eq wo w true L W X Y D E hLt hWt, hp])

/-- Inverse identification from `pairTriGMZ`. -/
theorem ident_inverse_GMZ (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriGMZ wo w false L W X Y D E = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_inverse_GM i j h g L W hL hW hLt hWt hX hY hB hBC hx hy
    (by rw [← pairTriGMZ_eq wo w false L W X Y D E hLt hWt, hp])
end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
