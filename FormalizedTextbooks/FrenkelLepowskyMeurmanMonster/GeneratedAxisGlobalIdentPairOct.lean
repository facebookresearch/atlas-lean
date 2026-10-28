/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairFast

/-! # Integer octad terms of the exact pairings

The octad Fourier coefficients are read from one certified `64 × 64` sign table, and the octad
short terms of `pairTri` are accumulated in integers (one division per term).  This gives
`pairTriG` with `pairTriG_eq : pairTriG fwd L W = pairTri fwd L W`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators

/-- Negative entries of the octad Fourier matrix: bit `64 e + f` is set iff the entry is `-1`. -/
def identOctSignTable : ℕ :=
    0x9966669999999999999999995aa5a55aa55a5aa53cc3c33cc33c3cc30000000000000000 |||
    (0x6969969696966969ff0000ff00ffff00c3c3c3c3c3c3c3c3a5a5a5a5a5a5a5a566999966 <<< 288) |||
    (0x3333ccccf00ff00ff00ff00ff0f00f0f0f0ff0f0cc33cc33cc33cc33aa55aa55aa55aa55 <<< 576) |||
    (0xaaaa5555aaaa555569966996966996696996699669966996aaaa55555555aaaacccc3333 <<< 864) |||
    (0x55aa55aacc33cc3333cc33ccf0f00f0ff0f00f0ff00ff00f0ff00ff0cccc3333cccc3333 <<< 1152) |||
    (0xa5a5a5a55a5a5a5ac3c3c3c33c3c3c3cff0000ffff0000ff6969969669699696aa55aa55 <<< 1440) |||
    (0xffffffff3cc3c33c3cc3c33c5aa5a55a5aa5a55a99999999666666666699996666999966 <<< 1728) |||
    (0xf00f0ff0f00f0ff0cccccccc33333333aaaaaaaa55555555699696696996966900000000 <<< 2016) |||
    (0x00ff00ff6969696996969696aa5555aaaa5555aacc3333cccc3333ccf0f0f0f00f0f0f0f <<< 2304) |||
    (0x99996666999966666699669999669966a5a55a5aa5a55a5ac3c33c3cc3c33c3cff00ff00 <<< 2592) |||
    (0xc33cc33cffff00000000ffff0000ffff0000ffff3cc33cc3c33cc33c5aa55aa5a55aa55a <<< 2880) |||
    (0x5a5aa5a5a5a55a5a99669966996699666666999999996666a55aa55aa55aa55ac33cc33c <<< 3168) |||
    (0xcc3333cc55aaaa55aa5555aa969696969696969600ff00ff00ff00ff3c3cc3c3c3c33c3c <<< 3456) |||
    (0x555555555555555533333333333333330ff0f00ff00f0ff00f0f0f0f0f0f0f0f33cccc33 <<< 3744) |||
    (0x9669699669969669 <<< 4032)

/-- The octad Fourier coefficient (forward: `M e f`, inverse: `M f e`) from the sign table. -/
def octMT (fwd : Bool) (e f : ℕ) : ℤ :=
  if identOctSignTable.testBit (if fwd then 64 * (e % 64) + f % 64 else 64 * (f % 64) + e % 64)
  then -1 else 1

set_option maxRecDepth 100000 in
/-- The sign table agrees with the packed Fourier coefficients. -/
theorem identOctSignTable_spec : ∀ e f : Fin 64,
    ((if identOctSignTable.testBit (64 * e.val + f.val) then -1 else 1 : ℤ) : ℚ) =
      octMF true e.val f.val := by
  decide +kernel

/-- The table coefficient is the original Fourier coefficient. -/
theorem octMT_eq (fwd : Bool) (e f : ℕ) : (octMT fwd e f : ℚ) = octM fwd e f := by
  rw [← octMF_eq]
  cases fwd
  · have h := identOctSignTable_spec ⟨f % 64, Nat.mod_lt _ (by decide)⟩
      ⟨e % 64, Nat.mod_lt _ (by decide)⟩
    simp only [octMT, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [h]
    simp [octMF]
  · have h := identOctSignTable_spec ⟨e % 64, Nat.mod_lt _ (by decide)⟩
      ⟨f % 64, Nat.mod_lt _ (by decide)⟩
    simp only [octMT, ↓reduceIte] at h ⊢
    rw [h]
    simp [octMF]

/-- The octad short coordinate of a triality image, accumulated in integers. -/
def triOctT (fwd : Bool) (L : IdentVec) (o e : ℕ) : ℚ :=
  L.sden * (((L.sh.oct.map (fun b => if b.1 = o then
    (b.2.map (fun q => q.2 * octMT fwd e q.1)).sum else 0)).sum : ℤ) : ℚ) / 8

/-- The integer octad coordinate is the octad coordinate. -/
theorem triOctT_eq (fwd : Bool) (L : IdentVec) (o e : ℕ) :
    triOctT fwd L o e = triOctQ fwd L o e := by
  unfold triOctT triOctQ
  rw [mul_div_assoc]
  congr 1
  rw [Int.cast_list_sum, List.map_map]
  induction L.sh.oct with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.sum_cons, add_div, ih, Function.comp_apply]
    congr 1
    split_ifs
    · rw [Int.cast_list_sum, List.map_map, div_eq_mul_inv, list_sum_map_mul]
      congr 1
      apply List.map_congr_left
      intro q _
      simp only [Function.comp_apply, Int.cast_mul, octMT_eq]
      ring
    · simp

/-- The short part with integer octad terms. -/
def triShortG (fwd : Bool) (L W : IdentVec) : ℚ :=
  W.sden * ((W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF fwd L q.1)).sum +
    (W.sh.oct.map (fun b => (b.2.map (fun q => (q.2 : ℚ) * triOctT fwd L b.1 q.1)).sum)).sum +
    (W.sh.odd.map (fun q => (q.2 : ℚ) * triOddF fwd L q.1)).sum)

/-- The fast exact pairing with integer octad terms. -/
def pairTriG (fwd : Bool) (L W : IdentVec) : ℚ :=
  triMatF fwd L W + triShortG fwd L W +
    ((L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) * triTCF fwd W q.1)).sum +
      ∑ k : Fin 4096, ∑ j : Fin 24, tPartQ fwd L.ten k j * W.ten k j) / 2

/-- The integer-octad pairing is the exact pairing. -/
theorem pairTriG_eq (fwd : Bool) (L W : IdentVec) : pairTriG fwd L W = pairTri fwd L W := by
  rw [← pairTriF_eq]
  have h3 : ∀ o e, triOctT fwd L o e = triOctF fwd L o e := by
    intro o e
    rw [triOctT_eq]
    simp only [triOctF, triOctQ, octMF_eq]
  simp only [pairTriG, pairTriF, triShortG, triShortF, h3]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
