/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorOddX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentRegroupI

/-! # The octad part of the triality pairing blockwise in integers

`octPartZ` evaluates the octad part of the triality pairing (`triOctT` summed over the octad
terms of `W`) block by block: for every octad block of `W` the terms of `L` in the same octad are
collected once, and all products are integers.  With both vectors grouped by octad
(`ShortData.ofListI`) the cost is `blocks² + Σ_o n_W(o) n_L(o)` instead of
`terms(W) × blocks(L)` rational evaluations.  `pairTriZ` is `pairTriX` with this octad part. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- All terms of the blocks of octad `o`. -/
def lookupBlocks (o : ℕ) : List (ℕ × List (ℕ × ℤ)) → List (ℕ × ℤ)
  | [] => []
  | b :: bs => if b.1 = o then b.2 ++ lookupBlocks o bs else lookupBlocks o bs

/-- The integer octad Fourier sum of a list of octad terms at sign label `e`. -/
def octBlockSumZ (fwd : Bool) (Lb : List (ℕ × ℤ)) (e : ℕ) : ℤ := (Lb.map (fun q => q.2 * octMT fwd e q.1)).sum

/-- The octad part, blockwise in integers. -/
def octPartZ (fwd : Bool) (Lo Wo : List (ℕ × List (ℕ × ℤ))) : ℤ :=
  (Wo.map (fun b => (b.2.map (fun q => q.2 * octBlockSumZ fwd (lookupBlocks b.1 Lo) q.1)).sum)).sum

/-- Integer octad sums split along concatenation. -/
theorem octBlockSumZ_append (fwd : Bool) (A B : List (ℕ × ℤ)) (e : ℕ) :
    octBlockSumZ fwd (A ++ B) e = octBlockSumZ fwd A e + octBlockSumZ fwd B e := by
  simp only [octBlockSumZ, List.map_append, List.sum_append]

/-- The block filter of `triOctT` is the octad sum of the collected terms. -/
theorem octSum_lookup (fwd : Bool) (o e : ℕ) : ∀ bs : List (ℕ × List (ℕ × ℤ)),
    (bs.map (fun b => if b.1 = o then (b.2.map (fun q => q.2 * octMT fwd e q.1)).sum else 0)).sum =
      octBlockSumZ fwd (lookupBlocks o bs) e
  | [] => by simp [lookupBlocks, octBlockSumZ]
  | b :: bs => by
    simp only [List.map_cons, List.sum_cons, lookupBlocks]
    rw [octSum_lookup fwd o e bs]
    split_ifs
    · rw [octBlockSumZ_append]
      rfl
    · simp

/-- The octad part of the triality pairing is the blockwise integer octad part. -/
theorem octPart_eq (fwd : Bool) (L W : IdentVec) :
    (W.sh.oct.map (fun b => (b.2.map (fun q => (q.2 : ℚ) * triOctT fwd L b.1 q.1)).sum)).sum =
      L.sden * (octPartZ fwd L.sh.oct W.sh.oct : ℚ) / 8 := by
  unfold octPartZ
  rw [cast_list_sum, mul_div_assoc, list_sum_div_const, const_mul_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  rw [cast_list_sum, list_sum_div_const, const_mul_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  unfold triOctT
  rw [octSum_lookup]
  push_cast
  ring

/-- The exact triality pairing with all tensor terms packed and the octad part blockwise in
integers. -/
def pairTriZ (w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ) : ℚ :=
  triMatF fwd L W +
    W.sden * ((W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF fwd L q.1)).sum +
      L.sden * (octPartZ fwd L.sh.oct W.sh.oct : ℚ) / 8 +
      (oddXP w fwd (!fwd) W.sh.odd X : ℚ) / (2 * D)) +
    (L.sden * (oddXP w (!fwd) fwd L.sh.odd Y : ℚ) / E +
      (tdotM w (trialityTensorT w (!fwd) X) Y : ℚ) / (2 * D * E)) / 2

/-- With packed tensors and bounds, `pairTriZ` is the exact pairing. -/
theorem pairTriZ_eq {w B C : ℕ} (fwd : Bool) (L W : IdentVec) {X Y : List SVec} {D E : ℚ}
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hb : PairXBounds w B C L W) :
    pairTriZ w fwd L W X Y D E = pairTri fwd L W := by
  rw [← pairTriX_eq fwd L W hLt hWt hX hY hb]
  unfold pairTriZ pairTriX
  rw [octPart_eq]

/-- Forward identification from `pairTriZ`. -/
theorem ident_forward_Z (i j : Fin 12) (h g : H) (L W : IdentVec) {w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hb : PairXBounds w B C L W)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriZ w true L W X Y D E = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_forward i j h g L W hL hW hx hy (by rw [← pairTriZ_eq true L W hLt hWt hX hY hb, hp])

/-- Inverse identification from `pairTriZ`. -/
theorem ident_inverse_Z (i j : Fin 12) (h g : H) (L W : IdentVec) {w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hb : PairXBounds w B C L W)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriZ w false L W X Y D E = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_inverse i j h g L W hL hW hx hy (by rw [← pairTriZ_eq false L W hLt hWt hX hY hb, hp])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
