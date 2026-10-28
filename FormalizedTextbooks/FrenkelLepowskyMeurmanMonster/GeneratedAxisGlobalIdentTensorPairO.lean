/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOctZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctP

/-! # The fully packed identification criterion

`pairTriPO` combines the packed pieces of the exact triality pairing: the packed octad
Walsh-Hadamard transform of `L` (worker `gident2`, `octPackX` / `octZ`), the packed odd cross
terms (`oddXP`) and the multiplicative packed tensor pairing (`tdotM`).  Only the matrix part and
the pair terms remain term by term. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The fully packed exact triality pairing (octad field width `wo`, tensor field width `w`). -/
def pairTriPO (wo w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ) : ℚ :=
  triMatF fwd L W +
    W.sden * ((W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF fwd L q.1)).sum +
      L.sden * (((W.sh.oct.map (fun b => (b.2.map (fun q =>
        q.2 * octZ wo fwd (octPackX wo fwd L) b.1 q.1)).sum)).sum : ℤ) : ℚ) / 8 +
      (oddXP w fwd (!fwd) W.sh.odd X : ℚ) / (2 * D)) +
    (L.sden * (oddXP w (!fwd) fwd L.sh.odd Y : ℚ) / E +
      (tdotM w (trialityTensorT w (!fwd) X) Y : ℚ) / (2 * D * E)) / 2

/-- With the packed octad transform applicable, packed tensors and bounds, `pairTriPO` is the
exact pairing. -/
theorem pairTriPO_eq {wo w B C : ℕ} (fwd : Bool) (L W : IdentVec) {X Y : List SVec} {D E : ℚ}
    (hok : octPackOk wo L = true) (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E)
    (hX : TBnd w B X) (hY : TBnd w C Y) (hb : PairXBounds w B C L W) :
    pairTriPO wo w fwd L W X Y D E = pairTri fwd L W := by
  rw [← pairTriZ_eq fwd L W hLt hWt hX hY hb]
  unfold pairTriPO pairTriZ octPartZ
  have h : ∀ o e, octZ wo fwd (octPackX wo fwd L) o e = octBlockSumZ fwd (lookupBlocks o L.sh.oct) e := by
    intro o e
    rw [octZ_eq wo fwd L hok o e, octSum_lookup]
  simp only [h]

/-- Forward identification from the fully packed pairing. -/
theorem ident_forward_PO (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hok : octPackOk wo L = true) (hLt : L.ten = tensorRat w X D)
    (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X) (hY : TBnd w C Y)
    (hb : PairXBounds w B C L W)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriPO wo w true L W X Y D E = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_forward i j h g L W hL hW hx hy
    (by rw [← pairTriPO_eq true L W hok hLt hWt hX hY hb, hp])

/-- Inverse identification from the fully packed pairing. -/
theorem ident_inverse_PO (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hok : octPackOk wo L = true) (hLt : L.ten = tensorRat w X D)
    (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X) (hY : TBnd w C Y)
    (hb : PairXBounds w B C L W)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriPO wo w false L W X Y D E = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_inverse i j h g L W hL hW hx hy
    (by rw [← pairTriPO_eq false L W hok hLt hWt hX hY hb, hp])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
