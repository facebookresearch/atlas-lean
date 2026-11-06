/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorPairG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctP

/-! # The multiplicative packed pairing with the packed octad transform

`pairTriGMO` is `pairTriGM` (worker `gident`: multiplicative packed tensor pairing) in which the
octad short terms are computed by the packed Walsh-Hadamard transform (`triShortO`), so that the
octad part costs one packing, six butterflies and one field read per octad term of `W`.  It equals
`pairTriGM` unconditionally (`pairTriGMO_eq`), and the identification criteria follow. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent

/-- `pairTriGM` with the packed octad transform at octad field width `wo`. -/
def pairTriGMO (wo w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ) : ℚ :=
  triMatF fwd L W + triShortO wo fwd L W +
    ((L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) * triTCF fwd W q.1)).sum +
      (tdotM w (trialityTensorT w (!fwd) X) Y : ℚ) / (2 * D * E)) / 2

/-- The packed-octad pairing is `pairTriGM`. -/
theorem pairTriGMO_eq (wo w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ) :
    pairTriGMO wo w fwd L W X Y D E = pairTriGM w fwd L W X Y D E := by
  unfold pairTriGMO pairTriGM
  rw [triShortO_eq, triShortG_eq_F]

/-- Forward identification from `pairTriGMO`. -/
theorem ident_forward_GMO (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriGMO wo w true L W X Y D E = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_forward_GM i j h g L W hL hW hLt hWt hX hY hB hBC hx hy
    (by rw [← pairTriGMO_eq wo, hp])

/-- Inverse identification from `pairTriGMO`. -/
theorem ident_inverse_GMO (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriGMO wo w false L W X Y D E = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_inverse_GM i j h g L W hL hW hLt hWt hX hY hB hBC hx hy
    (by rw [← pairTriGMO_eq wo, hp])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
