/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorDot
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOct

/-! # The identification criterion: integer octad terms and multiplicative tensor pairing

`pairTriGM` is the exact triality pairing `pairTriG` (integer octad Fourier terms, worker
`gident2`) in which the dense tensor-to-tensor sum is one multiplicative packed dot product
(`tdotM`).  `ident_forward_GM` / `ident_inverse_GM` identify whole vectors from the single kernel
evaluation `pairTriGM .. = 128`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The fast exact pairing: integer octad terms and the multiplicative packed tensor pairing. -/
def pairTriGM (w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ) : ℚ :=
  triMatF fwd L W + triShortG fwd L W +
    ((L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) * triTCF fwd W q.1)).sum +
      (tdotM w (trialityTensorT w (!fwd) X) Y : ℚ) / (2 * D * E)) / 2

/-- With packed tensors and bounds, `pairTriGM` is the exact pairing. -/
theorem pairTriGM_eq {w B C : ℕ} (fwd : Bool) (L W : IdentVec) {X Y : List SVec} {D E : ℚ}
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w) :
    pairTriGM w fwd L W X Y D E = pairTri fwd L W := by
  rw [← pairTriG_eq]
  unfold pairTriG pairTriGM
  rw [hLt, hWt, tPart_sum fwd hX hB Y D E,
    tdotM_eq (trialityTensorT_spec (!fwd) hX hB).1 hY hBC]

/-- Forward identification from `pairTriGM`. -/
theorem ident_forward_GM (i j : Fin 12) (h g : H) (L W : IdentVec) {w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriGM w true L W X Y D E = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_forward i j h g L W hL hW hx hy (by rw [← pairTriGM_eq true L W hLt hWt hX hY hB hBC, hp])

/-- Inverse identification from `pairTriGM`. -/
theorem ident_inverse_GM (i j : Fin 12) (h g : H) (L W : IdentVec) {w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriGM w false L W X Y D E = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_inverse i j h g L W hL hW hx hy (by rw [← pairTriGM_eq false L W hLt hWt hX hY hB hBC, hp])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
