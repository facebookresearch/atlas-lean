/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorTPart
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairCriterion

/-! # The identification criterion with packed tensors

`pairTriP` is the fast exact triality pairing `pairTriF` in which the dense tensor-to-tensor sum
is evaluated as one packed dot product (`tPart_sum`).  The criterion theorems
`ident_forward_packed` / `ident_inverse_packed` identify whole vectors from the single kernel
evaluation `pairTriP .. = 128`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The fast exact pairing with the dense tensor sum as a packed dot product. -/
def pairTriP (w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ) : ℚ :=
  triMatF fwd L W + triShortF fwd L W +
    ((L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) * triTCF fwd W q.1)).sum +
      (tdot w (trialityTensorT w (!fwd) X) Y : ℚ) / (2 * D * E)) / 2

/-- With packed tensors, the packed pairing is the exact pairing. -/
theorem pairTriP_eq {w B : ℕ} (fwd : Bool) (L W : IdentVec) {X Y : List SVec} {D E : ℚ}
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w) :
    pairTriP w fwd L W X Y D E = pairTri fwd L W := by
  rw [← pairTriF_eq]
  unfold pairTriF pairTriP
  rw [hLt, hWt, tPart_sum fwd hX hB Y D E]

/-- Forward identification from a packed pairing. -/
theorem ident_forward_packed (i j : Fin 12) (h g : H) (L W : IdentVec) {w B : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriP w true L W X Y D E = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_forward i j h g L W hL hW hx hy (by rw [← pairTriP_eq true L W hLt hWt hX hB, hp])

/-- Inverse identification from a packed pairing. -/
theorem ident_inverse_packed (i j : Fin 12) (h g : H) (L W : IdentVec) {w B : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriP w false L W X Y D E = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_inverse i j h g L W hL hW hx hy (by rw [← pairTriP_eq false L W hLt hWt hX hB, hp])

/-- A forward packed identification places the image in the union of the local orbits. -/
theorem ident_forward_packed_mem (i j : Fin 12) (h g : H) (L W : IdentVec) {w B : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriP w true L W X Y D E = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport j g
    (ident_forward_packed i j h g L W hL hW hLt hWt hX hB hx hy hp)

/-- An inverse packed identification places the image in the union of the local orbits. -/
theorem ident_inverse_packed_mem (i j : Fin 12) (h g : H) (L W : IdentVec) {w B : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriP w false L W X Y D E = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport j g
    (ident_inverse_packed i j h g L W hL hW hLt hWt hX hB hx hy hp)

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
