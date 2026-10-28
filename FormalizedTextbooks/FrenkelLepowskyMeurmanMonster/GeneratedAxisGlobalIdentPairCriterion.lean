/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairTri
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityInvariance

/-! # The pairing criterion for whole-vector identifications

All twelve family representatives and their local images are axes of norm `128`.  If the exact
pairing (`pairTri`) of the forward or inverse triality image of one local image with another
local image is `128`, the two vectors are equal (positive definiteness), and the triality image
lies in the union of the twelve local orbits. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent

/-- Every family representative has norm `128`. -/
theorem identRep_norm (i : Fin 12) :
    griessForm (generatedAxisGlobalTwelveRepresentative i)
      (generatedAxisGlobalTwelveRepresentative i) = 128 := by
  obtain ⟨g, hg⟩ := generatedAxisGlobalTwelveRepresentative_mem_generated i (Sum.inl (0, 0)) 0
  rw [← hg, generated_group_preserves_griessForm, conwayShortAxis_norm_sq]

/-- Every local image of a family representative has norm `128`. -/
theorem identLocal_norm (i : Fin 12) (h : H) :
    griessForm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i))
      (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = 128 := by
  rw [rhoLocal_form, identRep_norm]

/-- The inverse triality preserves the form. -/
theorem sExtra_symm_preserves_griessForm (x y : GriessSpace) :
    griessForm (sExtra.symm x) (sExtra.symm y) = griessForm x y := by
  have h := sExtra_preserves_griessForm (sExtra.symm x) (sExtra.symm y)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Forward identification: pairing `128` of representations identifies the whole vectors. -/
theorem ident_forward (i j : Fin 12) (h g : H) (L W : IdentVec) (hL : L.sh.ok = true)
    (hW : W.sh.ok = true)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTri true L W = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) := by
  apply eq_of_pairing_128
  · rw [sExtra_preserves_griessForm, identLocal_norm]
  · exact identLocal_norm j g
  · rw [pairTri_forward_actual _ _ L W hL hW hx hy, hp]
    norm_num

/-- Inverse identification: pairing `128` of representations identifies the whole vectors. -/
theorem ident_inverse (i j : Fin 12) (h g : H) (L W : IdentVec) (hL : L.sh.ok = true)
    (hW : W.sh.ok = true)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTri false L W = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) := by
  apply eq_of_pairing_128
  · rw [sExtra_symm_preserves_griessForm, identLocal_norm]
  · exact identLocal_norm j g
  · rw [pairTri_inverse_actual _ _ L W hL hW hx hy, hp]
    norm_num

/-- A forward identification places the triality image in the union of the local orbits. -/
theorem ident_forward_mem (i j : Fin 12) (h g : H) (L W : IdentVec) (hL : L.sh.ok = true)
    (hW : W.sh.ok = true)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTri true L W = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport j g (ident_forward i j h g L W hL hW hx hy hp)

/-- An inverse identification places the triality image in the union of the local orbits. -/
theorem ident_inverse_mem (i j : Fin 12) (h g : H) (L W : IdentVec) (hL : L.sh.ok = true)
    (hW : W.sh.ok = true)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTri false L W = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport j g (ident_inverse i j h g L W hL hW hx hy hp)

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
