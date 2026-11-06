/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE28PA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE28PB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE28MA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE28MB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots

/-! # Dense pilot: both triality images at the representative coset of Eighth root 28

With `h = [xi, mono (0, false)]` (the representative coset of Eighth root 28) and the Eighth
representative `v₈`: `sExtra (h v₈) = g v₈` for `g = [qel (qmElt (4030716, true)), sign 1815 0] ++ h`
and `sExtra⁻¹ (h v₈) = gm v₈` for `gm = [qel (qmElt (4491039, true)), sign 2029 0] ++ h` (both exact
packed pairings are `128`; dense vectors with 43676 short terms each).  Hence the Eighth root bound
at root 28 (`e28_root`, through goctad's wrapper `generatedAxisGlobalTwelveEighthBind_root28`),
from explicit identifications only. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing of `sExtra (h v₈)` with `g v₈` is `128`. -/
theorem e28p_pair : pairTriGMZ 32 64 true e28VH e28VG e28XH e28XG e28EH e28EG = 128 := by
  rw [pairTriGMZ_parts e28p_octOk e28p_partM e28p_partP e28p_partO e28p_partA e28p_partB
    e28p_partC, show e28VG.sden = 1 / 32 from e8SrcVecS_sden,
    show e28VH.sden = 1 / 32 from e8SrcVecS_sden, e28p_EH, e28p_EG]
  norm_num

/-- The exact pairing of `sExtra⁻¹ (h v₈)` with `gm v₈` is `128`. -/
theorem e28m_pair : pairTriGMZ 32 64 false e28VH e28VGm e28XH e28XGm e28EH e28EGm = 128 := by
  rw [pairTriGMZ_parts e28m_octOk e28m_partM e28m_partP e28m_partO e28m_partA e28m_partB
    e28m_partC, show e28VGm.sden = 1 / 32 from e8SrcVecS_sden,
    show e28VH.sden = 1 / 32 from e8SrcVecS_sden, e28m_EH, e28m_EGm]
  norm_num

/-- Positive triality: `sExtra (h v₈) = g v₈`. -/
theorem e28p_ident : sExtra (rhoLocal (identWordLocal e28H) (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal e28G) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_forward_GMZ 7 7 _ _ e28VH e28VG e28VH_ok e28VG_ok e28VH_ten e28VG_ten e28XH_bnd e28XG_bnd
    (by norm_num) (by norm_num) e28VH_actual e28VG_actual e28p_pair

/-- Inverse triality: `sExtra⁻¹ (h v₈) = gm v₈`. -/
theorem e28m_ident :
    sExtra.symm (rhoLocal (identWordLocal e28H) (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal e28Gm) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_inverse_GMZ 7 7 _ _ e28VH e28VGm e28VH_ok e28VGm_ok e28VH_ten e28VGm_ten e28XH_bnd
    e28XGm_bnd (by norm_num) (by norm_num) e28VH_actual e28VGm_actual e28m_pair

/-- The representative coset of Eighth root 28 is the word `h`. -/
theorem e28_coset : generatedAxisGlobalTwelveEighthBindCoset28 = identWordLocal e28H := rfl

/-- Eighth root 28: both triality images at its representative coset lie in the union of the twelve
local orbits (explicit identifications with H-images of the Eighth representative). -/
theorem e28_root : GeneratedAxisGlobalTwelveEighthRootBound 28 :=
  generatedAxisGlobalTwelveEighthBind_root28
    ⟨7, identWordLocal e28G, by rw [e28_coset]; exact e28p_ident⟩
    ⟨7, identWordLocal e28Gm, by rw [e28_coset]; exact e28m_ident⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
