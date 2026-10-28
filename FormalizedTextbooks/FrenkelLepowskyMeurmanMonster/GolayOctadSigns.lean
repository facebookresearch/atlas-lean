/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exactly the even sign patterns extend over the standard Golay octad. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOctadTransitivity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayCoordinateProjection

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every Golay word restricts to an even word on the standard octad. -/
theorem golayStandardOctad_restriction_even (c : golayCode) :
    (∑ j : Fin 8, c.val (Fin.castAdd 16 j)) = 0 := by
  have h := golayCode_self_orthogonal c.val golayStandardOctad c.property
    golayStandardOctad_mem
  simpa [golayStandardOctad, Fin.sum_univ_succ, add_assoc] using h

/-- Every even eight-bit prescription on the standard octad extends to an actual Golay word. -/
theorem golayStandardOctad_even_signs (bits : Fin 8 → ZMod 2)
    (heven : ∑ j, bits j = 0) :
    ∃ c : golayCode, ∀ j : Fin 8, c.val (Fin.castAdd 16 j) = bits j := by
  let f : Fin 7 → Fin 24 := fun j => Fin.castAdd 17 j
  have hf : Function.Injective f := by
    intro j k h
    exact Fin.ext (congrArg (fun i : Fin 24 => i.val) h)
  obtain ⟨c, hc⟩ := golayCoordinateProjection_surjective (by decide : 7 < 8) f hf
    (fun j => bits j.castSucc)
  have hfirst (j : Fin 7) : c.val (Fin.castAdd 16 j.castSucc) = bits j.castSucc := by
    exact congrFun hc j
  have hlast : c.val (Fin.castAdd 16 (Fin.last 7)) = bits (Fin.last 7) := by
    have hcode := golayStandardOctad_restriction_even c
    rw [Fin.sum_univ_castSucc] at hcode heven
    simp_rw [hfirst] at hcode
    exact add_left_cancel (hcode.trans heven.symm)
  refine ⟨c, ?_⟩
  intro j
  exact Fin.lastCases hlast hfirst j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
