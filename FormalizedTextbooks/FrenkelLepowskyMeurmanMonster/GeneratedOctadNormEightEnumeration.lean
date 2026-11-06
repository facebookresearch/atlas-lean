/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightVectors

/-! A bijective finite source enumeration of the actual section vectors. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The central source residue, as well as the coordinates, is recovered uniquely. -/
theorem generatedOctadBoundedVector_injective : Function.Injective generatedOctadBoundedVector := by
  rintro ⟨b, a⟩ ⟨d, k⟩ h
  have hv : generatedOctadEightInteger a.val = generatedOctadEightInteger k.val :=
    congrArg (fun x => x.val.val) h
  have hak : a.val = k.val := generatedOctadEightInteger_injective hv
  have hr : 2 * (b.val : ZMod 4) = 2 * (d.val : ZMod 4) := by
    have he := congrArg (fun z : ℤ => (z : ZMod 4))
      (congrFun hak (0 : Fin 8) |> congrArg leechNormEightCoordinate)
    exact (a.property.1 0).symm.trans (he.trans (k.property.1 0))
  have hb : b = d := by
    have hs : ∀ b d : ZMod 2, 2 * (b.val : ZMod 4) = 2 * (d.val : ZMod 4) → b = d := by
      decide +kernel
    exact hs b d hr
  subst d
  have he : a = k := Subtype.ext hak
  subst k
  rfl

/-- The norm bounds give a bounded assignment for every genuine section vector
with the specified source residue. -/
theorem generatedOctadBoundedVector_of_residue (b : ZMod 2)
    (u : leechIntegral) (hu : generatedStandardOctadSupported u.val)
    (hn : leechSquareSum u.val = 64)
    (hr : ∀ j : Fin 8, (u.val (Fin.castAdd 16 j) : ZMod 4) = 2 * (b.val : ZMod 4))
    (hh : ((∑ i, u.val i : ℤ) : ZMod 8) = 0) :
    ∃ a : GeneratedOctadNormEightBounded b, generatedOctadEightInteger a.val = u.val := by
  let a : Fin 8 → Fin 17 := fun j =>
    ⟨(u.val (Fin.castAdd 16 j) + 8).toNat, by
      have hb := leechNormEight_natAbs_le u.val hn (Fin.castAdd 16 j)
      have he : |u.val (Fin.castAdd 16 j)| ≤ (8 : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hb
      obtain ⟨hl, hh⟩ := abs_le.mp he
      omega⟩
  have ha (j : Fin 8) : leechNormEightCoordinate (a j) = u.val (Fin.castAdd 16 j) := by
    have hb := leechNormEight_natAbs_le u.val hn (Fin.castAdd 16 j)
    have he : |u.val (Fin.castAdd 16 j)| ≤ (8 : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hb
    obtain ⟨hl, hh⟩ := abs_le.mp he
    dsimp [a, leechNormEightCoordinate]
    omega
  have hout (j : Fin 16) : u.val (Fin.natAdd 8 j) = 0 :=
    hu _ (by change 8 ≤ 8 + j.val; omega)
  have hs8 : (∑ j : Fin 8, u.val (Fin.castAdd 16 j) ^ 2) = 64 := by
    unfold leechSquareSum at hn
    rw [Fin.sum_univ_add (a := 8) (b := 16)] at hn
    simpa only [hout, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, add_zero] using hn
  have hh8 : ((∑ j : Fin 8, u.val (Fin.castAdd 16 j) : ℤ) : ZMod 8) = 0 := by
    rw [Fin.sum_univ_add (a := 8) (b := 16)] at hh
    simpa only [hout, Finset.sum_const_zero, add_zero] using hh
  have han : (∑ j, (leechNormEightCoordinate (a j)).natAbs ^ 2) = 64 := by
    have he : ((∑ j, (leechNormEightCoordinate (a j)).natAbs ^ 2 : ℕ) : ℤ) = 64 := by
      simpa only [Nat.cast_sum, Nat.cast_pow, Int.natCast_natAbs, sq_abs, ha] using hs8
    exact_mod_cast he
  refine ⟨⟨a, ⟨fun j => by rw [ha]; exact hr j, han, ?_⟩⟩, ?_⟩
  · simpa only [ha] using hh8
  · funext i
    refine Fin.addCases (m := 8) (n := 16) ?_ ?_ i
    · intro j
      simpa only [generatedOctadEightInteger, Fin.append_left] using ha j
    · intro j
      simpa only [generatedOctadEightInteger, Fin.append_right] using (hout j).symm

/-- Every actual norm-eight section vector occurs in the counted source space. -/
theorem generatedOctadBoundedVector_surjective :
    Function.Surjective generatedOctadBoundedVector := by
  intro x
  have hu := (generatedOctadSupported_standard x.val.val).mp x.property.1
  obtain ⟨c, hc, hr, hh⟩ := generatedStandardOctad_source x.val hu
  rcases hc with hc | hc
  · have hr0 : ∀ j : Fin 8, (x.val.val (Fin.castAdd 16 j) : ZMod 4) =
        2 * ((0 : ZMod 2).val : ZMod 4) := by
      intro j
      simpa only [hc, Pi.zero_apply] using hr (Fin.castAdd 16 j)
    obtain ⟨a, ha⟩ := generatedOctadBoundedVector_of_residue 0 x.val hu x.property.2 hr0 hh
    refine ⟨⟨0, a⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact ha
  · have hr1 : ∀ j : Fin 8, (x.val.val (Fin.castAdd 16 j) : ZMod 4) =
        2 * ((1 : ZMod 2).val : ZMod 4) := by
      intro j
      have he := hr (Fin.castAdd 16 j)
      rw [hc] at he
      simpa [golayStandardOctad] using he
    obtain ⟨a, ha⟩ := generatedOctadBoundedVector_of_residue 1 x.val hu x.property.2 hr1 hh
    refine ⟨⟨1, a⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact ha

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
