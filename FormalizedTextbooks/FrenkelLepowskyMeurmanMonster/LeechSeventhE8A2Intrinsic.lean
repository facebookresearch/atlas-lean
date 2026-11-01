/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2Stabilizer

/-! Intrinsic A2 planes in an arbitrary genuine integral section, with preferred signs retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The intrinsic real A2 planes spanned by two nonorthogonal actual short lines in a section. -/
def leechSeventhA2PlanesIn (S : Submodule ℤ leechIntegral) :
    Set (Submodule ℝ (Fin 24 → ℝ)) :=
  {W | ∃ r s : GriessShortIndex, r ∈ generatedAxisE8ShortLines S ∧
    s ∈ generatedAxisE8ShortLines S ∧
    |stdPairingFun (griessShortVector r) (griessShortVector s)| = 2 ∧
    W = Submodule.span ℝ {griessShortVector r, griessShortVector s}}

/-- Changing either root orientation does not change its two-root span. -/
theorem leechSeventh_span_pair_sign (x y u v : Fin 24 → ℝ)
    (hx : x = u ∨ x = -u) (hy : y = v ∨ y = -v) :
    Submodule.span ℝ {x, y} = Submodule.span ℝ {u, v} := by
  have hn (w : Fin 24 → ℝ) : Submodule.span ℝ {-w} = Submodule.span ℝ {w} := by
    simpa only [neg_one_smul] using
      Submodule.span_singleton_smul_eq (isUnit_neg_one : IsUnit (-1 : ℝ)) w
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp only [Submodule.span_insert, hn]

/-- Absolute actual physical pairing is independent of preferred root orientation. -/
theorem leechSeventh_pairing_abs_sign (x y u v : Fin 24 → ℝ)
    (hx : x = u ∨ x = -u) (hy : y = v ∨ y = -v) :
    |stdPairingFun x y| = |stdPairingFun u v| := by
  change |x ⬝ᵥ y| = |u ⬝ᵥ v|
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp only [dotProduct_neg, neg_dotProduct, neg_neg, abs_neg]

/-- The finite root pairing condition is exactly the genuine preferred physical pairing. -/
theorem leechSeventhE8Root_pairing_iff (r s : Fin 120) :
    |∑ i, leechSeventhE8RootLocal r i * leechSeventhE8RootLocal s i| = 16 ↔
      |stdPairingFun (griessShortVector (leechSeventhE8RootLabel r))
        (griessShortVector (leechSeventhE8RootLabel s))| = 2 := by
  rw [← leechSeventh_pairing_abs_sign _ _ _ _
    (leechSeventhE8RealRoot_label_sign r) (leechSeventhE8RealRoot_label_sign s),
    leechSeventhE8RealRoot_pairing]
  simp only [abs_div, show |(8 : ℝ)| = 8 by norm_num]
  constructor
  · intro h
    have hR : |((∑ i, leechSeventhE8RootLocal r i *
        leechSeventhE8RootLocal s i : ℤ) : ℝ)| = 16 := by exact_mod_cast h
    rw [hR]
    norm_num
  · intro h
    have hR : |((∑ i, leechSeventhE8RootLocal r i *
        leechSeventhE8RootLocal s i : ℤ) : ℝ)| = 16 := by linarith
    exact_mod_cast hR

/-- The finite selected-section carrier is exactly the intrinsic actual short-line carrier. -/
theorem leechSeventhE8A2Planes_eq_intrinsic :
    leechSeventhE8A2Planes = leechSeventhA2PlanesIn
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) := by
  ext W
  constructor
  · rintro ⟨r, s, hrs, rfl⟩
    refine ⟨leechSeventhE8RootLabel r, leechSeventhE8RootLabel s,
      leechSeventhE8Root_label_supported r, leechSeventhE8Root_label_supported s,
      (leechSeventhE8Root_pairing_iff r s).mp hrs, ?_⟩
    exact leechSeventh_span_pair_sign _ _ _ _
      (leechSeventhE8RealRoot_label_sign r) (leechSeventhE8RealRoot_label_sign s)
  · rintro ⟨r, s, hr, hs, hrs, rfl⟩
    let a := leechSeventhE8RootLabelEquiv.symm ⟨r, hr⟩
    let b := leechSeventhE8RootLabelEquiv.symm ⟨s, hs⟩
    have ha : leechSeventhE8RootLabel a = r :=
      congrArg Subtype.val (leechSeventhE8RootLabelEquiv.apply_symm_apply ⟨r, hr⟩)
    have hb : leechSeventhE8RootLabel b = s :=
      congrArg Subtype.val (leechSeventhE8RootLabelEquiv.apply_symm_apply ⟨s, hs⟩)
    refine ⟨a, b, (leechSeventhE8Root_pairing_iff a b).mpr ?_, ?_⟩
    · rwa [ha, hb]
    · symm
      have h := leechSeventh_span_pair_sign _ _ _ _
        (leechSeventhE8RealRoot_label_sign a) (leechSeventhE8RealRoot_label_sign b)
      rwa [ha, hb] at h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
