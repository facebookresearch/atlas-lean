/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthBinaryImage

/-! Exact cardinality of the genuine fifth stabilizer's binary extraspecial image. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Distinct literal translation and modulation pairs give distinct actual binary classes. -/
theorem generatedFifth_binary_coordinates_injective : Function.Injective
    (fun p : ZMod 2 × Fin 16 => Fin.append (p.1 • (Pi.single 11 1 : SpinIndex))
      (golayLabelCoefficients (generatedFifthModulationLabels p.2))) := by
  rintro ⟨b, k⟩ ⟨c, l⟩ h
  have hbc : b = c := by
    have he := congrFun h (Fin.castAdd 12 11)
    simpa only [Fin.append_left, Pi.smul_apply, Pi.single_apply, ite_true,
      smul_eq_mul, mul_one] using he
  have hm : golayLabelCoefficients (generatedFifthModulationLabels k) =
      golayLabelCoefficients (generatedFifthModulationLabels l) := by
    funext i
    have he := congrFun h (Fin.natAdd 12 i)
    simpa only [Fin.append_right] using he
  exact Prod.ext hbc
    (generatedFifth_modulation_labels_injective (golayLabelCoefficients_injective hm))

/-- The 32 literal binary coordinate pairs biject with the actual stabilizer binary image. -/
noncomputable def generatedFifthBinaryImageEquiv :
    (ZMod 2 × Fin 16) ≃ generatedFifthAxisBinaryImage :=
  Equiv.ofBijective (fun p => ⟨Fin.append (p.1 • (Pi.single 11 1 : SpinIndex))
    (golayLabelCoefficients (generatedFifthModulationLabels p.2)),
      (generatedFifth_axis_binary_image_mem _).mpr ⟨p.1, p.2, rfl⟩⟩) (by
        constructor
        · intro p r h
          exact generatedFifth_binary_coordinates_injective (congrArg Subtype.val h)
        · intro v
          obtain ⟨b, k, hk⟩ := (generatedFifth_axis_binary_image_mem v.val).mp v.property
          exact ⟨(b, k), Subtype.ext hk⟩)

/-- The actual stabilizer's binary extraspecial image has exactly 32 classes. -/
theorem generatedFifth_axis_binary_image_card : Nat.card generatedFifthAxisBinaryImage = 32 := by
  rw [← Nat.card_congr generatedFifthBinaryImageEquiv, Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
