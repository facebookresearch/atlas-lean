/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineMarkingCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinatesComplete

/-! The complete original marking catalogue is an actual union of nine affine four-spaces
in the genuine lattice quotient. Coefficient classification and the intrinsic spread
stabilizer remain separate obligations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original anchor as an actual lattice-quotient class. -/
def generatedNinthAffineAnchorClass (i : Fin 9) : LeechModTwo :=
  leechHyperbolicCoordinates.symm
    (monsterCo1GeometryBinaryMaskDecode
      (generatedNinthMarkingMask (generatedNinthAffineAnchorIndex i)))

/-- The genuine quotient linear map of the four directions of an original marking fiber. -/
def generatedNinthAffineDirectionClassMap (i : Fin 9) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] LeechModTwo :=
  leechHyperbolicCoordinates.symm.toLinearMap.comp (generatedNinthAffineDirectionMap i)

/-- The actual whole four-dimensional quotient subspace of a marking fiber. -/
def generatedNinthAffineDirectionClassSpace (i : Fin 9) :
    Submodule (ZMod 2) LeechModTwo :=
  (generatedNinthAffineDirectionClassMap i).range

/-- Every original fiber has independent actual quotient directions. -/
theorem generatedNinth_affine_direction_class_injective (i : Fin 9) :
    Function.Injective (generatedNinthAffineDirectionClassMap i) :=
  leechHyperbolicCoordinates.symm.injective.comp
    (generatedNinth_affine_direction_injective i)

/-- Each whole actual direction space has sixteen elements. -/
theorem generatedNinth_affine_direction_class_card (i : Fin 9) :
    Nat.card (generatedNinthAffineDirectionClassSpace i) = 16 := by
  rw [generatedNinthAffineDirectionClassSpace]
  change Nat.card (Set.range (generatedNinthAffineDirectionClassMap i)) = 16
  rw [← Nat.card_congr (Equiv.ofInjective (generatedNinthAffineDirectionClassMap i)
    (generatedNinth_affine_direction_class_injective i))]
  exact Nat.card_congr (Equiv.ofBijective generatedNinthAffineCoefficientLabel
    generatedNinth_affine_coefficient_label_bijective) |>.trans (Nat.card_fin 16)

/-- The original dictionary index of an affine fiber coordinate. -/
def generatedNinthAffineMarkingReindex (p : Fin 9 × (Fin 4 → ZMod 2)) : Fin 144 :=
  generatedNinthAffineMarkingIndex p.1 (generatedNinthAffineCoefficientLabel p.2)

/-- The affine coordinates exhaust all original marking indices. -/
theorem generatedNinth_affine_marking_reindex_surjective :
    Function.Surjective generatedNinthAffineMarkingReindex := by
  intro k
  obtain ⟨⟨i, j⟩, hk⟩ := generatedNinth_affine_marking_index_bijective.2 k
  obtain ⟨a, ha⟩ := generatedNinth_affine_coefficient_label_bijective.2 j
  exact ⟨(i, a), by simpa only [generatedNinthAffineMarkingReindex, ha] using hk⟩

/-- Every original affine coordinate is its genuine source-marking quotient class. -/
theorem generatedNinth_affine_marking_class (i : Fin 9) (a : Fin 4 → ZMod 2) :
    leechHyperbolicCoordinates.symm (monsterCo1GeometryBinaryMaskDecode
      (generatedNinthMarkingMask (generatedNinthAffineMarkingReindex (i, a)))) =
        generatedNinthAffineAnchorClass i + generatedNinthAffineDirectionClassMap i a := by
  apply leechHyperbolicCoordinates.injective
  change leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm _) = _
  rw [LinearEquiv.apply_symm_apply, map_add]
  change monsterCo1GeometryBinaryMaskDecode
      (generatedNinthMarkingMask
        (generatedNinthAffineMarkingIndex i (generatedNinthAffineCoefficientLabel a))) =
    leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm _) +
      leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm _)
  simpa only [LinearEquiv.apply_symm_apply] using
    generatedNinth_affine_marking_coordinates i a

/-- The whole actual source-marking carrier is exactly the nine affine four-space union. -/
theorem generatedNinth_marked_short_classes_eq_affine_range :
    generatedNinthMarkedShortClasses =
      Set.range (fun p : Fin 9 × (Fin 4 → ZMod 2) =>
        generatedNinthAffineAnchorClass p.1 + generatedNinthAffineDirectionClassMap p.1 p.2) := by
  rw [generatedNinth_marked_short_classes_eq_coordinate_range]
  ext v
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨⟨i, a⟩, rfl⟩ := generatedNinth_affine_marking_reindex_surjective k
    exact ⟨(i, a), (generatedNinth_affine_marking_class i a).symm⟩
  · rintro ⟨⟨i, a⟩, rfl⟩
    exact ⟨generatedNinthAffineMarkingReindex (i, a),
      generatedNinth_affine_marking_class i a⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
