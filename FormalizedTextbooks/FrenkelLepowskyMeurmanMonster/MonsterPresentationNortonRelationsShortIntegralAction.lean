/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Generic actual short-basis transport in the genuine integer lattice coordinates,
with the full Norton u specialization and all central phases retained. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortFromVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLocalIntegral
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImage

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The preferred coefficient-zero Q lift of finite integer lattice coordinates. -/
def monsterNortonCoordinateQ (z : Fin 24 → ℤ) : Q :=
  ⟨ofAdd (leechHyperbolicInverse *ᵥ integerParity z), 1⟩

private theorem coordinates_map (t : Fin 24 → ℤ) :
    leechExplicitCoordinates (leechExplicitCoordinateMap t) = t :=
  leechExplicitCoordinates.apply_symm_apply t

variable (f : localFiberSubgroup) (C : Matrix (Fin 24) (Fin 24) ℤ)
variable (he : ∀ z : Fin 24 → ℤ,
  f.val.2.val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
    leechCoordinateEmbedding (leechBasisMatrix *ᵥ (C *ᵥ z)))

include he in
/-- An actual certified integral basis action preserves the short-vector norm. -/
theorem monsterNortonIntegralAction_short_norm (z : Fin 24 → ℤ)
    (hn : leechSquareSum (leechBasisMatrix *ᵥ z) = 32) :
    leechSquareSum (leechBasisMatrix *ᵥ (C *ᵥ z)) = 32 := by
  have hu : leechIntegralAction f.val.2 (leechExplicitCoordinateMap z) =
      leechExplicitCoordinateMap (C *ᵥ z) := by
    apply leechExplicitCoordinates.injective
    rw [leechIntegralAction_coordinates_of_basis_certificate _ _ he]
    rw [coordinates_map, coordinates_map]
  have hs := leechIntegralAction_squareSum f.val.2 (leechExplicitCoordinateMap z)
  rw [hu] at hs
  exact hs.trans hn

include he in
/-- The actual spin conjugation of a preferred-coordinate lift has the certified lattice image. -/
theorem monsterNortonIntegralAction_Q_binary (z : Fin 24 → ℤ) :
    toAdd (spinConjugation f.val.1 (monsterNortonCoordinateQ z)).base =
      leechHyperbolicInverse *ᵥ integerParity (C *ᵥ z) := by
  have ha := qBinaryAction_apply (spinConjugation f.val.1) (monsterNortonCoordinateQ z)
  change spinBinaryAction f.val.1 (leechHyperbolicInverse *ᵥ integerParity z) = _ at ha
  have hz : leechHyperbolicCoordinates (leechReduction (leechExplicitCoordinateMap z)) =
      leechHyperbolicInverse *ᵥ integerParity z := by
    rw [leechHyperbolicCoordinates_explicit]
    rw [coordinates_map]
  rw [← hz, f.property, leechBinaryAction_coordinates] at ha
  change leechHyperbolicCoordinates
    (leechReduction (leechIntegralAction f.val.2 (leechExplicitCoordinateMap z))) = _ at ha
  rw [leechHyperbolicCoordinates_explicit,
    leechIntegralAction_coordinates_of_basis_certificate _ _ he] at ha
  rw [coordinates_map] at ha
  exact ha.symm

/-- The actual central coefficient of the preferred-coordinate spin image. -/
noncomputable def monsterNortonIntegralShortPhase (z : Fin 24 → ℤ) : ZMod 2 :=
  toAdd (spinConjugation f.val.1 (monsterNortonCoordinateQ z)).coeff

include he in
/-- The preferred short labels are transported with their full actual central correction. -/
theorem monsterNortonIntegralAction_short_Q_image (z : Fin 24 → ℤ)
    (hn : leechSquareSum (leechBasisMatrix *ᵥ z) = 32) :
    spinConjugation f.val.1
      (monsterNortonShortQ (monsterNortonShortIndexOfCoordinates z hn)) =
    qCentral (monsterNortonIntegralShortPhase f z) *
      monsterNortonShortQ (monsterNortonShortIndexOfCoordinates (C *ᵥ z)
        (monsterNortonIntegralAction_short_norm f C he z hn)) := by
  rw [monsterNortonShortIndexOfCoordinates_Q, monsterNortonShortIndexOfCoordinates_Q]
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    apply toAdd.injective
    exact monsterNortonIntegralAction_Q_binary f C he z
  · apply toAdd.injective
    rw [qCentral_mul_coeff]
    change monsterNortonIntegralShortPhase f z = monsterNortonIntegralShortPhase f z + 0
    rw [add_zero]

include he in
/-- Certified shortest vectors have actual Griess short-basis transport without enumeration. -/
theorem monsterNortonIntegralAction_short_basis (z : Fin 24 → ℤ)
    (hn : leechSquareSum (leechBasisMatrix *ᵥ z) = 32) :
    localGriessRepresentation f
      (griessConwayDecode (0, (Pi.single (monsterNortonShortIndexOfCoordinates z hn) 1, 0))) =
    griessConwayDecode (0, (qSign (monsterNortonIntegralShortPhase f z) •
      Pi.single (monsterNortonShortIndexOfCoordinates (C *ᵥ z)
        (monsterNortonIntegralAction_short_norm f C he z hn)) (1 : ℝ), 0)) :=
  monsterNortonGriessShortBasis_of_Q_image _ _ _ _
    (monsterNortonIntegralAction_short_Q_image f C he z hn)

/-- The complete actual source Norton u preserves norm32 in integer lattice coordinates. -/
theorem monsterNortonUIntegralAction_short_norm (z : Fin 24 → ℤ)
    (hn : leechSquareSum (leechBasisMatrix *ᵥ z) = 32) :
    leechSquareSum (leechBasisMatrix *ᵥ (monsterNortonUIntegralAction *ᵥ z)) = 32 :=
  monsterNortonIntegralAction_short_norm monsterNortonUFiber _
    monsterNortonUIntegralAction_basis z hn

/-- The complete actual source Norton u has this actual binary action on every coordinate lift. -/
theorem monsterNortonUIntegralAction_Q_binary (z : Fin 24 → ℤ) :
    toAdd (monsterNortonUQImage (monsterNortonCoordinateQ z)).base =
      leechHyperbolicInverse *ᵥ integerParity (monsterNortonUIntegralAction *ᵥ z) := by
  rw [← monsterNortonUQImage_eq]
  exact monsterNortonIntegralAction_Q_binary monsterNortonUFiber _
    monsterNortonUIntegralAction_basis z

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
