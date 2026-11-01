/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual short labels from certified norm32 lattice vectors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual short class of a certified norm32 vector in the genuine integral Leech basis. -/
noncomputable def monsterNortonShortClassOfCoordinates (z : Fin 24 → ℤ)
    (hn : leechSquareSum (leechBasisMatrix *ᵥ z) = 32) : LeechShortClasses :=
  ⟨leechReduction (leechExplicitCoordinateMap z), ⟨leechExplicitCoordinateMap z, rfl, hn⟩⟩

/-- Its genuine dictionary label is selected by the already proved short-class equivalence. -/
noncomputable def monsterNortonShortIndexOfCoordinates (z : Fin 24 → ℤ)
    (hn : leechSquareSum (leechBasisMatrix *ᵥ z) = 32) : GriessShortIndex :=
  griessShortClassEquiv.symm (monsterNortonShortClassOfCoordinates z hn)

/-- The actual dictionary class is exactly the certified lattice vector's class. -/
theorem monsterNortonShortIndexOfCoordinates_class (z : Fin 24 → ℤ)
    (hn : leechSquareSum (leechBasisMatrix *ᵥ z) = 32) :
    griessShortClass (monsterNortonShortIndexOfCoordinates z hn) =
      leechReduction (leechExplicitCoordinateMap z) := by
  exact congrArg Subtype.val
    (griessShortClassEquiv.apply_symm_apply (monsterNortonShortClassOfCoordinates z hn))

/-- The preferred actual Q lift has a computable formula in the certified integer coordinates. -/
theorem monsterNortonShortIndexOfCoordinates_Q (z : Fin 24 → ℤ)
    (hn : leechSquareSum (leechBasisMatrix *ᵥ z) = 32) :
    monsterNortonShortQ (monsterNortonShortIndexOfCoordinates z hn) =
      (⟨ofAdd (leechHyperbolicInverse *ᵥ integerParity z), 1⟩ : Q) := by
  rw [monsterNortonShortQ_eq]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change leechHyperbolicCoordinates
      (griessShortClass (monsterNortonShortIndexOfCoordinates z hn)) = _
    rw [monsterNortonShortIndexOfCoordinates_class, leechHyperbolicCoordinates_explicit]
    have hz : leechExplicitCoordinates (leechExplicitCoordinateMap z) = z :=
      leechExplicitCoordinates.apply_symm_apply z
    rw [hz]
    rfl
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
