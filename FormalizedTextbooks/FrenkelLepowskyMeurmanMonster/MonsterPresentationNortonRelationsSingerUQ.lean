/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full-phase coordinate certificates for the Singer permutation and the literal Norton U. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerUQData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The source permutation intertwines U with U cubed on every positive coordinate lift. -/
theorem monsterNortonSinger_U_coordinate_certificate (i : Fin 24) :
    monsterNortonSingerImage (monsterNortonUQGeneratorImage i) =
      monsterNortonUQFastImage (monsterNortonUQFastImage (monsterNortonUQFastImage
        (monsterNortonSingerImage (qCoordinateGenerator i)))) := by
  have h0 : monsterNortonUQFastImage (monsterNortonSingerUCoordinate 0 i) =
      monsterNortonSingerUCoordinate 1 i := by
    have hx : Fin.castAdd 1 (0 : Fin 3) = (0 : Fin 4) := by decide +kernel
    have hy : Fin.natAdd 1 (0 : Fin 3) = (1 : Fin 4) := by decide +kernel
    have h := monsterNortonSingerUCoordinate_step 0 i
    rw [hx, hy] at h
    exact h
  have h1 : monsterNortonUQFastImage (monsterNortonSingerUCoordinate 1 i) =
      monsterNortonSingerUCoordinate 2 i := by
    have hx : Fin.castAdd 1 (1 : Fin 3) = (1 : Fin 4) := by decide +kernel
    have hy : Fin.natAdd 1 (1 : Fin 3) = (2 : Fin 4) := by decide +kernel
    have h := monsterNortonSingerUCoordinate_step 1 i
    rw [hx, hy] at h
    exact h
  have h2 : monsterNortonUQFastImage (monsterNortonSingerUCoordinate 2 i) =
      monsterNortonSingerUCoordinate 3 i := by
    have hx : Fin.castAdd 1 (2 : Fin 3) = (2 : Fin 4) := by decide +kernel
    have hy : Fin.natAdd 1 (2 : Fin 3) = (3 : Fin 4) := by decide +kernel
    have h := monsterNortonSingerUCoordinate_step 2 i
    rw [hx, hy] at h
    exact h
  rw [monsterNortonSingerUCoordinate_initial, h0, h1, h2,
    monsterNortonSingerUCoordinate_target]

set_option maxRecDepth 10000 in
/-- The finite intertwining certificate holds for the actual spin conjugation maps. -/
theorem monsterNortonSinger_U_conjugation_coordinates (i : Fin 24) :
    spinConjugation (monsterNortonSingerSpin * monsterNortonUFiber.val.1)
      (qCoordinateGenerator i) =
      spinConjugation (monsterNortonUFiber.val.1 * monsterNortonUFiber.val.1 *
        monsterNortonUFiber.val.1 * monsterNortonSingerSpin) (qCoordinateGenerator i) := by
  simp only [map_mul]
  change spinConjugation monsterNortonSingerSpin
      (spinConjugation monsterNortonUFiber.val.1 (qCoordinateGenerator i)) =
    spinConjugation monsterNortonUFiber.val.1
      (spinConjugation monsterNortonUFiber.val.1
        (spinConjugation monsterNortonUFiber.val.1
          (spinConjugation monsterNortonSingerSpin (qCoordinateGenerator i))))
  simp only [monsterNortonSingerSpin_conjugation]
  rw [monsterNortonUQImage_eq, monsterNortonUQGeneratorImage_certificate]
  simp only [monsterNortonUQImage_eq, monsterNortonUQFastImage_eq]
  exact monsterNortonSinger_U_coordinate_certificate i

/-- The finite coordinate certificate intertwines actual spin conjugation on all of Q. -/
theorem monsterNortonSinger_U_conjugation :
    spinConjugation (monsterNortonSingerSpin * monsterNortonUFiber.val.1) =
      spinConjugation (monsterNortonUFiber.val.1 * monsterNortonUFiber.val.1 *
        monsterNortonUFiber.val.1 * monsterNortonSingerSpin) := by
  let images : Fin 24 → Q := fun i =>
    spinConjugation (monsterNortonSingerSpin * monsterNortonUFiber.val.1)
      (qCoordinateGenerator i)
  apply DFunLike.ext
  intro q
  rw [monsterNortonCoordinateEvaluation_eq _ images (fun _ => rfl),
    monsterNortonCoordinateEvaluation_eq _ images
      (fun i => (monsterNortonSinger_U_conjugation_coordinates i).symm)]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
