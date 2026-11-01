/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual all-Q normalization by the literal low-code source y words.
The proof uses the full actual tensor dictionary and the proved faithful local tensor action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsYSpinTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82SourceBinding

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem actual_q_tensor (q : Q) (x : GriessSpace) (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (rhoLocal (inclQ q) x)).2.2 t i =
      spinRepresentation q (fun u => (griessConwayEncode x).2.2 u i) t := by
  rw [show rhoLocal (inclQ q) = localGriessRepresentation (localFiberIncl q) from rfl,
    localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  exact localTensorRepresentation_q q (griessConwayEncode x).2.2 t i

private theorem explicit_y_intertwines (a : Fin 2048) (q : Q) (f : SpinSpace) :
    (monsterNortonYSpin a).val (spinRepresentation q f) =
      spinRepresentation (monsterNortonYImage a q) ((monsterNortonYSpin a).val f) := by
  rw [← monsterNortonYSpin_conjugation, spinConjugation_representation,
    LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    LinearEquiv.symm_apply_apply]

/-- The actual literal triality-conjugated source code normalizes every Q element
by the fully phase-correct explicit spin formula. -/
theorem monsterNortonYWord_conjugation (a : Fin 2048)
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (q : Q) :
    y555NortonActualY ⟨a.val, by omega⟩ 0 * qIntoGenerated q *
      (y555NortonActualY ⟨a.val, by omega⟩ 0)⁻¹ =
        qIntoGenerated (monsterNortonYImage a q) := by
  obtain ⟨h, hh⟩ := monsterSourceY_word_mem_local ⟨a.val, by omega⟩ 0
  have hρ : rhoLocal h =
      sExtra * rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) * sExtra⁻¹ := by
    rw [y555NortonActualY_word] at hh
    exact congrArg Subtype.val hh
  have hT (x : GriessSpace) (t : SpinIndex) (i : Fin 24) :
      (griessConwayEncode (rhoLocal h x)).2.2 t i =
        qSign (golayEncoder (monsterNortonYCode a) i) *
          (monsterNortonYSpin a).val (fun u => (griessConwayEncode x).2.2 u i) t := by
    rw [hρ]
    exact monsterNortonYWord_tensor a ha x t i
  have he : h * inclQ q = inclQ (monsterNortonYImage a q) * h := by
    apply monsterLocalTensor_identifies
    intro x
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    funext t i
    rw [hT, actual_q_tensor]
    have hq : (fun u => (griessConwayEncode (rhoLocal (inclQ q) x)).2.2 u i) =
        spinRepresentation q (fun u => (griessConwayEncode x).2.2 u i) := by
      funext u
      exact actual_q_tensor q x u i
    have hy : (fun u => (griessConwayEncode (rhoLocal h x)).2.2 u i) =
        qSign (golayEncoder (monsterNortonYCode a) i) •
          (monsterNortonYSpin a).val (fun u => (griessConwayEncode x).2.2 u i) := by
      funext u
      exact hT x u i
    rw [hq, hy, map_smul]
    change _ = qSign (golayEncoder (monsterNortonYCode a) i) * _
    rw [explicit_y_intertwines]
  have heG := congrArg localIntoGenerated he
  rw [map_mul, map_mul, hh] at heG
  change _ * qIntoGenerated q = qIntoGenerated (monsterNortonYImage a q) * _ at heG
  calc
    _ = (qIntoGenerated (monsterNortonYImage a q) *
      y555NortonActualY ⟨a.val, by omega⟩ 0) *
        (y555NortonActualY ⟨a.val, by omega⟩ 0)⁻¹ := by rw [heG]
    _ = _ := by group

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
