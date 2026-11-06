/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Conjugation covariance forces genuine Singer-triality commutator checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerSourceAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenCocode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Two exact conjugation dictionaries give a full commutator centralization check. -/
theorem monsterNortonSinger_commutator_commutes_of_covariance
    {K : Type*} [Group K] (p e x x' : K)
    (hx : p * x * p⁻¹ = x')
    (hy : p * (e * x * e⁻¹) * p⁻¹ = e * x' * e⁻¹) :
    Commute (p⁻¹ * e⁻¹ * p * e) x := by
  have h : (p⁻¹ * e⁻¹ * p * e) * x * (p⁻¹ * e⁻¹ * p * e)⁻¹ = x := by
    calc
      _ = p⁻¹ * e⁻¹ * (p * (e * x * e⁻¹) * p⁻¹) * e * p := by group
      _ = p⁻¹ * e⁻¹ * (e * x' * e⁻¹) * e * p := by rw [hy]
      _ = p⁻¹ * x' * p := by group
      _ = x := by rw [← hx]; group
  exact mul_inv_eq_iff_eq_mul.mp h

/-- An element and its exact permutation image commuting with triality give a check. -/
theorem monsterNortonSinger_commutator_commutes_of_triality_commutation
    {K : Type*} [Group K] (p e x x' : K)
    (hx : p * x * p⁻¹ = x') (he : Commute x e) (he' : Commute x' e) :
    Commute (p⁻¹ * e⁻¹ * p * e) x := by
  apply monsterNortonSinger_commutator_commutes_of_covariance p e x x' hx
  have h : e * x * e⁻¹ = x := by
    rw [he.symm.eq]
    group
  have h' : e * x' * e⁻¹ = x' := by
    rw [he'.symm.eq]
    group
  rw [h, h']
  exact hx

/-- The forward actual Singer lift acts on every actual Q element by its proved spin image. -/
theorem monsterNortonSingerLocal_generated_conjugate_Q (q : Q) :
    localIntoGenerated monsterNortonSingerLocal * qIntoGenerated q *
      (localIntoGenerated monsterNortonSingerLocal)⁻¹ =
        qIntoGenerated (monsterNortonSingerImage q) := by
  have h := monsterFiberGenerated_conjugate_Q monsterNortonSingerFiber q
  change _ = qIntoGenerated (spinConjugation monsterNortonSingerSpin q) at h
  rw [monsterNortonSingerSpin_conjugation] at h
  exact h

/-- The genuine Singer lift fixes the full preferred all-one Q element. -/
theorem monsterNortonSingerOmega_certificate :
    monsterNortonSingerImage sourceOmegaQ = sourceOmegaQ := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    change (fun j : Fin 24 => Multiplicative.toAdd
      (monsterNortonSingerImage sourceOmegaQ).base j) =
      (fun j : Fin 24 => Multiplicative.toAdd sourceOmegaQ.base j)
    decide +kernel
  · rfl

/-- The actual source central sign is also fixed with its full coefficient. -/
theorem monsterNortonSingerCentral_certificate :
    monsterNortonSingerImage qCentralInvolution = qCentralInvolution := by
  rw [← monsterNortonSingerSpin_conjugation]
  exact spinConjugation_central monsterNortonSingerSpin 1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
