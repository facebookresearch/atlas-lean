/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual central-corrected Q normal forms for all Norton point/line Coxeter words. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeCube

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The full Q coefficient obtained by normalizing a point/line word.
It retains the spin conjugation's actual central correction. -/
noncomputable def monsterNortonPointLineQ (i : Fin 13) (p : Q) : Q :=
  spinConjugation (monsterNortonUFiber ^ i.val).val.1 (y555NortonVQ * p) * y555NortonVQ

/-- Its generated image is the exact local conjugation word. -/
theorem monsterNortonPointLineQ_generated (i : Fin 13) (p : Q) :
    qIntoGenerated (monsterNortonPointLineQ i p) =
      y555NortonActualU ^ i.val * (y555NortonV * qIntoGenerated p) *
        (y555NortonActualU ^ i.val)⁻¹ * y555NortonV := by
  have hf : localIntoGenerated
      (QuotientGroup.mk' localDiagonalSubgroup (monsterNortonUFiber ^ i.val)) =
      y555NortonActualU ^ i.val := by
    rw [map_pow, map_pow]
    exact congrArg (fun u : ↥G => u ^ i.val) monsterNortonULocal_generated
  have h := monsterFiberGenerated_conjugate_Q (monsterNortonUFiber ^ i.val)
    (y555NortonVQ * p)
  rw [hf, map_mul] at h
  unfold monsterNortonPointLineQ
  rw [map_mul, ← h]
  rfl

/-- Every point/line word is conjugate to one actual Q coefficient times source triality. -/
theorem monsterNortonPointLineQ_normal_form (i : Fin 13) (p : Q) :
    (y555NortonActualU ^ i.val * y555NortonV) *
      (qIntoGenerated p * (y555NortonLine monsterSourceTriality i)⁻¹) *
      (y555NortonActualU ^ i.val * y555NortonV)⁻¹ =
      qIntoGenerated (monsterNortonPointLineQ i p) * monsterSourceTriality := by
  have hv : y555NortonV⁻¹ = y555NortonV := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two, y555NortonV_square]
  rw [monsterNortonPointLineQ_generated]
  unfold y555NortonLine y555NortonConjugate
  change (y555NortonActualU ^ i.val * y555NortonV) *
      (qIntoGenerated p *
        (y555NortonV * ((y555NortonActualU ^ i.val)⁻¹ *
          (y555NortonV * monsterSourceTriality) * y555NortonActualU ^ i.val)⁻¹)⁻¹) *
      (y555NortonActualU ^ i.val * y555NortonV)⁻¹ = _
  have hv2 : y555NortonV⁻¹ * y555NortonV⁻¹ = 1 := by
    rw [hv, ← pow_two, y555NortonV_square]
  simp only [mul_inv_rev, inv_inv]
  calc
    _ = y555NortonActualU ^ i.val * y555NortonV * qIntoGenerated p *
      (y555NortonActualU ^ i.val)⁻¹ * y555NortonV * monsterSourceTriality *
      y555NortonActualU ^ i.val * (y555NortonV⁻¹ * y555NortonV⁻¹) *
      (y555NortonActualU ^ i.val)⁻¹ := by group
    _ = _ := by rw [hv2]; group


/-- All power checks for these words reduce to their concrete Q/triality normal forms. -/
theorem monsterNortonPointLineQ_pow_iff (i : Fin 13) (p : Q) (k : ℕ) :
    (qIntoGenerated p * (y555NortonLine monsterSourceTriality i)⁻¹) ^ k = 1 ↔
      (qIntoGenerated (monsterNortonPointLineQ i p) * monsterSourceTriality) ^ k = 1 := by
  let c := y555NortonActualU ^ i.val * y555NortonV
  have h := congrArg (fun u : ↥G => u ^ k) (monsterNortonPointLineQ_normal_form i p)
  rw [conj_pow] at h
  constructor
  · intro hw
    rw [← h, hw]
    simp
  · intro hw
    have hc : c * (qIntoGenerated p *
        (y555NortonLine monsterSourceTriality i)⁻¹) ^ k * c⁻¹ = 1 := h.trans hw
    apply (MulAut.conj c).injective
    change c * (qIntoGenerated p *
      (y555NortonLine monsterSourceTriality i)⁻¹) ^ k * c⁻¹ = c * 1 * c⁻¹
    simpa using hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
