/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Each source code-basis sign matrix is bound to the actual Conway lattice action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignIntegralCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignBinaryCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBaseStabilizer

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual sign isometries act by their literal physical diagonal integer matrices. -/
theorem monsterCo1GeometrySign_embedding (k : Fin 12) (u : Fin 24 → ℤ) :
    (monsterCo1GeometrySignIsometry k).val (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding (monsterCo1GeometrySignPhysical k *ᵥ u) := by
  ext i
  simp [monsterCo1GeometrySignIsometry, monsterCo1GeometrySignCode,
    golaySignIsometry, golayRealSign_apply, leechCoordinateEmbedding,
    monsterCo1GeometrySignPhysical, Matrix.mulVec, dotProduct, qSign, ite_mul]
  all_goals split_ifs <;> simp [neg_div]

/-- The complete checked integral sign matrices are the actual lattice basis actions. -/
theorem monsterCo1GeometrySign_basis (k : Fin 12) (u : Fin 24 → ℤ) :
    (monsterCo1GeometrySignIsometry k).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ u)) =
    leechCoordinateEmbedding (leechBasisMatrix *ᵥ
      (monsterCo1GeometrySignIntegral k *ᵥ u)) := by
  rw [monsterCo1GeometrySign_embedding, Matrix.mulVec_mulVec,
    monsterCo1GeometrySignIntegral_certificate, ← Matrix.mulVec_mulVec]

/-- The displayed binary matrices therefore act through genuine Conway lattice classes. -/
theorem monsterCo1GeometrySign_binary (k : Fin 12) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (QuotientGroup.mk (monsterCo1GeometrySignIsometry k)) v =
      monsterCo1GeometrySignBinary k *ᵥ v := by
  change leechBinaryAction (monsterCo1GeometrySignIsometry k) v = _
  rw [leechBinaryAction_of_basis_certificate _ _ (monsterCo1GeometrySign_basis k),
    ← monsterCo1GeometrySignBinary_certificate]

/-- Each actual code-basis sign class belongs to the intrinsic full base-point two-core. -/
theorem monsterCo1GeometrySign_mem_baseTwoCore (k : Fin 12) :
    QuotientGroup.mk (monsterCo1GeometrySignIsometry k) ∈
      monsterCo1GeometryPointTwoCore monsterCo1GeometryBasePoint := by
  rw [monsterCo1GeometryBasePoint_twoCore]
  refine ⟨Multiplicative.ofAdd (monsterCo1GeometrySignCode k), ?_⟩
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
