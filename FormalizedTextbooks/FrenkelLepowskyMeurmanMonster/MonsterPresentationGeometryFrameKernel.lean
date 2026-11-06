/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact separation of the genuine source-local z subgroup from the remaining recognition kernel. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryFrameCentralMap

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual Q projection kernel lies in the literal binary projection kernel. -/
theorem monsterGeometryFrame_Q_ker_le_binary_ker :
    monsterGeometryFrameIntoQ.ker ≤ monsterGeometryFrameIntoBinary.ker := by
  intro x hx
  change qQuotHom (monsterGeometryFrameIntoQ x) = 1
  change monsterGeometryFrameIntoQ x = 1 at hx
  rw [hx, map_one]

/-- The remaining local recognition kernel meets the original source z subgroup trivially. -/
theorem monsterGeometryFrame_Z_inf_Q_ker :
    monsterGeometryFrameSourceZ ⊓ monsterGeometryFrameIntoQ.ker = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 1
  apply monsterGeometryFrameIntoQ_injective_on_central x 1 hx.1
    monsterGeometryFrameSourceZ.one_mem
  exact hx.2.trans (map_one monsterGeometryFrameIntoQ).symm

/-- Binary-trivial source-local elements are products of source z and the actual Q kernel. -/
theorem monsterGeometryFrame_binary_ker_le_Z_sup_Q_ker :
    monsterGeometryFrameIntoBinary.ker ≤
      monsterGeometryFrameSourceZ ⊔ monsterGeometryFrameIntoQ.ker := by
  have hl : monsterGeometryFrameSourceZ ≤
      monsterGeometryFrameSourceZ ⊔ monsterGeometryFrameIntoQ.ker := le_sup_left
  have hr : monsterGeometryFrameIntoQ.ker ≤
      monsterGeometryFrameSourceZ ⊔ monsterGeometryFrameIntoQ.ker := le_sup_right
  intro x hx
  have hc : monsterGeometryFrameIntoQ x ∈ centerQ := by
    rw [← qQuotHom_ker]
    exact hx
  by_cases he : monsterGeometryFrameIntoQ x = 1
  · exact hr he
  · have hz := qCentralInvolution_eq_of_mem_center_ne_one _ hc he
    have hk : monsterGeometryFrameSourceCentral⁻¹ * x ∈ monsterGeometryFrameIntoQ.ker := by
      change monsterGeometryFrameIntoQ (monsterGeometryFrameSourceCentral⁻¹ * x) = 1
      rw [map_mul, map_inv, monsterGeometryFrameIntoQ_central, hz, inv_mul_cancel]
    have hzmem : monsterGeometryFrameSourceCentral ∈
        monsterGeometryFrameSourceZ ⊔ monsterGeometryFrameIntoQ.ker :=
      hl (Subgroup.mem_zpowers _)
    have hm := (monsterGeometryFrameSourceZ ⊔ monsterGeometryFrameIntoQ.ker).mul_mem
      hzmem (hr hk)
    simpa only [mul_inv_cancel_left] using hm

/-- Exact binary kernel decomposition; the second factor is the still-open local source kernel. -/
theorem monsterGeometryFrame_binary_ker_eq_Z_sup_Q_ker :
    monsterGeometryFrameIntoBinary.ker =
      monsterGeometryFrameSourceZ ⊔ monsterGeometryFrameIntoQ.ker := by
  apply le_antisymm monsterGeometryFrame_binary_ker_le_Z_sup_Q_ker
  exact sup_le monsterGeometryFrameSourceZ_le_binary_ker
    monsterGeometryFrame_Q_ker_le_binary_ker

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
