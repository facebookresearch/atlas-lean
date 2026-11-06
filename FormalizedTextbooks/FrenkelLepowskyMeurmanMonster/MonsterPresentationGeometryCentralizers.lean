/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual point centralizers are conjugates of the proved full distinguished centralizer. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryPoints

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The full actual centralizer of a source geometry point. -/
noncomputable def monsterGeometryPointCentralizer (p : MonsterGeometryPoint) : Subgroup G :=
  Subgroup.centralizer {p.val}

/-- A genuine chosen conjugator identifies actual full point centralizers. -/
noncomputable def monsterGeometryCentralizerConjugation (p : MonsterGeometryPoint) (g : G)
    (hg : g * generatedCentralInvolution * g⁻¹ = p.val) :
    generatedCentralizer ≃* monsterGeometryPointCentralizer p where
  toFun h := ⟨g * h.val * g⁻¹, by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    symm
    have hc : generatedCentralInvolution * h.val = h.val * generatedCentralInvolution :=
      (Subgroup.mem_centralizer_singleton_iff.mp h.property).symm
    rw [← hg]
    calc
      (g * generatedCentralInvolution * g⁻¹) * (g * h.val * g⁻¹) =
          g * (generatedCentralInvolution * h.val) * g⁻¹ := by group
      _ = g * (h.val * generatedCentralInvolution) * g⁻¹ := by rw [hc]
      _ = (g * h.val * g⁻¹) * (g * generatedCentralInvolution * g⁻¹) := by group⟩
  invFun h := ⟨g⁻¹ * h.val * g, by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    symm
    have hc : p.val * h.val = h.val * p.val :=
      (Subgroup.mem_centralizer_singleton_iff.mp h.property).symm
    change generatedCentralInvolution * (g⁻¹ * h.val * g) =
      (g⁻¹ * h.val * g) * generatedCentralInvolution
    calc
      generatedCentralInvolution * (g⁻¹ * h.val * g) =
          g⁻¹ * (p.val * h.val) * g := by rw [← hg]; group
      _ = g⁻¹ * (h.val * p.val) * g := by rw [hc]
      _ = (g⁻¹ * h.val * g) * generatedCentralInvolution := by rw [← hg]; group⟩
  left_inv h := by apply Subtype.ext; dsimp; group
  right_inv h := by apply Subtype.ext; dsimp; group
  map_mul' h k := by apply Subtype.ext; dsimp; group

/-- The centralizer isomorphism retains the literal actual conjugation value. -/
@[simp] theorem monsterGeometryCentralizerConjugation_value
    (p : MonsterGeometryPoint) (g : G) (hg) (h : generatedCentralizer) :
    (monsterGeometryCentralizerConjugation p g hg h).val = g * h.val * g⁻¹ := rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
