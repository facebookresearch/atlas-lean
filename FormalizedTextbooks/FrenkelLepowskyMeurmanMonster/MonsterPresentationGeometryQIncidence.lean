/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Conjugator independence of the actual extraspecial Q-incidence condition. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryPoints
public import Mathlib.Tactic.Group

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual local centralizer normalizes its embedded extraspecial subgroup, using the
proved exact kernel of the local projection. -/
theorem monsterGeometryLocal_conjugate_Q (h : H) (x : Q) :
    ∃ y : Q, localIntoGenerated h * qIntoGenerated x * (localIntoGenerated h)⁻¹ =
      qIntoGenerated y := by
  have hm : h * inclQ x * h⁻¹ ∈ inclQ.range := by
    rw [inclQ_range_eq_projH_ker]
    have hx : inclQ x ∈ projH.ker := projH_inclQ x
    exact (inferInstance : projH.ker.Normal).conj_mem _ hx h
  obtain ⟨y, hy⟩ := hm
  refine ⟨y, ?_⟩
  have he := congrArg localIntoGenerated hy
  simpa only [map_mul, map_inv, qIntoGenerated, MonoidHom.comp_apply] using he.symm

/-- Any actual element centralizing the distinguished involution normalizes embedded Q. -/
theorem monsterGeometryCentralizer_conjugate_Q (h : G)
    (hh : h ∈ Subgroup.centralizer {generatedCentralInvolution}) (x : Q) :
    ∃ y : Q, h * qIntoGenerated x * h⁻¹ = qIntoGenerated y := by
  have hl : h ∈ localIntoGenerated.range := generatedCentralizer_eq_local_range.le hh
  obtain ⟨k, rfl⟩ := hl
  exact monsterGeometryLocal_conjugate_Q k x

/-- Q-incidence can be tested with any chosen actual conjugator for its first point.
Thus the existential point definition does not enlarge the source Q(p). -/
theorem monsterGeometryQIncident_iff_of_conjugator (p q : MonsterGeometryPoint) (g : G)
    (hg : g * generatedCentralInvolution * g⁻¹ = p.val) :
    monsterGeometryQIncident p q ↔
      ∃ x : Q, g * qIntoGenerated x * g⁻¹ = q.val := by
  constructor
  · rintro ⟨k, hk, x, hx⟩
    have hc : g⁻¹ * k ∈ Subgroup.centralizer {generatedCentralInvolution} := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      symm
      calc
        generatedCentralInvolution * (g⁻¹ * k) =
            g⁻¹ * (g * generatedCentralInvolution * g⁻¹) * k := by group
        _ = g⁻¹ * (k * generatedCentralInvolution * k⁻¹) * k := by rw [hg, hk]
        _ = (g⁻¹ * k) * generatedCentralInvolution := by group
    obtain ⟨y, hy⟩ := monsterGeometryCentralizer_conjugate_Q (g⁻¹ * k) hc x
    refine ⟨y, ?_⟩
    calc
      g * qIntoGenerated y * g⁻¹ =
          g * ((g⁻¹ * k) * qIntoGenerated x * (g⁻¹ * k)⁻¹) * g⁻¹ := by rw [hy]
      _ = k * qIntoGenerated x * k⁻¹ := by group
      _ = q.val := hx
  · rintro ⟨x, hx⟩
    exact ⟨g, hg, x, hx⟩

/-- Each source point belongs to its own actual conjugated extraspecial subgroup. -/
theorem monsterGeometryQIncident_self (p : MonsterGeometryPoint) :
    monsterGeometryQIncident p p := by
  obtain ⟨g, hg⟩ := isConj_iff.mp p.property
  exact ⟨g, hg, qCentralInvolution, hg⟩

/-- Source Q-incidence implies actual commutation, by the embedded local centralizer. -/
theorem monsterGeometryQIncident_commute (p q : MonsterGeometryPoint)
    (h : monsterGeometryQIncident p q) : p.val * q.val = q.val * p.val := by
  obtain ⟨g, hp, x, hq⟩ := h
  have hx : qIntoGenerated x ∈ Subgroup.centralizer {generatedCentralInvolution} :=
    localIntoGenerated_range_le_centralizer ⟨inclQ x, rfl⟩
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hx
  rw [← hp, ← hq]
  calc
    (g * generatedCentralInvolution * g⁻¹) * (g * qIntoGenerated x * g⁻¹) =
        g * (generatedCentralInvolution * qIntoGenerated x) * g⁻¹ := by group
    _ = g * (qIntoGenerated x * generatedCentralInvolution) * g⁻¹ := by rw [hc]
    _ = (g * qIntoGenerated x * g⁻¹) * (g * generatedCentralInvolution * g⁻¹) := by group

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
