/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionCo1FrameOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalOrbit

/-! The actual source Ω centralizer projection in the local group. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual local centralizer of the actual source Ω element. -/
noncomputable def localOmegaStabilizer : Subgroup H :=
  Subgroup.centralizer {inclQ sourceOmegaQ}

/-- Fiber commutation with Ω is exactly commutation in the faithful Q inclusion. -/
theorem localOmegaStabilizer_fiber_iff (f : localFiberSubgroup) :
    localFiberIntoH f ∈ localOmegaStabilizer ↔ spinConjugation f.val.1 sourceOmegaQ =
      sourceOmegaQ := by
  rw [localOmegaStabilizer, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply inclQ_injective
    rw [inclQ_spinConjugation, h, mul_assoc, mul_inv_cancel, mul_one]
  · intro h
    have hh := congrArg inclQ h
    rw [inclQ_spinConjugation] at hh
    calc
      localFiberIntoH f * inclQ sourceOmegaQ =
          (localFiberIntoH f * inclQ sourceOmegaQ * (localFiberIntoH f)⁻¹) *
            localFiberIntoH f := by group
      _ = inclQ sourceOmegaQ * localFiberIntoH f := by rw [hh]

/-- Fixing actual Ω fixes its actual Conway quotient class. -/
theorem localOmegaStabilizer_projection_mem (h : localOmegaStabilizer) :
    projH h.val ∈ co1OmegaFrameStabilizer := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hmem : localFiberIntoH f ∈ localOmegaStabilizer := hf ▸ h.property
  have hc := (localOmegaStabilizer_fiber_iff f).mp hmem
  have hb := congrArg (fun q : Q => toAdd (qQuotHom q)) hc
  have ha := qBinaryAction_apply (spinConjugation f.val.1) sourceOmegaQ
  change spinBinaryAction f.val.1 (toAdd (qQuotHom sourceOmegaQ)) = _ at ha
  rw [f.property] at ha
  rw [← hf]
  change leechBinaryAction f.val.2 (toAdd (qQuotHom sourceOmegaQ)) =
    toAdd (qQuotHom sourceOmegaQ)
  exact ha.trans hb

/-- Restriction of the actual local projection to the actual Ω centralizer. -/
noncomputable def localOmegaProjection : localOmegaStabilizer →* co1OmegaFrameStabilizer :=
  (projH.comp localOmegaStabilizer.subtype).codRestrict _ localOmegaStabilizer_projection_mem

/-- The actual Q intersection is precisely the source Ω phase kernel. -/
theorem localOmegaStabilizer_comap_inclQ :
    localOmegaStabilizer.comap inclQ = localOmegaQPhase.ker := by
  rw [localOmegaQPhase_kernel_eq_centralizer]
  ext q
  change inclQ q ∈ Subgroup.centralizer {inclQ sourceOmegaQ} ↔
    q ∈ Subgroup.centralizer {sourceOmegaQ}
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    ← map_mul, ← map_mul, inclQ_injective.eq_iff]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
