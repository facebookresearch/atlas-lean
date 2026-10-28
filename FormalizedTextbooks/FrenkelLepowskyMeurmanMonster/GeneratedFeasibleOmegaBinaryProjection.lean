/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOmegaConjugacy
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOmegaPhase

/-! The actual simultaneous short-class and Ω-class stabilizer in Co₂. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine Co₂ subgroup fixing the actual binary Ω class. -/
def generatedFeasibleOmegaBinaryStabilizer (p : Fin 276) :
    Subgroup (co2ShortStabilizer (Sum.inl (0, p))) :=
  co1OmegaFrameStabilizer.subgroupOf (co2ShortStabilizer (Sum.inl (0, p)))

/-- The genuine feasible transition subgroup projects into the actual binary stabilizer. -/
def generatedFeasibleOmegaBinaryProjection (p : Fin 276) :
    localFeasibleTransitionSubgroup p →* generatedFeasibleOmegaBinaryStabilizer p :=
  ((localAxisStabilizerProjection p).comp
    (localFeasibleTransitionSubgroup p).subtype).codRestrict _ (by
      intro n
      exact localOmegaStabilizer_projection_mem ⟨n.val.val, n.property⟩)

/-- Every genuine simultaneous binary stabilizer has a full lift fixing both actual elements.
The second phase correction takes place inside the full Ω centralizer. -/
theorem generatedFeasibleOmegaBinaryProjection_surjective (p : Fin 276) :
    Function.Surjective (generatedFeasibleOmegaBinaryProjection p) := by
  intro c
  let a : co1OmegaFrameStabilizer := ⟨c.val.val, c.property⟩
  obtain ⟨h, hh⟩ := localOmegaProjection_surjective a
  have hproj : projH h.val = c.val.val := congrArg Subtype.val hh
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hp : griessShortPermutation f.val.2 (Sum.inl (0, p)) = Sum.inl (0, p) := by
    have hc : co1ShortPermutation c.val.val (Sum.inl (0, p)) = Sum.inl (0, p) :=
      c.val.property
    rw [← hproj, ← hf, localAxis_projection_short_mk] at hc
    exact hc
  obtain ⟨q, hqOmega, hqPhase⟩ := generatedAxis_short_localOmega_phase (Sum.inl (0, p))
    (localShortPhase f (Sum.inl (0, p)))
  let k := localFiberIncl q * f
  have hkAxis : localFiberIntoH k ∈ localAxisStabilizer p := by
    rw [localAxisStabilizer_mk_iff]
    constructor
    · change griessShortPermutation (1 * f.val.2) (Sum.inl (0, p)) = _
      simpa only [one_mul] using hp
    · rw [localShortPhase_mul, hp, hqPhase]
      exact CharTwo.add_self_eq_zero _
  have hkOmega : localFiberIntoH k ∈ localOmegaStabilizer := by
    change inclQ q * localFiberIntoH f ∈ localOmegaStabilizer
    rw [hf]
    exact localOmegaStabilizer.mul_mem hqOmega h.property
  refine ⟨⟨⟨localFiberIntoH k, hkAxis⟩, hkOmega⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change projH (inclQ q * localFiberIntoH f) = c.val.val
  rw [map_mul, projH_inclQ, one_mul, hf, hproj]

/-- The actual phase kernel fixing both the first axis and Ω. -/
def generatedFeasibleOmegaBinaryPhaseKernel (p : Fin 276) :
    Subgroup (localAxisQPhase (Sum.inl (0, p))).ker :=
  localOmegaQPhase.ker.subgroupOf (localAxisQPhase (Sum.inl (0, p))).ker

/-- The genuine simultaneous phase kernel has exactly 2²³ elements. -/
theorem generatedFeasibleOmegaBinaryPhaseKernel_card (p : Fin 276) :
    Nat.card (generatedFeasibleOmegaBinaryPhaseKernel p) = 2 ^ 23 :=
  generatedFeasibleOmegaQPhase_kernel_card p

/-- The simultaneous actual phase kernel embeds in the genuine transition subgroup. -/
def generatedFeasibleOmegaBinaryPhaseInclusion (p : Fin 276) :
    generatedFeasibleOmegaBinaryPhaseKernel p →* localFeasibleTransitionSubgroup p :=
  ((localAxisPhaseInclusion p).comp
    (generatedFeasibleOmegaBinaryPhaseKernel p).subtype).codRestrict _ (by
      intro q
      change inclQ q.val.val ∈ localOmegaStabilizer
      change q.val.val ∈ localOmegaStabilizer.comap inclQ
      rw [localOmegaStabilizer_comap_inclQ]
      exact q.property)

/-- The original extraspecial inclusion remains faithful on the simultaneous phase kernel. -/
theorem generatedFeasibleOmegaBinaryPhaseInclusion_injective (p : Fin 276) :
    Function.Injective (generatedFeasibleOmegaBinaryPhaseInclusion p) := by
  intro q r he
  apply Subtype.ext
  apply Subtype.ext
  apply inclQ_injective
  exact congrArg (fun n : localFeasibleTransitionSubgroup p => n.val.val) he

/-- The genuine binary projection has precisely the actual simultaneous phase kernel. -/
theorem generatedFeasibleOmegaBinaryPhaseInclusion_range (p : Fin 276) :
    (generatedFeasibleOmegaBinaryPhaseInclusion p).range =
      (generatedFeasibleOmegaBinaryProjection p).ker := by
  ext n
  constructor
  · rintro ⟨q, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    exact projH_inclQ q.val.val
  · intro hn
    have hp : n.val.val ∈ projH.ker :=
      congrArg (fun c : generatedFeasibleOmegaBinaryStabilizer p => c.val.val) hn
    rw [← inclQ_range_eq_projH_ker] at hp
    obtain ⟨q, hq⟩ := hp
    have ha : q ∈ (localAxisQPhase (Sum.inl (0, p))).ker := by
      rw [← localAxisStabilizer_comap_inclQ]
      change inclQ q ∈ localAxisStabilizer p
      rw [hq]
      exact n.val.property
    have ho : q ∈ localOmegaQPhase.ker := by
      rw [← localOmegaStabilizer_comap_inclQ]
      change inclQ q ∈ localOmegaStabilizer
      rw [hq]
      exact n.property
    exact ⟨⟨⟨q, ha⟩, ho⟩, Subtype.ext (Subtype.ext hq)⟩

/-- The actual simultaneous binary projection has kernel order 2²³. -/
theorem generatedFeasibleOmegaBinaryProjection_kernel_card (p : Fin 276) :
    Nat.card (generatedFeasibleOmegaBinaryProjection p).ker = 2 ^ 23 := by
  rw [← generatedFeasibleOmegaBinaryPhaseInclusion_range]
  have h := Nat.card_congr (MonoidHom.ofInjective
    (generatedFeasibleOmegaBinaryPhaseInclusion_injective p)).toEquiv
  rw [← h]
  exact generatedFeasibleOmegaBinaryPhaseKernel_card p

/-- The entire actual Co₂ stabilizer of the binary Ω class has this exact order. -/
theorem generatedFeasibleOmegaBinaryStabilizer_card (p : Fin 276) :
    Nat.card (generatedFeasibleOmegaBinaryStabilizer p) = 908328960 := by
  have h := (generatedFeasibleOmegaBinaryProjection p).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr
    (generatedFeasibleOmegaBinaryProjection_surjective p), Subgroup.card_top,
    generatedFeasibleOmegaBinaryProjection_kernel_card,
    Nat.card_congr (localFeasibleTransitionEquiv p).toEquiv,
    localOmegaAxisIntersection_card] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2 ^ 23) h

/-- The actual binary Ω class has 46,575 cosets under the actual Co₂ group. -/
theorem generatedFeasibleOmegaBinaryStabilizer_index (p : Fin 276) :
    (generatedFeasibleOmegaBinaryStabilizer p).index = 46575 := by
  have h := (generatedFeasibleOmegaBinaryStabilizer p).card_mul_index
  rw [generatedFeasibleOmegaBinaryStabilizer_card, co2Short_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 908328960) h

/-- The actual Co₂ subgroup acts through its original Conway binary representation. -/
instance (priority := 2000) generatedFeasibleCo2BinaryAction (p : Fin 276) :
    MulAction (co2ShortStabilizer (Sum.inl (0, p))) (Fin 24 → ZMod 2) :=
  MulAction.compHom (Fin 24 → ZMod 2)
    (co1BinaryAction.comp (co2ShortStabilizer (Sum.inl (0, p))).subtype)

/-- The counted simultaneous binary subgroup is the full stabilizer in the actual action. -/
theorem generatedFeasibleOmegaBinary_stabilizer (p : Fin 276) :
    MulAction.stabilizer (co2ShortStabilizer (Sum.inl (0, p)))
      (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) =
      generatedFeasibleOmegaBinaryStabilizer p := rfl

/-- The genuine Co₂ orbit of Ω has 46,575 binary points, before its two full central signs. -/
theorem generatedFeasibleOmegaBinaryOrbit_card (p : Fin 276) :
    Nat.card (MulAction.orbit (co2ShortStabilizer (Sum.inl (0, p)))
      (Multiplicative.toAdd (qQuotHom sourceOmegaQ))) = 46575 := by
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer,
    generatedFeasibleOmegaBinary_stabilizer]
  exact generatedFeasibleOmegaBinaryStabilizer_index p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
