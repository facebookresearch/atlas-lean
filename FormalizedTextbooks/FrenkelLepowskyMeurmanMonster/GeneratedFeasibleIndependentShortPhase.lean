/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleTriplePhaseCharacters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationPhaseLift

/-! Genuine extraspecial sign correction in the simultaneous first-axis and
Omega stabilizer, with binary independence stated on the actual short bases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual commutator character is additive in its binary parameter. -/
theorem generatedFeasible_binary_phase_add (u v : Fin 24 → ZMod 2) :
    localAxisBinaryPhase (u + v) = localAxisBinaryPhase u * localAxisBinaryPhase v := by
  apply MonoidHom.ext
  intro q
  apply toAdd.injective
  change qBeta (toAdd q.base) (u + v) + qBeta (u + v) (toAdd q.base) =
    (qBeta (toAdd q.base) u + qBeta u (toAdd q.base)) +
      (qBeta (toAdd q.base) v + qBeta v (toAdd q.base))
  rw [qBeta_add_right, qBeta_add_left]
  abel

private theorem simultaneous_phase_mem (p : Fin 276) (q : Q)
    (hΩ : localOmegaQPhase q = 1) (hp : localAxisQPhase (Sum.inl (0, p)) q = 1) :
    inclQ q ∈ localAxisStabilizer p ⊓ localOmegaStabilizer := by
  constructor
  · change q ∈ (localAxisStabilizer p).comap inclQ
    rw [localAxisStabilizer_comap_inclQ, MonoidHom.mem_ker]
    exact hp
  · have hc : q ∈ Subgroup.centralizer {sourceOmegaQ} := by
      rw [← localOmegaQPhase_kernel_eq_centralizer, MonoidHom.mem_ker]
      exact hΩ
    change inclQ q ∈ Subgroup.centralizer {inclQ sourceOmegaQ}
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← map_mul, ← map_mul]
    exact congrArg inclQ (Subgroup.mem_centralizer_singleton_iff.mp hc)

/-- Any sign on a short base outside the first/Omega binary plane is realized
by an actual Q element that fixes both the first axis and Omega. -/
theorem generatedFeasible_independent_short_phase (p : Fin 276) (r : GriessShortIndex)
    (hfirst : (griessShortQ r).base ≠ (griessShortQ (Sum.inl (0, p))).base)
    (hsum : toAdd (griessShortQ r).base ≠
      toAdd sourceOmegaQ.base + toAdd (griessShortQ (Sum.inl (0, p))).base)
    (δ : ZMod 2) :
    ∃ q : Q, inclQ q ∈ localAxisStabilizer p ⊓ localOmegaStabilizer ∧
      localShortPhase (localFiberIncl q) r = δ := by
  have hne (s : GriessShortIndex) : localAxisQPhase s ≠ localOmegaQPhase := by
    intro he
    have hb := generatedAxis_binary_phase_injective he
    exact generatedAxis_short_base_ne_omega s (toAdd.injective hb)
  have hrf : localAxisQPhase r ≠ localAxisQPhase (Sum.inl (0, p)) := by
    intro he
    have hb := generatedAxis_binary_phase_injective he
    exact hfirst (toAdd.injective hb)
  have hrprod : localAxisQPhase r ≠ localOmegaQPhase * localAxisQPhase (Sum.inl (0, p)) := by
    intro he
    have hb : localAxisBinaryPhase (toAdd (griessShortQ r).base) =
        localAxisBinaryPhase
          (toAdd sourceOmegaQ.base + toAdd (griessShortQ (Sum.inl (0, p))).base) := by
      rw [generatedFeasible_binary_phase_add]
      exact he
    exact hsum (generatedAxis_binary_phase_injective hb)
  obtain ⟨q, hΩ, hp, hr⟩ := generatedFeasible_three_characters_kernel
    localOmegaQPhase (localAxisQPhase (Sum.inl (0, p))) (localAxisQPhase r)
    localOmegaQPhase_surjective (localAxisQPhase_surjective _) (localAxisQPhase_surjective r)
    (hne _) (hne r) hrf hrprod
  have hbit : δ = 0 ∨ δ = 1 := by
    have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact hc δ
  rcases hbit with rfl | rfl
  · refine ⟨1, ?_, ?_⟩
    · simpa only [map_one] using (localAxisStabilizer p ⊓ localOmegaStabilizer).one_mem
    · rw [localAxisQPhase_eq_short_phase, map_one]
      rfl
  · refine ⟨q, simultaneous_phase_mem p q hΩ hp, ?_⟩
    rw [localAxisQPhase_eq_short_phase, hr]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
