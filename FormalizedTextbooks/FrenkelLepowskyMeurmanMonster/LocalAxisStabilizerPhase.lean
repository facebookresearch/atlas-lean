/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalAxisStabilizerCoordinates

/-! The nontrivial extraspecial phase character of an actual short-vector lift.
Its kernel has order 2^24 by an ordinary finite exact-sequence count. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

/-- The hyperbolic binary conjugation character evaluated on a fixed vector. -/
def localAxisBinaryPhase (v : Fin 24 → ZMod 2) : Q →* Multiplicative (ZMod 2) where
  toFun q := ofAdd (qBeta (toAdd q.base) v +
    qBeta v (toAdd q.base))
  map_one' := by simp [qBeta_zero_left, qBeta_zero_right]
  map_mul' q k := by
    apply toAdd.injective
    change qBeta (toAdd q.base + toAdd k.base) v +
      qBeta v (toAdd q.base + toAdd k.base) = _
    rw [qBeta_add_left, qBeta_add_right]
    change _ = (qBeta (toAdd q.base) v +
      qBeta v (toAdd q.base)) +
      (qBeta (toAdd k.base) v +
      qBeta v (toAdd k.base))
    abel

/-- The conjugation phase on the actual preferred short lift. -/
noncomputable def localAxisQPhase (r : GriessShortIndex) : Q →* Multiplicative (ZMod 2) :=
  localAxisBinaryPhase (toAdd (griessShortQ r).base)

/-- The abstract conjugation character is exactly the implemented short-coordinate phase. -/
theorem localAxisQPhase_eq_short_phase (r : GriessShortIndex) (q : Q) :
    localShortPhase (localFiberIncl q) r = toAdd (localAxisQPhase r q) := by
  change toAdd (spinConjugation (spinHolomorphIncl q) (griessShortQ r)).coeff = _
  rw [spinConjugation_incl, q_conjugation_central_phase, qCentral_mul_coeff,
    griessShortQ_coeff, add_zero]
  rfl

/-- The short lift is noncentral, so its extraspecial conjugation phase is nontrivial. -/
theorem localAxisQPhase_nontrivial (r : GriessShortIndex) :
    ∃ q : Q, localAxisQPhase r q ≠ 1 := by
  by_contra! h
  have hc : griessShortQ r ∈ centerQ := by
    apply Subgroup.mem_center_iff.mpr
    intro q
    apply (q_mul_comm_iff q (griessShortQ r)).mpr
    have hz := congrArg toAdd (h q)
    change qBeta (toAdd q.base) (toAdd (griessShortQ r).base) +
      qBeta (toAdd (griessShortQ r).base) (toAdd q.base) = 0 at hz
    have hn : ∀ a : ZMod 2, -a = a := by decide
    simpa only [hn] using eq_neg_of_add_eq_zero_left hz
  exact griessShortQ_base_ne_one r ((q_mem_center_iff_base_eq_one _).mp hc)

/-- Every binary phase is realized by an actual extraspecial element. -/
theorem localAxisQPhase_surjective (r : GriessShortIndex) :
    Function.Surjective (localAxisQPhase r) := by
  obtain ⟨q, hq⟩ := localAxisQPhase_nontrivial r
  have hbit : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hq1 : toAdd (localAxisQPhase r q) = 1 := by
    rcases hbit (toAdd (localAxisQPhase r q)) with h | h
    · exact False.elim (hq (toAdd.injective h))
    · exact h
  intro a
  rcases hbit (toAdd a) with ha | ha
  · exact ⟨1, by rw [map_one]; exact (toAdd.injective ha).symm⟩
  · exact ⟨q, toAdd.injective (hq1.trans ha.symm)⟩

/-- Exactly half the actual extraspecial group fixes a given short-coordinate sign. -/
theorem localAxisQPhase_kernel_card (r : GriessShortIndex) :
    Nat.card (localAxisQPhase r).ker = 2 ^ 24 := by
  have h := (localAxisQPhase r).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (localAxisQPhase_surjective r),
    Subgroup.card_top, q_card] at h
  have hc : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp [ZMod.card]
  rw [hc] at h
  omega

/-- The actual Q intersection of the local axis stabilizer is the phase kernel. -/
theorem localAxisStabilizer_comap_inclQ (p : Fin 276) :
    (localAxisStabilizer p).comap inclQ = (localAxisQPhase (Sum.inl (0, p))).ker := by
  ext q
  change localFiberIntoH (localFiberIncl q) ∈ localAxisStabilizer p ↔ _
  rw [localAxisStabilizer_mk_iff, localAxisQPhase_eq_short_phase]
  have hp : griessShortPermutation (localFiberIncl q).val.2 (Sum.inl (0, p)) =
      Sum.inl (0, p) := by change griessShortPermutation 1 _ = _; rw [map_one]; rfl
  simp only [hp, true_and, MonoidHom.mem_ker]
  exact ⟨fun h => toAdd.injective h, fun h => congrArg toAdd h⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
