/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100FaithfulAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechConcreteGeneration

/-! The actual positive-pair point stabilizer is the original Mathieu two-coordinate stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The original root and positive pair sum to the genuine distinguished frame vector. -/
theorem leechNormSixHS100Root_add_pair :
    leechNormSixHS100Root + leechNormSixHS100Pair = leechCoordinateFrameLattice 0 := by
  apply Subtype.ext
  funext i
  simp only [Submodule.coe_add, Pi.add_apply, leechNormSixHS100Root,
    leechNormSixHS100RootIntegral, leechNormSixHS100Pair, leechNormSixHS100PairIntegral,
    leechCoordinateFrameLattice, leechCoordinateFrameVector, Pi.single_apply]
  split_ifs <;> simp_all

/-- Original signed Golay permutations act by the original integral coordinate formula. -/
theorem leechNormSixHS100Monomial_action (d : golayCode) (p : golayAutomorphismSubgroup)
    (z : leechIntegral) :
    (leechIntegralAction (golayMonomialPair (d, p)) z).val =
      golayIntegerSign d.val (golayIntegerPermute p.val z.val) := by
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding]
  change golayRealSign d.val (golayRealPermute p.val (leechCoordinateEmbedding z.val)) = _
  rw [golayRealPermute_embedding, golayRealSign_embedding]

/-- Original unsigned Golay permutations have their actual integral coordinate action. -/
theorem leechNormSixHS100Permutation_action (p : golayAutomorphismSubgroup)
    (z : leechIntegral) :
    (leechIntegralAction (golayPermutationIsometry p) z).val =
      golayIntegerPermute p.val z.val := by
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding]
  exact golayRealPermute_embedding p.val z.val

/-- Membership in the original first-two-coordinate Mathieu stabilizer. -/
theorem leechNormSixHS100TwoCoordinates_mem (p : golayAutomorphismSubgroup) :
    p ∈ golayPointStabilizer 2 ↔ p.val 0 = 0 ∧ p.val 1 = 1 := by
  constructor
  · intro h
    exact ⟨by simpa [golayBasePoints] using h 0 (by decide),
      by simpa [golayBasePoints] using h 1 (by decide)⟩
  · rintro ⟨h0, h1⟩ j hj
    fin_cases j <;> simp_all [golayBasePoints]

/-- A signed monomial fixing the actual companion has no signs and fixes its distinguished coordinate. -/
theorem leechNormSixHS100Monomial_fix_companion (d : golayCode)
    (p : golayAutomorphismSubgroup)
    (hy : leechIntegralAction (golayMonomialPair (d, p)) leechNormSixHS100Companion =
      leechNormSixHS100Companion) : d = 0 ∧ p.val 0 = 0 := by
  have hc := congrArg Subtype.val hy
  rw [leechNormSixHS100Monomial_action] at hc
  have hd : d = 0 := by
    apply Subtype.ext
    funext i
    change d.val i = 0
    by_contra hi
    have hh := congrFun hc i
    simp only [golayIntegerSign, hi, ite_false, golayIntegerPermute,
      leechNormSixHS100Companion, leechNormSixHS100CompanionIntegral] at hh
    split_ifs at hh
  refine ⟨hd, ?_⟩
  have hh := congrFun hc 0
  rw [hd] at hh
  simp only [golayIntegerSign, ite_true, golayIntegerPermute,
    leechNormSixHS100Companion, leechNormSixHS100CompanionIntegral] at hh
  have hpre : p.val.symm 0 = 0 := by
    by_contra h
    norm_num [h] at hh
  exact ((p.val.symm_apply_eq).mp hpre).symm

/-- Fixing the actual root after fixing coordinate zero also fixes coordinate one. -/
theorem leechNormSixHS100Permutation_fix_root (p : golayAutomorphismSubgroup)
    (h0 : p.val 0 = 0)
    (hx : leechIntegralAction (golayPermutationIsometry p) leechNormSixHS100Root =
      leechNormSixHS100Root) : p.val 1 = 1 := by
  have hc := congrArg Subtype.val hx
  rw [leechNormSixHS100Permutation_action] at hc
  have hh := congrFun hc 1
  have hn : p.val.symm 1 ≠ 0 := by
    intro h
    have he := (p.val.symm_apply_eq).mp h
    rw [h0] at he
    exact (by decide : (1 : Fin 24) ≠ 0) he
  have hpre : p.val.symm 1 = 1 := by
    by_contra h
    norm_num [golayIntegerPermute, leechNormSixHS100Root,
      leechNormSixHS100RootIntegral, hn, h] at hh
  exact ((p.val.symm_apply_eq).mp hpre).symm

/-- Original permutations fixing zero and one fix all three complete flag vectors. -/
theorem leechNormSixHS100Permutation_fix_flag (p : golayAutomorphismSubgroup)
    (hp : p ∈ golayPointStabilizer 2) :
    leechIntegralAction (golayPermutationIsometry p) leechNormSixHS100Root = leechNormSixHS100Root ∧
    leechIntegralAction (golayPermutationIsometry p) leechNormSixHS100Companion =
      leechNormSixHS100Companion ∧
    leechIntegralAction (golayPermutationIsometry p) leechNormSixHS100Pair = leechNormSixHS100Pair := by
  obtain ⟨h0, h1⟩ := leechNormSixHS100TwoCoordinates_mem p |>.mp hp
  have hpre0 (i : Fin 24) : p.val.symm i = 0 ↔ i = 0 := by
    rw [Equiv.symm_apply_eq, h0]
  have hpre1 (i : Fin 24) : p.val.symm i = 1 ↔ i = 1 := by
    rw [Equiv.symm_apply_eq, h1]
  constructor
  · apply Subtype.ext
    rw [leechNormSixHS100Permutation_action]
    funext i
    simp only [golayIntegerPermute, leechNormSixHS100Root, leechNormSixHS100RootIntegral,
      hpre0, hpre1]
  constructor
  · apply Subtype.ext
    rw [leechNormSixHS100Permutation_action]
    funext i
    simp only [golayIntegerPermute, leechNormSixHS100Companion,
      leechNormSixHS100CompanionIntegral, hpre0]
  · apply Subtype.ext
    rw [leechNormSixHS100Permutation_action]
    funext i
    simp only [golayIntegerPermute, leechNormSixHS100Pair, leechNormSixHS100PairIntegral,
      hpre0, hpre1]

/-- Fixing the three actual vectors is exactly an original Mathieu permutation fixing zero and one. -/
theorem leechNormSixHS100Triple_fix_iff (g : leechIsomSubgroup) :
    (leechIntegralAction g leechNormSixHS100Root = leechNormSixHS100Root ∧
     leechIntegralAction g leechNormSixHS100Companion = leechNormSixHS100Companion ∧
     leechIntegralAction g leechNormSixHS100Pair = leechNormSixHS100Pair) ↔
    ∃ p : golayPointStabilizer 2, g = golayPermutationIsometry p.val := by
  constructor
  · rintro ⟨hx, hy, hz⟩
    have hf : leechIntegralAction g (leechCoordinateFrameLattice 0) = leechCoordinateFrameLattice 0 := by
      rw [← leechNormSixHS100Root_add_pair, map_add, hx, hz]
    obtain ⟨d, p, hg⟩ := leech_fix_frame_mem_monomial g hf
    have hyg : leechIntegralAction (golayMonomialPair (d, p)) leechNormSixHS100Companion =
        leechNormSixHS100Companion := by simpa only [golayMonomialPair, ← hg] using hy
    obtain ⟨hd, hp0⟩ := leechNormSixHS100Monomial_fix_companion d p hyg
    have hsign : golaySignIsometry (0 : golayCode) = 1 := golaySignHom.map_one
    rw [hd, hsign, one_mul] at hg
    have hp1 := leechNormSixHS100Permutation_fix_root p hp0 (by rw [← hg]; exact hx)
    exact ⟨⟨p, (leechNormSixHS100TwoCoordinates_mem p).mpr ⟨hp0, hp1⟩⟩, hg⟩
  · rintro ⟨p, rfl⟩
    exact leechNormSixHS100Permutation_fix_flag p.val p.property

/-- The concrete positive pair as a point of the complete original geometry. -/
def leechNormSixHS100PairPoint :
    LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion :=
  ⟨leechNormSixHS100Pair, leechNormSixHS100Pair_point⟩

/-- The actual point stabilizer inside the actual simultaneous flag stabilizer. -/
def leechNormSixHS100PairPointStabilizer :
    Subgroup (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion) :=
  MulAction.stabilizer _ leechNormSixHS100PairPoint

/-- The original Mathieu two-coordinate stabilizer maps into the actual point stabilizer. -/
def leechNormSixHS100PairPointHom :
    golayPointStabilizer 2 →* leechNormSixHS100PairPointStabilizer where
  toFun p :=
    let h := leechNormSixHS100Permutation_fix_flag p.val p.property
    ⟨⟨golayPermutationIsometry p.val,
      (leechNormSixActualPairStabilizer_mem _ _ _).mpr ⟨h.1, h.2.1⟩⟩, by
      apply Subtype.ext
      exact h.2.2⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact golayPermutationHom.map_one
  map_mul' p q := by
    apply Subtype.ext
    apply Subtype.ext
    exact golayPermutationHom.map_mul p.val q.val

/-- No two original Mathieu permutations induce the same original point-stabilizer map. -/
theorem leechNormSixHS100PairPointHom_injective :
    Function.Injective leechNormSixHS100PairPointHom := by
  intro p q h
  have he : golayPermutationIsometry p.val = golayPermutationIsometry q.val :=
    congrArg (fun g : leechNormSixHS100PairPointStabilizer => g.val.val) h
  have hm : golayMonomialPair (0, p.val) = golayMonomialPair (0, q.val) :=
    congrArg (fun g => golaySignIsometry (0 : golayCode) * g) he
  apply Subtype.ext
  exact congrArg Prod.snd (golayMonomialPair_injective hm)

/-- Every actual positive-pair point stabilizer is one of the original Mathieu permutations. -/
theorem leechNormSixHS100PairPointHom_surjective :
    Function.Surjective leechNormSixHS100PairPointHom := by
  intro g
  obtain ⟨hx, hy⟩ := (leechNormSixActualPairStabilizer_mem _ _ g.val.val).mp g.val.property
  have hz : leechIntegralAction g.val.val leechNormSixHS100Pair = leechNormSixHS100Pair :=
    congrArg Subtype.val g.property
  obtain ⟨p, hp⟩ := (leechNormSixHS100Triple_fix_iff g.val.val).mp ⟨hx, hy, hz⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hp.symm

/-- The actual positive-pair point stabilizer is isomorphic to the original Mathieu two-coordinate group. -/
def leechNormSixHS100PairPointEquiv :
    golayPointStabilizer 2 ≃* leechNormSixHS100PairPointStabilizer :=
  MulEquiv.ofBijective leechNormSixHS100PairPointHom
    ⟨leechNormSixHS100PairPointHom_injective, leechNormSixHS100PairPointHom_surjective⟩

/-- The complete actual two-coordinate group has the standard M22 order. -/
theorem leechNormSixHS100TwoCoordinates_card : Nat.card (golayPointStabilizer 2) = 443520 := by
  have h2 := golayPointStabilizer_card_step (2 : Fin 7)
  have h3 := golayPointStabilizer_card_step (3 : Fin 7)
  have h4 := golayPointStabilizer_card_step (4 : Fin 7)
  have h5 := golayPointStabilizer_card_step (5 : Fin 7)
  have h6 := golayPointStabilizer_card_step (6 : Fin 7)
  change Nat.card (golayPointStabilizer 2) = 22 * Nat.card (golayPointStabilizer 3) at h2
  change Nat.card (golayPointStabilizer 3) = 21 * Nat.card (golayPointStabilizer 4) at h3
  change Nat.card (golayPointStabilizer 4) = 20 * Nat.card (golayPointStabilizer 5) at h4
  change Nat.card (golayPointStabilizer 5) = 16 * Nat.card (golayPointStabilizer 6) at h5
  change Nat.card (golayPointStabilizer 6) = 3 * Nat.card (golayPointStabilizer 7) at h6
  rw [h2, h3, h4, h5, h6, golayPointStabilizer_seven]
  norm_num

/-- The actual point stabilizer in the faithful one-hundred-point geometry has443520 elements. -/
theorem leechNormSixHS100PairPointStabilizer_card :
    Nat.card leechNormSixHS100PairPointStabilizer = 443520 := by
  rw [← Nat.card_congr leechNormSixHS100PairPointEquiv.toEquiv,
    leechNormSixHS100TwoCoordinates_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
