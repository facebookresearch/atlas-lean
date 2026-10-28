/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPermutationGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySignGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryGeneration

/-! Entire actual signed-anchor generation and the eleven genuine full-axis lift obligations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All six actual outside-coordinate images of the two genuine original source words. -/
def generatedTenthAxisLowerRecoveryOutsideForward : Fin 2 → Fin 6 → Fin 6 :=
  ![![3, 2, 4, 5, 1, 0], ![1, 4, 2, 3, 5, 0]]

/-- All six inverse outside-coordinate images, with their original ordering. -/
def generatedTenthAxisLowerRecoveryOutsideInverse : Fin 2 → Fin 6 → Fin 6 :=
  ![![5, 4, 1, 0, 2, 3], ![5, 0, 2, 3, 1, 4]]

private theorem outside_coordinates_injective :
    Function.Injective generatedTenthE7StandardOutsideCoordinates := by
  intro i j h
  apply generatedTenth_e7_standard_outside_point_bijective.injective
  exact Subtype.ext h

/-- The full original source words induce the specified entire outside-coordinate actions. -/
theorem generatedTenth_axis_lower_recovery_outside_actual (k : Fin 2) (i : Fin 6) :
    generatedTenthE7StandardOutsidePermutation
      (generatedTenthAxisLowerRecoveryFlagGenerator k) i =
        generatedTenthAxisLowerRecoveryOutsideForward k i := by
  apply outside_coordinates_injective
  rw [generatedTenth_e7_standard_outside_permutation_coordinate]
  change (generatedTenthAxisLowerRecoveryPermutation k).val
    (generatedTenthE7StandardOutsideCoordinates i) = _
  rw [generatedTenth_axis_lower_recovery_source_forward]
  have h : ∀ k : Fin 2, ∀ i : Fin 6,
      generatedTenthAxisLowerRecoveryPermutationForward k
        (generatedTenthE7StandardOutsideCoordinates i) =
      generatedTenthE7StandardOutsideCoordinates
        (generatedTenthAxisLowerRecoveryOutsideForward k i) := by
    decide +kernel
  exact h k i

/-- The complete inverse outside action is certified by the original forward source coordinates. -/
theorem generatedTenth_axis_lower_recovery_outside_inverse_actual (k : Fin 2) (i : Fin 6) :
    (generatedTenthE7StandardOutsidePermutation
      (generatedTenthAxisLowerRecoveryFlagGenerator k)).symm i =
        generatedTenthAxisLowerRecoveryOutsideInverse k i := by
  apply (generatedTenthE7StandardOutsidePermutation
    (generatedTenthAxisLowerRecoveryFlagGenerator k)).injective
  rw [Equiv.apply_symm_apply, generatedTenth_axis_lower_recovery_outside_actual]
  have h : ∀ k : Fin 2, ∀ i : Fin 6,
      generatedTenthAxisLowerRecoveryOutsideForward k
        (generatedTenthAxisLowerRecoveryOutsideInverse k i) = i := by decide +kernel
  exact (h k i).symm

/-- Both actual source code corrections satisfy the entire true signed permutation fiber. -/
theorem generatedTenth_axis_lower_recovery_permutation_code_valid : ∀ k : Fin 2,
    generatedTenthE7StandardTwistedSignCondition
      (generatedTenthE7SignedFlagPhase (generatedTenthAxisLowerRecoveryFlagGenerator k))
      (generatedTenthAxisLowerRecoveryCode
        (generatedTenthAxisLowerRecoveryPermutationCodeLabel k)) := by
  intro k
  unfold generatedTenthE7SignedFlagPhase
  simp only [generatedTenth_axis_lower_recovery_outside_inverse_actual]
  have h : ∀ k : Fin 2, generatedTenthE7StandardTwistedSignCondition
      (fun i => generatedTenthE7StandardOutsideSigns i +
        generatedTenthE7StandardOutsideSigns (generatedTenthAxisLowerRecoveryOutsideInverse k i))
      (generatedTenthAxisLowerRecoveryCode
        (generatedTenthAxisLowerRecoveryPermutationCodeLabel k)) := by
    unfold generatedTenthE7StandardTwistedSignCondition
    decide +kernel
  exact h k

/-- The two original code-corrected permutation generators are genuine full matrix/root fixers. -/
def generatedTenthAxisLowerRecoverySignedPermutationGenerator (k : Fin 2) :
    generatedTenthE7ActualAnchorStabilizer :=
  generatedTenthE7SignedAnchorEnumeration
    ⟨generatedTenthAxisLowerRecoveryFlagGenerator k,
      ⟨generatedTenthAxisLowerRecoveryCode (generatedTenthAxisLowerRecoveryPermutationCodeLabel k),
        generatedTenth_axis_lower_recovery_permutation_code_valid k⟩⟩

/-- The actual signed spatial generator whose full-axis lift is still a separate obligation. -/
def generatedTenthAxisLowerRecoverySignedPermutationSpatial (k : Fin 2) : leechIsomSubgroup :=
  golayMonomialPair
    (generatedTenthAxisLowerRecoveryCode (generatedTenthAxisLowerRecoveryPermutationCodeLabel k),
      generatedTenthAxisLowerRecoveryPermutation k)

/-- The exact original code accumulated by an arbitrary original source word. -/
def generatedTenthAxisLowerRecoveryWordCode : List (Fin 2) → golayCode
  | [] => 0
  | k :: w =>
      generatedTenthAxisLowerRecoveryCode (generatedTenthAxisLowerRecoveryPermutationCodeLabel k) +
        golayCodePermutation (generatedTenthAxisLowerRecoveryPermutation k)
          (generatedTenthAxisLowerRecoveryWordCode w)

private theorem sign_add (c d : golayCode) :
    golaySignIsometry (c + d) = golaySignIsometry c * golaySignIsometry d :=
  golaySignHom.map_mul (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)

/-- Every actual anchor word has precisely its original full spatial product. -/
theorem generatedTenth_axis_lower_recovery_signed_word_value (w : List (Fin 2)) :
    ((w.map generatedTenthAxisLowerRecoverySignedPermutationGenerator).prod).val.val =
      (w.map generatedTenthAxisLowerRecoverySignedPermutationSpatial).prod := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    simp only [List.map_cons, List.prod_cons]
    change generatedTenthAxisLowerRecoverySignedPermutationSpatial k *
      ((w.map generatedTenthAxisLowerRecoverySignedPermutationGenerator).prod).val.val = _
    rw [ih]

/-- The entire signed source word retains its actual original accumulated code and permutation. -/
theorem generatedTenth_axis_lower_recovery_signed_word_pair (w : List (Fin 2)) :
    (w.map generatedTenthAxisLowerRecoverySignedPermutationSpatial).prod =
      golayMonomialPair (generatedTenthAxisLowerRecoveryWordCode w,
        ((w.map generatedTenthAxisLowerRecoveryFlagGenerator).prod).val.val) := by
  induction w with
  | nil =>
    change 1 = golaySignIsometry (0 : golayCode) *
      golayPermutationIsometry (1 : golayAutomorphismSubgroup)
    rw [show golaySignIsometry (0 : golayCode) = 1 from golaySignHom.map_one,
      show golayPermutationIsometry (1 : golayAutomorphismSubgroup) = 1 from
        golayPermutationHom.map_one, one_mul]
  | cons k w ih =>
    simp only [List.map_cons, List.prod_cons, generatedTenthAxisLowerRecoveryWordCode]
    rw [ih]
    let c := generatedTenthAxisLowerRecoveryCode
      (generatedTenthAxisLowerRecoveryPermutationCodeLabel k)
    let d := generatedTenthAxisLowerRecoveryWordCode w
    let p := generatedTenthAxisLowerRecoveryPermutation k
    let q := ((w.map generatedTenthAxisLowerRecoveryFlagGenerator).prod).val.val
    change (golaySignIsometry c * golayPermutationIsometry p) *
      (golaySignIsometry d * golayPermutationIsometry q) =
        golaySignIsometry (c + golayCodePermutation p d) * golayPermutationIsometry (p * q)
    have hpq : golayPermutationIsometry (p * q) =
        golayPermutationIsometry p * golayPermutationIsometry q :=
      golayPermutationHom.map_mul p q
    calc
      _ = golaySignIsometry c *
          (golayPermutationIsometry p * golaySignIsometry d) *
            golayPermutationIsometry q := by simp only [mul_assoc]
      _ = golaySignIsometry c *
          (golaySignIsometry (golayCodePermutation p d) * golayPermutationIsometry p) *
            golayPermutationIsometry q := by rw [golayPermutation_sign_commute]
      _ = _ := by rw [sign_add, hpq]; simp only [mul_assoc]

/-- The difference of two genuine corrections for one actual permutation
is an actual kernel sign. -/
theorem generatedTenth_axis_lower_recovery_sign_difference
    (y : Fin 6 → ZMod 2) (c d : golayCode)
    (hc : generatedTenthE7StandardTwistedSignCondition y c)
    (hd : generatedTenthE7StandardTwistedSignCondition y d) :
    generatedTenthE7StandardTwistedSignCondition 0 (c - d) := by
  constructor
  · exact congrArg₂ (fun a b : ZMod 2 => a - b) hc.1 hd.1
  · intro i
    have hci := hc.2 i
    have hdi := hd.2 i
    change (c.val (generatedTenthE7StandardOutsideCoordinates i) -
      d.val (generatedTenthE7StandardOutsideCoordinates i)) + (0 : ZMod 2) =
        (c.val 14 - d.val 14) + 0
    linear_combination hci - hdi

/-- Seven original signs and two original corrected words generate the entire actual anchor.
This assertion concerns matrix/root fixers; full-axis lifts remain separate obligations. -/
theorem generatedTenth_axis_lower_recovery_signed_anchor_generation
    (P : Subgroup leechIsomSubgroup)
    (hbasis : ∀ k : Fin 7,
      golaySignIsometry (generatedTenthAxisLowerRecoveryCode
        (generatedTenthAxisLowerRecoverySignBasis k)) ∈ P)
    (hperm : ∀ k : Fin 2, generatedTenthAxisLowerRecoverySignedPermutationSpatial k ∈ P)
    (a : generatedTenthE7ActualAnchorStabilizer) : a.val.val ∈ P := by
  obtain ⟨v, rfl⟩ := generatedTenth_e7_signed_anchor_enumeration_surjective a
  obtain ⟨r, hr⟩ := generatedTenth_axis_lower_recovery_flag_word_surjective v.1
  let w := generatedTenthAxisLowerRecoveryTraversalWord r
  let b : generatedTenthE7ActualAnchorStabilizer :=
    (w.map generatedTenthAxisLowerRecoverySignedPermutationGenerator).prod
  have hbP : b.val.val ∈ P := by
    dsimp only [b]
    rw [generatedTenth_axis_lower_recovery_signed_word_value]
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hg
    exact hperm k
  have hbpair : b.val.val = golayMonomialPair
      (generatedTenthAxisLowerRecoveryWordCode w, v.1.val.val) := by
    dsimp only [b]
    rw [generatedTenth_axis_lower_recovery_signed_word_value,
      generatedTenth_axis_lower_recovery_signed_word_pair]
    change golayMonomialPair (_, (generatedTenthAxisLowerRecoveryFlagWord r).val.val) = _
    rw [hr]
  obtain ⟨u, hu⟩ := generatedTenth_e7_signed_anchor_enumeration_surjective b
  have hpairs : (u.2.val, u.1.val.val) =
      (generatedTenthAxisLowerRecoveryWordCode w, v.1.val.val) := by
    apply golayMonomialPair_injective
    exact (congrArg (fun x : generatedTenthE7ActualAnchorStabilizer => x.val.val) hu).trans hbpair
  have hup : u.1 = v.1 := Subtype.ext (Subtype.ext (congrArg Prod.snd hpairs))
  have huc : u.2.val = generatedTenthAxisLowerRecoveryWordCode w := congrArg Prod.fst hpairs
  have hd : generatedTenthE7StandardTwistedSignCondition (generatedTenthE7SignedFlagPhase v.1)
      (generatedTenthAxisLowerRecoveryWordCode w) := by
    have h : generatedTenthE7StandardTwistedSignCondition
        (generatedTenthE7SignedFlagPhase u.1) u.2.val := u.2.property
    rw [huc] at h
    rwa [hup] at h
  have hdiff := generatedTenth_axis_lower_recovery_sign_difference _ v.2.val _ v.2.property hd
  have hsign := generatedTenth_axis_lower_recovery_sign_generation P hbasis _ hdiff
  have h := P.mul_mem hsign hbP
  rw [hbpair] at h
  change golaySignIsometry (v.2.val - generatedTenthAxisLowerRecoveryWordCode w) *
    (golaySignIsometry (generatedTenthAxisLowerRecoveryWordCode w) *
      golayPermutationIsometry v.1.val.val) ∈ P at h
  rw [← mul_assoc, ← sign_add, sub_add_cancel] at h
  exact h

/-- The original Conway quotient value of a genuine standard-coordinate spatial map. -/
def generatedTenthAxisLowerRecoveryOriginalProjection : leechIsomSubgroup →* Co1 :=
  (QuotientGroup.mk' signsSubgroup).comp generatedTenthE7OrbitConjugation

/-- Eleven genuinely attained full-axis projections suffice for the exact local count.
No tensor fixation, source identity, or lift existence is assumed implicitly. -/
theorem generatedTenth_axis_lower_recovery_eleven_projection_values
    (hsigns : ∀ k : Fin 7, generatedTenthAxisLowerRecoveryOriginalProjection
      (golaySignIsometry (generatedTenthAxisLowerRecoveryCode
        (generatedTenthAxisLowerRecoverySignBasis k))) ∈ generatedTenthProjectedAxisStabilizer)
    (hperms : ∀ k : Fin 2, generatedTenthAxisLowerRecoveryOriginalProjection
      (generatedTenthAxisLowerRecoverySignedPermutationSpatial k) ∈
        generatedTenthProjectedAxisStabilizer)
    (hroots : ∀ k : Fin 2, generatedTenthAxisLowerRecoveryOriginalProjection
      (generatedTenthE7OrbitSpatialLetter k) ∈ generatedTenthProjectedAxisStabilizer) :
    Nat.card generatedTenthLocalAxisStabilizer = 2903040 := by
  let P := generatedTenthProjectedAxisStabilizer.comap
    generatedTenthAxisLowerRecoveryOriginalProjection
  apply generatedTenth_axis_lower_recovery_local_card
  · intro v
    exact generatedTenth_axis_lower_recovery_signed_anchor_generation P hsigns hperms
      (generatedTenthE7SignedAnchorEnumeration v)
  · exact hroots

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
