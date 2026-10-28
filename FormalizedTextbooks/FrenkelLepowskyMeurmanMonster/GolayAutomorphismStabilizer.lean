/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismStabilizerOrbitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismBaseCertificate

/-! Actual Golay automorphisms from the checked stabilizer representative arrays.
The endpoint of the chain is proved trivial by the seven-point base certificate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Each certified array is an actual coordinate permutation. -/
def golayStabilizerPermutation (r : Fin 129) : Equiv.Perm (Fin 24) where
  toFun := golayStabilizerRepForward r
  invFun := golayStabilizerRepInverse r
  left_inv i := (golayStabilizerRep_inverse_certificate r i).2
  right_inv i := (golayStabilizerRep_inverse_certificate r i).1

private theorem golayLabel_boolean (d : Fin 4096) (i : Fin 24) :
    golayEncoder (golayLabelCoefficients d) i =
      golayBooleanCast ((golayEncodedMask d.val).testBit i.val) := by
  apply ZMod.val_injective 2
  rw [golayLabelEncoder_match]
  have h0 : (0 : ZMod 2).val = 0 := by decide
  have h1 : (1 : ZMod 2).val = 1 := by decide
  cases h : (golayEncodedMask d.val).testBit i.val <;>
    simp only [golayBooleanCast, Bool.false_eq_true, ite_false, ite_true, h0, h1]

private theorem golayGenerator_boolean (j : Fin 12) (i : Fin 24) :
    (golayGeneratorBit j i : ZMod 2) =
      golayBooleanCast ((golayGeneratorMasks j).testBit i.val) := by
  cases h : (golayGeneratorMasks j).testBit i.val <;>
    simp only [golayGeneratorBit, golayBooleanCast, h, Bool.false_eq_true,
      ite_false, ite_true, Int.cast_zero, Int.cast_one]

private def golayPermutationLinear (p : Equiv.Perm (Fin 24)) :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := golayPermute p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem golayPermutation_mem_of_generator_images (p : Equiv.Perm (Fin 24))
    (hp : ∀ j, golayPermute p (fun i => (golayGeneratorBit j i : ZMod 2)) ∈ golayCode)
    (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) : golayPermute p c ∈ golayCode := by
  obtain ⟨a, rfl⟩ := hc
  have ha : a = ∑ j, a j • (Pi.single j 1 : Fin 12 → ZMod 2) := by
    ext i
    simp [Pi.single_apply]
  change (golayPermutationLinear p).comp golayEncoder a ∈ golayCode
  rw [ha, map_sum]
  apply golayCode.sum_mem
  intro j _
  rw [map_smul]
  apply golayCode.smul_mem
  have hrow : golayEncoder (Pi.single j 1) = fun i => (golayGeneratorBit j i : ZMod 2) := by
    ext i
    simp [golayEncoder, Pi.single_apply, ite_mul]
  change golayPermute p (golayEncoder (Pi.single j 1)) ∈ golayCode
  rw [hrow]
  exact hp j

/-- All 129 checked representatives preserve the actual Golay code. -/
def golayStabilizerAutomorphism (r : Fin 129) : golayAutomorphismSubgroup :=
  ⟨golayStabilizerPermutation r, by
    have hf (j : Fin 12) :
        golayPermute (golayStabilizerPermutation r) (fun i => (golayGeneratorBit j i : ZMod 2)) =
          golayEncoder (golayLabelCoefficients (golayStabilizerRepForwardCodes r j)) := by
      ext i
      change (golayGeneratorBit j (golayStabilizerRepInverse r i) : ZMod 2) = _
      rw [golayGenerator_boolean, golayLabel_boolean,
        (golayStabilizerRep_code_certificate r j i).1]
    have hi (j : Fin 12) :
        golayPermute (golayStabilizerPermutation r)⁻¹ (fun i => (golayGeneratorBit j i : ZMod 2)) =
          golayEncoder (golayLabelCoefficients (golayStabilizerRepInverseCodes r j)) := by
      ext i
      change (golayGeneratorBit j (golayStabilizerRepForward r i) : ZMod 2) = _
      rw [golayGenerator_boolean, golayLabel_boolean,
        (golayStabilizerRep_code_certificate r j i).2]
    intro c
    constructor
    · intro hc
      exact golayPermutation_mem_of_generator_images _
        (fun j => by rw [hf]; exact ⟨_, rfl⟩) c hc
    · intro hc
      have h := golayPermutation_mem_of_generator_images (golayStabilizerPermutation r)⁻¹
        (fun j => by rw [hi]; exact ⟨_, rfl⟩) _ hc
      rw [golayPermute_inv] at h
      exact h⟩

/-- The actual subgroup fixing all base points preceding level `k`. -/
def golayPointStabilizer (k : ℕ) : Subgroup golayAutomorphismSubgroup where
  carrier := {p | ∀ j : Fin 7, j.val < k → p.val (golayBasePoints j) = golayBasePoints j}
  one_mem' _ _ := rfl
  mul_mem' := by
    intro p q hp hq j hj
    change p.val (q.val (golayBasePoints j)) = golayBasePoints j
    rw [hq j hj, hp j hj]
  inv_mem' := by
    intro p hp j hj
    change p.val.symm (golayBasePoints j) = golayBasePoints j
    have h := congrArg p.val.symm (hp j hj)
    rw [p.val.symm_apply_apply] at h
    exact h.symm

/-- The seventh stabilizer is genuinely trivial in the actual automorphism group. -/
theorem golayPointStabilizer_seven : golayPointStabilizer 7 = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro p hp
  exact golayAutomorphism_eq_one_of_fix_base p (fun j => hp j j.isLt)

/-- Every certified eligible image is reached by an actual member of its stabilizer. -/
theorem golayPointStabilizer_reaches (k : Fin 7) (i : Fin 24)
    (hi : golayStabilizerOrbitEligible k i) :
    ∃ p : golayPointStabilizer k.val, p.val.val (golayBasePoints k) = i := by
  obtain ⟨r, hr, hri⟩ := golayStabilizerRep_orbit_certificate k i hi
  refine ⟨⟨golayStabilizerAutomorphism r, ?_⟩, hri⟩
  intro j hj
  change golayStabilizerRepForward r (golayBasePoints j) = golayBasePoints j
  apply golayStabilizerRep_prefix_certificate
  simpa only [hr] using hj

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
