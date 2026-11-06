/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayDodecads
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismOrder

/-! The actual label action and physical coordinate-zero stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual Golay automorphisms act on original coefficient labels. -/
def golayLabelActionHom : golayAutomorphismSubgroup →* Equiv.Perm (Fin 4096) where
  toFun := golayLabelPermutation
  map_one' := by
    apply Equiv.ext
    intro d
    apply golayLabelCoefficients_injective
    apply golayEncoder_injective
    rw [golayLabelPermutation_word]
    rfl
  map_mul' p q := by
    apply Equiv.ext
    intro d
    apply golayLabelCoefficients_injective
    apply golayEncoder_injective
    change golayEncoder (golayLabelCoefficients (golayLabelPermutation (p * q) d)) =
      golayEncoder (golayLabelCoefficients
        (golayLabelPermutation p (golayLabelPermutation q d)))
    rw [golayLabelPermutation_word, golayLabelPermutation_word]
    change golayPermute (p.val * q.val) (golayEncoder (golayLabelCoefficients d)) = _
    rw [golayPermute_mul, golayLabelPermutation_word]

instance : MulAction golayAutomorphismSubgroup (Fin 4096) :=
  MulAction.compHom (Fin 4096) golayLabelActionHom

/-- The action is exactly the original coordinate-permutation label action. -/
theorem golayLabelAction_smul (p : golayAutomorphismSubgroup) (d : Fin 4096) :
    p • d = golayLabelPermutation p d := rfl

/-- The first point stabilizer fixes precisely physical coordinate zero. -/
theorem golayPointStabilizer_one_iff (p : golayAutomorphismSubgroup) :
    p ∈ golayPointStabilizer 1 ↔ p.val 0 = 0 := by
  constructor
  · intro hp
    exact hp 0 (by decide)
  · intro hp j hj
    have he : j = 0 := Fin.ext (by omega)
    subst j
    exact hp

/-- The actual coordinate-zero stabilizer has order 10200960. -/
theorem golayPointStabilizer_one_card : Nat.card (golayPointStabilizer 1) = 10200960 := by
  have hzero : golayPointStabilizer 0 = ⊤ := by
    ext p
    change (∀ j : Fin 7, j.val < 0 → p.val (golayBasePoints j) = golayBasePoints j) ↔ True
    constructor
    · intro _
      trivial
    · intro _ j hj
      omega
  have h := golayPointStabilizer_card_step (0 : Fin 7)
  change Nat.card (golayPointStabilizer 0) = 24 * Nat.card (golayPointStabilizer 1) at h
  rw [hzero, Subgroup.card_top, golayAutomorphism_card] at h
  omega

/-- Relabeling transports the actual dodecad outside-point condition. -/
theorem golayLabelPermutation_dodecad_outside (p : golayAutomorphismSubgroup)
    (d : Fin 4096) (i : Fin 24) :
    golayLabelPermutation p d ∈ golayDodecadsOutside (p.val i) ↔
      d ∈ golayDodecadsOutside i := by
  simp only [golayDodecadsOutside, Finset.mem_filter, golayLabelPermutation_dodecad]
  have h := golayLabelPermutation_coordinate p d i
  have hv := congrArg ZMod.val h
  rw [golayLabelEncoder_match, golayLabelEncoder_match] at hv
  have he : (golayEncodedMask (golayLabelPermutation p d).val).testBit (p.val i).val =
      (golayEncodedMask d.val).testBit i.val := by
    cases ha : (golayEncodedMask (golayLabelPermutation p d).val).testBit (p.val i).val <;>
      cases hb : (golayEncodedMask d.val).testBit i.val <;> simp_all
  rw [he]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
