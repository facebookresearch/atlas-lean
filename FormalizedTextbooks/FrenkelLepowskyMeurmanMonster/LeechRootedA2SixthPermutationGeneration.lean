/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthPermutationTransport

/-! Three transported source generators and one root-pair swap
generate all actual flag permutations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The three actual source permutation generators transported to the physical sixth triple. -/
def leechRootedA2SixthPermutationGenerator (j : Fin 3) : golayAutomorphismSubgroup :=
  leechRootedA2SixthPermutationTransport * leechRootedA2ThreePointAutomorphism j *
    leechRootedA2SixthPermutationTransport⁻¹

private theorem transported_mem (B : golayAutomorphismSubgroup)
    (hb : B.val 0 = 16 ∧ B.val 1 = 17 ∧ B.val 2 = 19)
    (K : Subgroup golayAutomorphismSubgroup)
    (hK : ∀ j, B * leechRootedA2ThreePointAutomorphism j * B⁻¹ ∈ K)
    (p : golayAutomorphismSubgroup) (hp : p ∈ leechRootedA2SixthPermutationTriple) : p ∈ K := by
  let φ : golayAutomorphismSubgroup →* golayAutomorphismSubgroup :=
    (MulAut.conj B).toMonoidHom
  have h : leechRootedA2ThreePointSubgroup ≤ K.comap φ := by
    rw [leechRootedA2ThreePointSubgroup, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact hK j
  have hfix := (leechRootedA2SixthPermutationTriple_mem p).mp hp
  have hq : B⁻¹ * p * B ∈ golayPointStabilizer 3 := by
    intro k hk
    have hx : ∀ k : Fin 3, B.val (Fin.castAdd 21 k) = (![16, 17, 19] : Fin 3 → Fin 24) k := by
      intro k
      fin_cases k
      · exact hb.1
      · exact hb.2.1
      · exact hb.2.2
    let u : Fin 5 := ⟨k.val, by omega⟩
    have hu : Fin.castAdd 2 u = k := Fin.ext rfl
    have hkbase := golayBasePoints_firstFive u
    rw [hu] at hkbase
    let j : Fin 3 := ⟨k.val, hk⟩
    have hkbase' : golayBasePoints k = Fin.castAdd 21 j := hkbase.trans (Fin.ext rfl)
    change B.val.symm (p.val (B.val (golayBasePoints k))) = golayBasePoints k
    rw [hkbase', hx j]
    have hpj : ∀ i : Fin 3, p.val ((![16, 17, 19] : Fin 3 → Fin 24) i) =
        (![16, 17, 19] : Fin 3 → Fin 24) i := by
      intro i
      fin_cases i
      · exact hfix.1
      · exact hfix.2.1
      · exact hfix.2.2
    rw [hpj j, ← hx j, B.val.symm_apply_apply]
  rw [← leechRootedA2ThreePointSubgroup_eq] at hq
  have hpK := h hq
  change B * (B⁻¹ * p * B) * B⁻¹ ∈ K at hpK
  simpa only [mul_inv_cancel_left, mul_assoc, mul_inv_cancel, mul_one] using hpK

/-- The three actual transported generators and actual swap generate all flag permutations. -/
private theorem flag_mem (B s : golayAutomorphismSubgroup)
    (hb : B.val 0 = 16 ∧ B.val 1 = 17 ∧ B.val 2 = 19)
    (hspec : s.val 16 = 17 ∧ s.val 17 = 16 ∧ s.val 19 = 19)
    (K : Subgroup golayAutomorphismSubgroup)
    (hK : ∀ j, B * leechRootedA2ThreePointAutomorphism j * B⁻¹ ∈ K)
    (hs : s ∈ K)
    (p : golayAutomorphismSubgroup) (hp : p ∈ leechRootedA2SixthPermutationFlag) : p ∈ K := by
  rcases hp.1 with hfix | hswap
  · exact transported_mem B hb K hK p ((leechRootedA2SixthPermutationTriple_mem p).mpr
      ⟨hfix.1, hfix.2, hp.2⟩)
  · have hq : s⁻¹ * p ∈ leechRootedA2SixthPermutationTriple := by
      apply (leechRootedA2SixthPermutationTriple_mem _).mpr
      constructor
      · change s.val.symm (p.val 16) = 16
        rw [hswap.1, ← hspec.1, s.val.symm_apply_apply]
      constructor
      · change s.val.symm (p.val 17) = 17
        rw [hswap.2, ← hspec.2.1, s.val.symm_apply_apply]
      · change s.val.symm (p.val 19) = 19
        rw [hp.2]
        exact s.val.symm_apply_eq.mpr hspec.2.2.symm
    have h := K.mul_mem hs (transported_mem B hb K hK _ hq)
    simpa only [mul_inv_cancel_left] using h

/-- Three transported source permutations and the actual swap generate all flag permutations. -/
theorem leechRootedA2SixthPermutation_mem_of_generators (K : Subgroup golayAutomorphismSubgroup)
    (hK : ∀ j, leechRootedA2SixthPermutationGenerator j ∈ K)
    (hs : leechRootedA2SixthPermutationWordSwap ∈ K)
    (p : golayAutomorphismSubgroup) (hp : p ∈ leechRootedA2SixthPermutationFlag) : p ∈ K :=
  flag_mem leechRootedA2SixthPermutationTransport leechRootedA2SixthPermutationWordSwap
    leechRootedA2SixthPermutationTransport_spec leechRootedA2SixthPermutationWordSwap_spec
    K hK hs p hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
