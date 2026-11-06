/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayDodecadOrbitData

/-! Binding the finite dodecad forest to actual Golay automorphisms fixing coordinate zero. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual original coefficient label at an orbit entry. -/
def golayDodecadOrbitCodeLabel (n : Fin 1288) : Fin 4096 :=
  ⟨golayDodecadOrbitLabel n.val, (golayDodecadOrbit_labels_certificate n).1⟩

/-- Every listed label belongs to the actual dodecads outside physical coordinate zero. -/
theorem golayDodecadOrbitCodeLabel_mem (n : Fin 1288) :
    golayDodecadOrbitCodeLabel n ∈ golayDodecadsOutside 0 := by
  simp only [golayDodecadsOutside, golayDodecads, Finset.mem_filter,
    Finset.mem_univ, true_and, golayDodecadOrbitCodeLabel]
  exact ⟨(golayDodecadOrbit_labels_certificate n).2.1, by
    simp [(golayDodecadOrbit_labels_certificate n).2.2.1]⟩

/-- The checked inverse lookup proves the 1288 actual labels are distinct. -/
theorem golayDodecadOrbitCodeLabel_injective :
    Function.Injective golayDodecadOrbitCodeLabel := by
  intro n m h
  have hv := congrArg (fun d : Fin 4096 => golayDodecadOrbitInverse d.val) h
  change golayDodecadOrbitInverse (golayDodecadOrbitLabel n.val) =
    golayDodecadOrbitInverse (golayDodecadOrbitLabel m.val) at hv
  rw [(golayDodecadOrbit_labels_certificate n).2.2.2,
    (golayDodecadOrbit_labels_certificate m).2.2.2] at hv
  exact Fin.ext hv

/-- The checked labels cover every actual dodecad outside coordinate zero. -/
theorem golayDodecadOrbitCodeLabel_surjective :
    Function.Surjective (fun n : Fin 1288 =>
      (⟨golayDodecadOrbitCodeLabel n, golayDodecadOrbitCodeLabel_mem n⟩ :
        golayDodecadsOutside 0)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨?_, by simp [golayDodecadsOutside_zero_card]⟩ |>.surjective
  intro n m h
  exact golayDodecadOrbitCodeLabel_injective (congrArg Subtype.val h)

/-- The actual incoming strong-generator automorphism. -/
def golayDodecadOrbitAutomorphism (n : Fin 1288) : golayAutomorphismSubgroup :=
  golayStrongAutomorphism
    ⟨golayDodecadOrbitGenerator n.val, golayDodecadOrbit_generator_bound n⟩

/-- Every actual incoming generator fixes the physical coordinate zero. -/
theorem golayDodecadOrbitAutomorphism_zero (n : Fin 1288) :
    (golayDodecadOrbitAutomorphism n).val 0 = 0 := by
  rw [golayDodecadOrbitAutomorphism, leechRootedA2StrongAutomorphism_apply]
  exact (golayDodecadOrbit_parents_certificate n).2.1

/-- Every noninitial forest edge is an actual coordinate-permutation transport of codewords. -/
theorem golayDodecadOrbitAutomorphism_edge (n m : Fin 1288) (hn : 0 < n.val)
    (hm : m.val = golayDodecadOrbitParent n.val) :
    golayPermute (golayDodecadOrbitAutomorphism n).val
      (golayCodeLabelEquiv (golayDodecadOrbitCodeLabel m)).val =
        (golayCodeLabelEquiv (golayDodecadOrbitCodeLabel n)).val := by
  funext i
  simp only [golayPermute, golayCodeLabelEquiv_val]
  apply ZMod.val_injective
  rw [golayLabelEncoder_match, golayLabelEncoder_match]
  change (if (golayEncodedMask (golayDodecadOrbitLabel m.val)).testBit
      ((golayDodecadOrbitAutomorphism n).val.symm i).val then 1 else 0) = _
  rw [golayDodecadOrbitAutomorphism, leechRootedA2StrongAutomorphism_inverse_apply, hm]
  rw [← golayDodecadOrbit_transition_certificate n hn i]
  rfl

/-- All 1288 listed genuine dodecads are actual images of the initial codeword. -/
theorem golayDodecadOrbitCodeLabel_reaches (n : Fin 1288) :
    ∃ p : golayAutomorphismSubgroup, p.val 0 = 0 ∧
      golayPermute p.val (golayCodeLabelEquiv (golayDodecadOrbitCodeLabel 0)).val =
        (golayCodeLabelEquiv (golayDodecadOrbitCodeLabel n)).val := by
  induction n using Fin.strong_induction_on with
  | h n ih =>
    by_cases hn : n.val = 0
    · have he : n = 0 := Fin.ext hn
      subst n
      exact ⟨1, rfl, rfl⟩
    · have hnpos : 0 < n.val := Nat.pos_of_ne_zero hn
      have hparent := (golayDodecadOrbit_parents_certificate n).2.2 hnpos
      let m : Fin 1288 := ⟨golayDodecadOrbitParent n.val, hparent.trans n.isLt⟩
      obtain ⟨p, hp0, hp⟩ := ih m hparent
      refine ⟨golayDodecadOrbitAutomorphism n * p, ?_, ?_⟩
      · change (golayDodecadOrbitAutomorphism n).val (p.val 0) = 0
        rw [hp0, golayDodecadOrbitAutomorphism_zero]
      · change golayPermute ((golayDodecadOrbitAutomorphism n).val * p.val)
          (golayCodeLabelEquiv (golayDodecadOrbitCodeLabel 0)).val = _
        rw [golayPermute_mul, hp]
        exact golayDodecadOrbitAutomorphism_edge n m hnpos rfl

/-- Every actual dodecad outside coordinate zero lies in one genuine point-stabilizer orbit. -/
theorem golayDodecadsOutside_zero_reaches (d : Fin 4096)
    (hd : d ∈ golayDodecadsOutside 0) :
    ∃ p : golayAutomorphismSubgroup, p.val 0 = 0 ∧
      golayPermute p.val (golayCodeLabelEquiv (golayDodecadOrbitCodeLabel 0)).val =
        (golayCodeLabelEquiv d).val := by
  obtain ⟨n, hn⟩ := golayDodecadOrbitCodeLabel_surjective ⟨d, hd⟩
  have he : golayDodecadOrbitCodeLabel n = d := congrArg Subtype.val hn
  obtain ⟨p, hp0, hp⟩ := golayDodecadOrbitCodeLabel_reaches n
  exact ⟨p, hp0, by rwa [he] at hp⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
