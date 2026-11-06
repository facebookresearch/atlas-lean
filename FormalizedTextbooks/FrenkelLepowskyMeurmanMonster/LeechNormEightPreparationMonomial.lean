/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual Golay permutations and codeword signs normalize four norm-eight coordinates. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechConcreteGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismPermutations

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An injective four-tuple extends by one unused coordinate. -/
theorem leechNormEight_extend_four_tuple (a : Fin 4 → Fin 24)
    (ha : Function.Injective a) :
    ∃ b : Fin 5 → Fin 24, Function.Injective b ∧ ∀ j, b j.castSucc = a j := by
  classical
  have hn : ¬ Function.Surjective a := by
    intro hs
    have hc := Fintype.card_le_of_surjective a hs
    norm_num at hc
  have hv : ∃ v : Fin 24, v ∉ Set.range a := by
    simpa only [Function.Surjective, Set.mem_range, not_forall, not_exists] using hn
  obtain ⟨v, hv⟩ := hv
  exact ⟨Fin.snoc a v, Fin.snoc_injective_of_injective ha hv,
    fun j => by simp⟩

/-- Four-transitivity is a consequence of the proved five-transitivity of the actual code group. -/
theorem golayAutomorphism_four_transitive (a b : Fin 4 → Fin 24)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    ∃ p : golayAutomorphismSubgroup, ∀ j, p.val (a j) = b j := by
  obtain ⟨a', ha', hea⟩ := leechNormEight_extend_four_tuple a ha
  obtain ⟨b', hb', heb⟩ := leechNormEight_extend_four_tuple b hb
  obtain ⟨p, hp⟩ := golayAutomorphism_five_transitive a' b' ha' hb'
  exact ⟨p, fun j => by simpa only [hea, heb] using hp j.castSucc⟩

theorem leechIntegralAction_golayPermutation (p : golayAutomorphismSubgroup)
    (u : leechIntegral) :
    (leechIntegralAction (golayPermutationIsometry p) u).val =
      golayIntegerPermute p.val u.val := by
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding]
  exact golayRealPermute_embedding p.val u.val

theorem leechIntegralAction_golaySign (d : golayCode) (u : leechIntegral) :
    (leechIntegralAction (golaySignIsometry d) u).val = golayIntegerSign d.val u.val := by
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding]
  exact golayRealSign_embedding d.val u.val

/-- Independently prescribed signs at four distinct positions extend to an actual Golay sign. -/
theorem leechNormEight_four_signs (a b : Fin 4 → ℤ)
    (habs : ∀ j, (a j).natAbs = (b j).natAbs) :
    ∃ d : golayCode, ∀ j : Fin 4,
      (if d.val (Fin.castAdd 20 j) = 0 then a j else -a j) = b j := by
  classical
  let bits : Fin 4 → ZMod 2 := fun j => if a j = b j then 0 else 1
  obtain ⟨d, hd⟩ := golayCode_four_coordinate_surjective
    (fun j : Fin 4 => Fin.castAdd 20 j) (by
      intro i j h
      exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h)) bits
  refine ⟨d, ?_⟩
  intro j
  have hj := congrFun hd j
  change d.val (Fin.castAdd 20 j) = bits j at hj
  rw [hj]
  by_cases he : a j = b j
  · simp [bits, he]
  · have hn : a j = -b j := (Int.natAbs_eq_natAbs_iff.mp (habs j)).resolve_left he
    simp [bits, hn]

/-- Any actual vector with the specified multiplicities has the prescribed signed first row
after an element of the concrete monomial generator subgroup. -/
theorem leechNormEight_monomial_preparation (u : leechIntegral) (s : Fin 8)
    (hshape : leechNormEightMultiplicity u.val = leechNormEightShapeCounts s) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      ∀ j : Fin 4, (leechIntegralAction e u).val (Fin.castAdd 20 j) =
        leechNormEightTargetRows s j := by
  obtain ⟨f, hf, habs⟩ := leechNormEight_select_target_coordinates u.val s hshape
  obtain ⟨p, hp⟩ := golayAutomorphism_four_transitive f
    (fun j : Fin 4 => Fin.castAdd 20 j) hf (by
      intro i j h
      exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h))
  obtain ⟨d, hd⟩ := leechNormEight_four_signs (fun j => u.val (f j))
    (leechNormEightTargetRows s) habs
  refine ⟨golaySignIsometry d * golayPermutationIsometry p,
    leechConcreteGeneratorSubgroup.mul_mem (golaySignIsometry_mem_concrete d)
      (golayPermutationIsometry_mem_concrete p), ?_⟩
  intro j
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
    leechIntegralAction_golayPermutation]
  have hpj : p.val.symm (Fin.castAdd 20 j) = f j := by
    rw [← hp j, p.val.symm_apply_apply]
  simpa only [golayIntegerSign, golayIntegerPermute, hpj] using hd j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
