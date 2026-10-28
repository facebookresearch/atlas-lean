/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortTransitivity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionCo1FrameOrbit

/-! Actual monomial transitivity on the pair-short dictionary labels. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem monomial_four (u : leechIntegral) (f : Fin 4 → Fin 24)
    (hf : Function.Injective f) (b : Fin 4 → ℤ)
    (habs : ∀ j, (u.val (f j)).natAbs = (b j).natAbs) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      ∀ j : Fin 4, (leechIntegralAction e u).val (Fin.castAdd 20 j) = b j := by
  obtain ⟨p, hp⟩ := golayAutomorphism_four_transitive f
    (fun j : Fin 4 => Fin.castAdd 20 j) hf (by
      intro i j h
      exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h))
  obtain ⟨d, hd⟩ := leechNormEight_four_signs (fun j => u.val (f j)) b habs
  refine ⟨golaySignIsometry d * golayPermutationIsometry p, ⟨d, p, rfl⟩, ?_⟩
  intro j
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
    leechIntegralAction_golayPermutation]
  have hpj : p.val.symm (Fin.castAdd 20 j) = f j := by
    rw [← hp j, p.val.symm_apply_apply]
  simpa only [golayIntegerSign, golayIntegerPermute, hpj] using hd j

/-- Every actual pair-short vector is reduced by a genuine monomial lattice isometry. -/
theorem generatedAxis_pair_monomial_reduction (s : Fin 2) (p : Fin 276) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      (leechIntegralAction e (griessShortLatticeVector (Sum.inl (s, p)))).val =
        leechShortPairTarget := by
  let i := (griessCoordinatePair p).1
  let j := (griessCoordinatePair p).2
  have hij : i ≠ j := griessCoordinatePair_ne p
  let a : Fin 2 → Fin 24 := ![i, j]
  have ha : Function.Injective a := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [a]
  obtain ⟨b, hb, hba⟩ := leechShort_extend_tuple (by decide : 2 < 24) a ha
  obtain ⟨f, hf, hfb⟩ := leechShort_extend_tuple (by decide : 3 < 24) b hb
  have hfi : f 0 = i := (hfb 0).trans (hba 0)
  have hfj : f 1 = j := (hfb 1).trans (hba 1)
  let u := griessShortLatticeVector (Sum.inl (s, p))
  obtain ⟨e, he, hrow⟩ := monomial_four u f hf
    ![4, 4, u.val (f 2), u.val (f 3)] (by
      intro k
      fin_cases k
      · change (u.val (f 0)).natAbs = 4
        rw [hfi]
        simp [u, griessShortLatticeVector, i, griessPair_first]
      · change (u.val (f 1)).natAbs = 4
        rw [hfj]
        dsimp only [u, griessShortLatticeVector]
        rw [griessPair_second]
        split_ifs <;> norm_num
      · rfl
      · rfl)
  exact ⟨e, he, leechShort_eq_pair_of_first _
    (by
      rw [leechIntegralAction_squareSum]
      simpa only [griessShortLatticeVector] using griessShortIntegral_squareSum (Sum.inl (s, p)))
    (hrow 0) (hrow 1)⟩

/-- Actual monomial isometries are transitive on all 552 pair-short labels. -/
theorem generatedAxis_pair_monomial_transitive (s t : Fin 2) (p q : Fin 276) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      griessShortPermutation e (Sum.inl (s, p)) = Sum.inl (t, q) := by
  obtain ⟨a, ha, har⟩ := generatedAxis_pair_monomial_reduction s p
  obtain ⟨b, hb, hbs⟩ := generatedAxis_pair_monomial_reduction t q
  have hv : leechIntegralAction a (griessShortLatticeVector (Sum.inl (s, p))) =
      leechIntegralAction b (griessShortLatticeVector (Sum.inl (t, q))) :=
    Subtype.ext (har.trans hbs.symm)
  have hvec : a.val (griessShortVector (Sum.inl (s, p))) =
      b.val (griessShortVector (Sum.inl (t, q))) := by
    have h := congrArg (fun u : leechIntegral => leechCoordinateEmbedding u.val) hv
    rw [leechIntegralAction_embedding, leechIntegralAction_embedding] at h
    exact h
  let e := b⁻¹ * a
  have he : e.val (griessShortVector (Sum.inl (s, p))) =
      griessShortVector (Sum.inl (t, q)) := by
    change b.val.symm (a.val (griessShortVector (Sum.inl (s, p)))) = _
    rw [hvec, b.val.symm_apply_apply]
  refine ⟨e, golayMonomialSubgroup.mul_mem (golayMonomialSubgroup.inv_mem hb) ha, ?_⟩
  apply centralizer_shortVector_sign_unique
  rcases griessShortPermutation_vector e (Sum.inl (s, p)) with h | h
  · exact Or.inl (h.symm.trans he)
  · exact Or.inr (by
      rw [he] at h
      have hn := congrArg Neg.neg h
      simpa only [neg_neg] using hn.symm)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
