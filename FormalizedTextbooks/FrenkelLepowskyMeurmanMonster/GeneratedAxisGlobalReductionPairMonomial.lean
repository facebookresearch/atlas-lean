/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortTransitivityCoordinates

/-! Actual monomial transports on the signed pair family, retaining membership
in the Ω-normalizing monomial subgroup rather than only the full Conway group. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Four signed coordinates can be normalized by actual Golay monomial isometries. -/
theorem generatedAxisGlobal_pair_monomial_four (u : leechIntegral) (f : Fin 4 → Fin 24)
    (hf : Function.Injective f) (b : Fin 4 → ℤ)
    (habs : ∀ j, (u.val (f j)).natAbs = (b j).natAbs) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      ∀ j : Fin 4, (leechIntegralAction e u).val (Fin.castAdd 20 j) = b j := by
  obtain ⟨p, hp⟩ := golayAutomorphism_four_transitive f
    (fun j : Fin 4 => Fin.castAdd 20 j) hf (by
      intro i j h
      exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h))
  obtain ⟨d, hd⟩ := leechNormEight_four_signs (fun j => u.val (f j)) b habs
  refine ⟨golaySignIsometry d * golayPermutationIsometry p,
    ⟨d, p, rfl⟩, ?_⟩
  intro j
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
    leechIntegralAction_golayPermutation]
  have hpj : p.val.symm (Fin.castAdd 20 j) = f j := by
    rw [← hp j, p.val.symm_apply_apply]
  simpa only [golayIntegerSign, golayIntegerPermute, hpj] using hd j

/-- A physical short pair reduces to the positive pair
by a genuine monomial isometry. -/
theorem generatedAxisGlobal_pair_monomial_reduction (u : leechIntegral)
    (hs : leechSquareSum u.val = 32)
    (i j : Fin 24) (hij : i ≠ j) (hi : (u.val i).natAbs = 4)
    (hj : (u.val j).natAbs = 4) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      (leechIntegralAction e u).val = leechShortPairTarget := by
  let a : Fin 2 → Fin 24 := ![i, j]
  have ha : Function.Injective a := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [a]
  obtain ⟨b, hb, hba⟩ := leechShort_extend_tuple (by decide : 2 < 24) a ha
  obtain ⟨f, hf, hfb⟩ := leechShort_extend_tuple (by decide : 3 < 24) b hb
  have hfi : f 0 = i := (hfb 0).trans (hba 0)
  have hfj : f 1 = j := (hfb 1).trans (hba 1)
  obtain ⟨e, he, hrow⟩ := generatedAxisGlobal_pair_monomial_four u f hf
    ![4, 4, u.val (f 2), u.val (f 3)] (by
      intro k
      fin_cases k <;> simp [hfi, hfj, hi, hj])
  exact ⟨e, he, leechShort_eq_pair_of_first _
    (by rw [leechIntegralAction_squareSum, hs]) (hrow 0) (hrow 1)⟩

/-- Every pair-family short vector reaches the same target
by actual monomial isometries. -/
theorem generatedAxisGlobal_pair_monomial_target (s : Fin 2) (p : Fin 276) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      (leechIntegralAction e (griessShortLatticeVector (Sum.inl (s, p)))).val =
        leechShortPairTarget := by
  apply generatedAxisGlobal_pair_monomial_reduction _ (griessPair_squareSum s p)
    (griessCoordinatePair p).1 (griessCoordinatePair p).2 (griessCoordinatePair_ne p)
  · change (griessShortIntegral (Sum.inl (s, p)) (griessCoordinatePair p).1).natAbs = 4
    simp [griessShortIntegral, griessCoordinatePair_ne p]
  · change (griessShortIntegral (Sum.inl (s, p)) (griessCoordinatePair p).2).natAbs = 4
    fin_cases s <;> simp [griessShortIntegral, (griessCoordinatePair_ne p).symm]

/-- Genuine monomial isometries are transitive on every pair short label. -/
theorem generatedAxisGlobal_pair_monomial_transitive (s t : Fin 2) (p q : Fin 276) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      griessShortPermutation e (Sum.inl (s, p)) = Sum.inl (t, q) := by
  obtain ⟨a, ha, har⟩ := generatedAxisGlobal_pair_monomial_target s p
  obtain ⟨b, hb, hbr⟩ := generatedAxisGlobal_pair_monomial_target t q
  exact generatedAxis_monomial_common_target _ _ a b ha hb
    (Subtype.ext (har.trans hbr.symm))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
