/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightPreservation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortTransitivityCoordinates

/-! Short pair normalization inside the actual coordinate E8 section. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An injective tuple of fewer than eight section coordinates extends by one. -/
theorem generatedE8Short_extend_tuple {n : ℕ} (hn : n < 8) (a : Fin n → Fin 8)
    (ha : Function.Injective a) :
    ∃ b : Fin (n + 1) → Fin 8, Function.Injective b ∧ ∀ j, b j.castSucc = a j := by
  classical
  have hnonsurj : ¬ Function.Surjective a := by
    intro hs
    have hc := Fintype.card_le_of_surjective a hs
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨v, hv⟩ : ∃ v, v ∉ Set.range a := by
    simpa only [Function.Surjective, Set.mem_range, not_forall, not_exists] using hnonsurj
  exact ⟨Fin.snoc a v, Fin.snoc_injective_of_injective ha hv, fun j => by simp⟩

/-- Four selected coordinates can be normalized by actual section-preserving generators. -/
theorem generatedE8Short_monomial_four (u : leechIntegral) (f : Fin 4 → Fin 24)
    (hf : Function.Injective f) (hin : ∀ j, (f j).val < 8) (b : Fin 4 → ℤ)
    (habs : ∀ j, (u.val (f j)).natAbs = (b j).natAbs) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      generatedStandardOctadPreserves e ∧
      ∀ j : Fin 4, (leechIntegralAction e u).val (Fin.castAdd 20 j) = b j := by
  obtain ⟨p, hpres, hp⟩ := generatedStandardOctad_prepare_four f hf hin
  obtain ⟨d, hd⟩ := leechNormEight_four_signs (fun j => u.val (f j)) b habs
  refine ⟨golaySignIsometry d * golayPermutationIsometry p,
    leechConcreteGeneratorSubgroup.mul_mem (golaySignIsometry_mem_concrete d)
      (golayPermutationIsometry_mem_concrete p),
    generatedStandardOctadPreserves_mul _ _ (generatedStandardOctadPreserves_sign d)
      (generatedStandardOctadPreserves_permutation p hpres), ?_⟩
  intro j
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
    leechIntegralAction_golayPermutation]
  have hpj : p.val.symm (Fin.castAdd 20 j) = f j := by
    rw [← hp j, p.val.symm_apply_apply]
  simpa only [golayIntegerSign, golayIntegerPermute, hpj] using hd j

/-- A short pair in the section reaches the positive pair while preserving the section. -/
theorem generatedE8Short_pair_reduction (u : leechIntegral)
    (hs : leechSquareSum u.val = 32) (hu : generatedStandardOctadSupported u.val)
    (i j : Fin 24) (hij : i ≠ j) (hi : (u.val i).natAbs = 4)
    (hj : (u.val j).natAbs = 4) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      generatedStandardOctadPreserves e ∧
      (leechIntegralAction e u).val = leechShortPairTarget := by
  have hii : i.val < 8 := by
    by_contra h
    have hz := hu i (by omega)
    simp [hz] at hi
  have hji : j.val < 8 := by
    by_contra h
    have hz := hu j (by omega)
    simp [hz] at hj
  let a : Fin 2 → Fin 8 := ![⟨i.val, hii⟩, ⟨j.val, hji⟩]
  have ha : Function.Injective a := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [a, Fin.ext_iff]
  obtain ⟨b, hb, hba⟩ := generatedE8Short_extend_tuple (by decide : 2 < 8) a ha
  obtain ⟨f8, hf8, hfb⟩ := generatedE8Short_extend_tuple (by decide : 3 < 8) b hb
  let f : Fin 4 → Fin 24 := fun k => Fin.castAdd 16 (f8 k)
  have hf : Function.Injective f := by
    intro x y h
    exact hf8 (Fin.ext (congrArg (fun k : Fin 24 => k.val) h))
  have hfi : f 0 = i := by
    apply Fin.ext
    simpa [f, a] using congrArg (fun k : Fin 8 => k.val) ((hfb 0).trans (hba 0))
  have hfj : f 1 = j := by
    apply Fin.ext
    simpa [f, a] using congrArg (fun k : Fin 8 => k.val) ((hfb 1).trans (hba 1))
  obtain ⟨e, he, hpres, hrow⟩ := generatedE8Short_monomial_four u f hf
    (fun k => (f8 k).isLt) ![4, 4, u.val (f 2), u.val (f 3)] (by
      intro k
      fin_cases k <;> simp [hfi, hfj, hi, hj])
  exact ⟨e, he, hpres, leechShort_eq_pair_of_first _
    (by rw [leechIntegralAction_squareSum, hs]) (hrow 0) (hrow 1)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
