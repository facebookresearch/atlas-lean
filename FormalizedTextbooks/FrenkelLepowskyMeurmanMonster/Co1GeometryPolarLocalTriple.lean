/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryPolarLocalNormalization

/-! Actual monomial normalization of the second odd norm-eight shape. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem polarLocal_extend_tuple {n : ℕ} (hn : n < 24)
    (a : Fin n → Fin 24) (ha : Function.Injective a) :
    ∃ b : Fin (n + 1) → Fin 24, Function.Injective b ∧ ∀ j, b j.castSucc = a j := by
  classical
  have hnons : ¬ Function.Surjective a := by
    intro hs
    have hc := Fintype.card_le_of_surjective a hs
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨v, hv⟩ : ∃ v : Fin 24, v ∉ Set.range a := by
    simpa only [Function.Surjective, Set.mem_range, not_forall, not_exists] using hnons
  exact ⟨Fin.snoc a v, Fin.snoc_injective_of_injective ha hv, fun j => by simp⟩

/-- The residue-one triple shape normalized at coordinates zero, one and two. -/
def monsterCo1PolarTripleVector : Fin 24 → ℤ :=
  fun i => if i = 0 then 5 else if i = 1 ∨ i = 2 then -3 else 1

/-- A genuine code permutation takes every normalized second odd shape to its literal triple. -/
theorem monsterCo1PolarLocal_triple_to_standard (u : leechIntegral)
    (hn : leechSquareSum u.val = 64) (hr : ∀ i, (u.val i : ZMod 4) = 1)
    (hs : leechNormEightMultiplicity u.val = leechNormEightShapeCounts 6) :
    ∃ p : golayAutomorphismSubgroup,
      golayIntegerPermute p.val u.val = monsterCo1PolarTripleVector := by
  classical
  have hval := monsterCo1PolarLocal_normalized_values u hn hr
  have h3 (i : Fin 24) : (u.val i).natAbs = 3 ↔ u.val i = -3 := by
    rcases hval i with h | h | h <;> simp [h]
  have h5 (i : Fin 24) : (u.val i).natAbs = 5 ↔ u.val i = 5 := by
    rcases hval i with h | h | h <;> simp [h]
  have hc5 := congrFun hs 5
  change (Finset.univ.filter fun i => (u.val i).natAbs = 5).card = 1 at hc5
  simp only [h5] at hc5
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc5
  have hua : u.val a = 5 := by
    have : a ∈ Finset.univ.filter fun i => u.val i = 5 := by rw [ha]; simp
    exact (Finset.mem_filter.mp this).2
  have hu5 (i : Fin 24) : u.val i = 5 ↔ i = a := by
    have he : i ∈ (Finset.univ.filter fun j => u.val j = 5) ↔
        i ∈ ({a} : Finset (Fin 24)) :=
      by rw [ha]
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] using he
  have hc3 := congrFun hs 3
  change (Finset.univ.filter fun i => (u.val i).natAbs = 3).card = 2 at hc3
  simp only [h3] at hc3
  have hcard : Fintype.card {i : Fin 24 // u.val i = -3} = 2 := by
    simpa only [Fintype.card_subtype] using hc3
  let e : Fin 2 ≃ {i : Fin 24 // u.val i = -3} := (Fintype.equivFinOfCardEq hcard).symm
  let f : Fin 3 → Fin 24 := Fin.cons a (fun j => (e j).val)
  have hf : Function.Injective f := Fin.cons_injective_of_injective (by
    rintro ⟨j, hj⟩
    have he := (e j).property
    change (e j).val = a at hj
    rw [hj, hua] at he
    norm_num at he) (Subtype.val_injective.comp e.injective)
  obtain ⟨f4, hf4, he4⟩ := polarLocal_extend_tuple (by omega : 3 < 24) f hf
  obtain ⟨f5, hf5, he5⟩ := polarLocal_extend_tuple (by omega : 4 < 24) f4 hf4
  obtain ⟨q, hq⟩ := golayAutomorphism_maps_firstFive f5 hf5
  have hq3 (j : Fin 3) : q.val (Fin.castAdd 21 j) = f j := by
    have h := hq j.castSucc.castSucc
    change q.val (Fin.castAdd 21 j) = f5 j.castSucc.castSucc at h
    rw [he5, he4] at h
    exact h
  have hq0 : q.val 0 = a := by
    have h := hq3 0
    change q.val 0 = a at h
    exact h
  have hq1 : q.val 1 = (e 0).val := by
    have h := hq3 1
    change q.val 1 = (e 0).val at h
    exact h
  have hq2 : q.val 2 = (e 1).val := by
    have h := hq3 2
    change q.val 2 = (e 1).val at h
    exact h
  have hq5 (i : Fin 24) : u.val (q.val i) = 5 ↔ i = 0 := by
    rw [hu5, ← hq0]
    exact q.val.injective.eq_iff
  have hqneg (i : Fin 24) : u.val (q.val i) = -3 ↔ i = 1 ∨ i = 2 := by
    constructor
    · intro hi
      obtain ⟨j, hj⟩ := e.surjective ⟨q.val i, hi⟩
      have hjv := congrArg Subtype.val hj
      fin_cases j
      · exact Or.inl (q.val.injective (hjv.symm.trans hq1.symm))
      · exact Or.inr (q.val.injective (hjv.symm.trans hq2.symm))
    · rintro (rfl | rfl)
      · rw [hq1]; exact (e 0).property
      · rw [hq2]; exact (e 1).property
  refine ⟨q⁻¹, ?_⟩
  funext i
  change u.val (q.val i) = monsterCo1PolarTripleVector i
  by_cases hi0 : i = 0
  · simp only [monsterCo1PolarTripleVector, hi0, ite_true]
    exact (hq5 0).mpr rfl
  · by_cases hi12 : i = 1 ∨ i = 2
    · simp only [monsterCo1PolarTripleVector, hi0, hi12, ite_false, ite_true]
      exact (hqneg i).mpr hi12
    · simp only [monsterCo1PolarTripleVector, hi0, hi12, ite_false]
      rcases hval (q.val i) with h | h | h
      · exact h
      · exact False.elim (hi12 ((hqneg i).mp h))
      · exact False.elim (hi0 ((hq5 i).mp h))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
